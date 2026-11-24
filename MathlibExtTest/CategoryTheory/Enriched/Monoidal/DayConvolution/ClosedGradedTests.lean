/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedGraded

/-!
# Whole-coefficient clients of the genuine Day closed correspondence

The full coefficient, both inverse maps and original coefficient arrows are
retained. No tensor-unit separator, parameter points or index symmetry is
assumed. The unit coefficient agrees with the original ordinary transpose.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ClosedGradedTests

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)

/-- Every whole coefficient transposes a complete genuine transformation. -/
def coefficientTranspose (P : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    GradedNatTrans ((Center.ofBraided V).obj P) G.toEnrichedFunctor
      (Closed.rightObject d F Y).toEnrichedFunctor :=
  Closed.gradedHomEquiv d P F G Y t

/-- Every whole coefficient retains the genuine inverse transformation. -/
def coefficientUntranspose (P : V) (F G Y : EnrichedFunctorCat V I)
    (h : GradedNatTrans ((Center.ofBraided V).obj P) G.toEnrichedFunctor
      (Closed.rightObject d F Y).toEnrichedFunctor) :
    GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor :=
  (Closed.gradedHomEquiv d P F G Y).symm h

/-- Both original coefficient maps recover every complete tensor transformation. -/
theorem coefficient_left_inverse (P : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    coefficientUntranspose d P F G Y (coefficientTranspose d P F G Y t) = t :=
  (Closed.gradedHomEquiv d P F G Y).left_inv t

/-- Both original coefficient maps recover every complete transformation into the end. -/
theorem coefficient_right_inverse (P : V) (F G Y : EnrichedFunctorCat V I)
    (h : GradedNatTrans ((Center.ofBraided V).obj P) G.toEnrichedFunctor
      (Closed.rightObject d F Y).toEnrichedFunctor) :
    coefficientTranspose d P F G Y (coefficientUntranspose d P F G Y h) = h :=
  (Closed.gradedHomEquiv d P F G Y).right_inv h

/-- Every original coefficient projection retains the actual scalar crossing and Day point. -/
theorem coefficient_projection (P : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) (c j : I) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P)
        (coefficientTranspose d P F G Y t) c ≫ Closed.π d F Y c j =
      MonoidalClosed.curry
        ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso P
          (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
          (P ◁ Generators.point d.tensorEnrichedFunctor
            F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) t (j ⊗ c)) :=
  Closed.gradedHomEquiv_apply_π d P F G Y t c j

/-- The whole inverse retains its complete Hom weight and both actual coefficient crossings. -/
theorem coefficient_inverse_generator (P : V) (F G Y : EnrichedFunctorCat V I)
    (h : GradedNatTrans ((Center.ofBraided V).obj P) G.toEnrichedFunctor
      (Closed.rightObject d F Y).toEnrichedFunctor) (k : I) (p : I × I) :
    (P ◁ EnrichedDayKernel.gen d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor k p) ≫
        GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P)
          (coefficientUntranspose d P F G Y h) k =
      (α_ P ((p.1 ⊗ p.2) ⟶[V] k)
        (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).inv ≫
        ((β_ ((p.1 ⊗ p.2) ⟶[V] k) P).inv ▷
          (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)) ≫
        (α_ ((p.1 ⊗ p.2) ⟶[V] k) P
          (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).hom ≫
        (((p.1 ⊗ p.2) ⟶[V] k) ◁
          ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso P
            (F.toEnrichedFunctor.obj p.1) (G.toEnrichedFunctor.obj p.2)).inv ≫
            MonoidalClosed.uncurry
              (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) h p.2 ≫
                Closed.π d F Y p.2 p.1))) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) :=
  Closed.gradedHomEquiv_symm_gen d P F G Y h k p

/-- Every original coefficient arrow is retained by the whole transpose. -/
theorem coefficient_arrow {P P' : V} (r : P' ⟶ P) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    coefficientTranspose d P' F G Y (GradedNatTrans.regrade ((Center.ofBraided V).map r) t) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r)
        (coefficientTranspose d P F G Y t) :=
  Closed.gradedHomEquiv_regrade d r F G Y t

/-- Every whole variable-input arrow is retained in each original coefficient. -/
theorem variable_input_arrow (P : V) (F : EnrichedFunctorCat V I)
    {G G' : EnrichedFunctorCat V I} (f : G' ⟶ G) (Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    coefficientTranspose d P F G' Y
        (gradedPrecomp ((Center.ofBraided V).obj P) ((Closed.leftFunctor d F).map f) t) =
      gradedPrecomp ((Center.ofBraided V).obj P) f (coefficientTranspose d P F G Y t) :=
  Closed.gradedHomEquiv_naturality_left d P F f Y t

/-- Every full target arrow is retained in each original coefficient. -/
theorem target_arrow (P : V) (F G : EnrichedFunctorCat V I)
    {Y Y' : EnrichedFunctorCat V I} (q : Y ⟶ Y')
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    coefficientTranspose d P F G Y' (gradedPostcomp ((Center.ofBraided V).obj P) t q) =
      gradedPostcomp ((Center.ofBraided V).obj P) (coefficientTranspose d P F G Y t)
        ((Closed.rightFunctor d F).map q) :=
  Closed.gradedHomEquiv_naturality_right d P F G q t

/-- Every full original source weight arrow is retained in each coefficient. -/
theorem weight_arrow (P : V) {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    coefficientTranspose d P F' G Y
        (gradedPrecomp ((Center.ofBraided V).obj P) (Closed.weightMap d f G) t) =
      gradedPostcomp ((Center.ofBraided V).obj P) (coefficientTranspose d P F G Y t)
        (Closed.pre d f Y) :=
  Closed.gradedHomEquiv_naturality_source d P f G Y t

/-- The actual ambient-presheaf isomorphism retains the whole original transpose function. -/
theorem coefficient_presheaf_function (P : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (Closed.tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    (Closed.gradedPresheafIso d F G Y).hom.app (Opposite.op P) t =
      coefficientTranspose d P F G Y t :=
  Closed.gradedPresheafIso_hom_app d P F G Y t

/-- The whole unit-coefficient map is the original ordinary Day transpose. -/
theorem coefficient_unit (F G Y : EnrichedFunctorCat V I)
    (f : Closed.tensorObject d F G ⟶ Y) :
    coefficientTranspose d (𝟙_ V) F G Y f = Closed.transpose d F G Y f :=
  Closed.gradedHomEquiv_unit d F G Y f

end CategoryTheory.EnrichedDayKernel.ClosedGradedTests
