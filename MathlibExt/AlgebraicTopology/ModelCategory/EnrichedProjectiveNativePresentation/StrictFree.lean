/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.StrictSource
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Generators

/-!
# Original source free adjunctions in the actual strict presentation

Compose the actual original source adjunction with the full strict source
equivalence. Its whole evaluation comparison retains the original inverse
and actual carrier counit. Both Hom directions and the full chosen units
and counits compare to the actual strict native free adjunction.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The complete original inverse evaluation comparison uses the actual source counit. -/
def strictSourceInverseEvaluationIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (R : C ⥤ PointedCGWH.{u, v}) (hR : transportedEvaluation e a ≅ R) :
    (strictSourceEquivalence e).inverse ⋙ R ≅
      BasedNativePresentation.strictEvaluation (A := A) a :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EnrichedZeroCompletion.strictRestriction
      (Functor.isoWhiskerLeft e.inverse hR.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight e.counitIso (EnrichedFunctorCat.evaluation a) ≪≫
            Functor.leftUnitor _)

/-- The actual original source adjunction, full source equivalence and exact evaluation. -/
def strictSourceOriginalAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    L ⋙ (strictSourceEquivalence e).functor ⊣ BasedNativePresentation.strictEvaluation a :=
  (adj.comp (strictSourceEquivalence e).toAdjunction).ofNatIsoRight
    (strictSourceInverseEvaluationIso e a R hR)

/-- The full original forward Hom map and actual source equivalence Hom map are retained. -/
theorem strictSourceOriginalAdjunction_homEquiv
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : BasedNativePresentation.StrictCarrier (A := A)}
    (f : (L ⋙ (strictSourceEquivalence e).functor).obj X ⟶ Y) :
    (strictSourceOriginalAdjunction e a L R adj hR).homEquiv X Y f =
      adj.homEquiv X ((strictSourceEquivalence e).inverse.obj Y)
        ((strictSourceEquivalence e).toAdjunction.homEquiv (L.obj X) Y f) ≫
          (strictSourceInverseEvaluationIso e a R hR).hom.app Y := by
  unfold strictSourceOriginalAdjunction
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Both whole original inverse Hom maps and the inverse evaluation comparison are retained. -/
theorem strictSourceOriginalAdjunction_homEquiv_symm
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : BasedNativePresentation.StrictCarrier (A := A)}
    (f : X ⟶ (BasedNativePresentation.strictEvaluation a).obj Y) :
    ((strictSourceOriginalAdjunction e a L R adj hR).homEquiv X Y).symm f =
      ((strictSourceEquivalence e).toAdjunction.homEquiv (L.obj X) Y).symm
        ((adj.homEquiv X ((strictSourceEquivalence e).inverse.obj Y)).symm
          (f ≫ (strictSourceInverseEvaluationIso e a R hR).inv.app Y)) := by
  unfold strictSourceOriginalAdjunction
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  rw [Adjunction.comp_homEquiv]
  rfl

/-- Compare actual selected adjunctions with their identical entire strict evaluation. -/
def strictSourceFreeIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    L ⋙ (strictSourceEquivalence e).functor ≅ BasedNativePresentation.strictFreeAt a :=
  Adjunction.leftAdjointUniq (strictSourceOriginalAdjunction e a L R adj hR)
    (BasedNativePresentation.strictFreeAdjunction a)

/-- The complete original-to-strict adjunct compares to the same actual native strict adjunct. -/
theorem strictSourceFreeIso_homEquiv
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : BasedNativePresentation.StrictCarrier (A := A)}
    (f : (BasedNativePresentation.strictFreeAt a).obj X ⟶ Y) :
    (strictSourceOriginalAdjunction e a L R adj hR).homEquiv X Y
      ((strictSourceFreeIso e a L R adj hR).hom.app X ≫ f) =
        (BasedNativePresentation.strictFreeAdjunction a).homEquiv X Y f := by
  let oldAdj := strictSourceOriginalAdjunction e a L R adj hR
  let newAdj := BasedNativePresentation.strictFreeAdjunction a
  let q := strictSourceFreeIso e a L R adj hR
  have hStart := oldAdj.homEquiv_naturality_right (q.hom.app X) f
  have hUnit : oldAdj.homEquiv X ((BasedNativePresentation.strictFreeAt a).obj X)
      (q.hom.app X) = newAdj.unit.app X :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact hStart.trans
    ((congrArg (fun z => z ≫ (BasedNativePresentation.strictEvaluation a).map f) hUnit).trans
      (newAdj.homEquiv_unit X Y f).symm)

/-- The whole original-to-strict inverse adjunct retains the same complete original map. -/
theorem strictSourceFreeIso_homEquiv_symm
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : BasedNativePresentation.StrictCarrier (A := A)}
    (f : X ⟶ (BasedNativePresentation.strictEvaluation a).obj Y) :
    (strictSourceFreeIso e a L R adj hR).hom.app X ≫
      ((BasedNativePresentation.strictFreeAdjunction a).homEquiv X Y).symm f =
        ((strictSourceOriginalAdjunction e a L R adj hR).homEquiv X Y).symm f := by
  apply ((strictSourceOriginalAdjunction e a L R adj hR).homEquiv X Y).injective
  exact (strictSourceFreeIso_homEquiv e a L R adj hR _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- The whole actual composed original-source unit is preserved. -/
theorem strictSourceFreeIso_unit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) (X : PointedCGWH.{u, v}) :
    (strictSourceOriginalAdjunction e a L R adj hR).unit.app X ≫
      (BasedNativePresentation.strictEvaluation a).map
        ((strictSourceFreeIso e a L R adj hR).hom.app X) =
          (BasedNativePresentation.strictFreeAdjunction a).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The whole actual composed original-source counit is preserved. -/
theorem strictSourceFreeIso_counit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    (Y : BasedNativePresentation.StrictCarrier (A := A)) :
    (strictSourceFreeIso e a L R adj hR).hom.app
        ((BasedNativePresentation.strictEvaluation a).obj Y) ≫
      (BasedNativePresentation.strictFreeAdjunction a).counit.app Y =
        (strictSourceOriginalAdjunction e a L R adj hR).counit.app Y :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ Y

/-- Every original whole free arrow maps to the whole actual strict native free arrow. -/
def strictSourceFreeArrowIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk ((strictSourceEquivalence e).functor.map (L.map f)) ≅
      CategoryTheory.Arrow.mk ((BasedNativePresentation.strictFreeAt a).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (strictSourceFreeIso e a L R adj hR) (CategoryTheory.Arrow.mk f)

/-- Every actual iso-invariant strict class preserves the same original free arrow. -/
theorem strictSourceFreeArrowClass_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    (P : MorphismProperty (BasedNativePresentation.StrictCarrier (A := A))) [P.RespectsIso]
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    P ((strictSourceEquivalence e).functor.map (L.map f)) ↔
      P ((BasedNativePresentation.strictFreeAt a).map f) :=
  P.arrow_mk_iso_iff (strictSourceFreeArrowIso e a L R adj hR f)

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual composed original free/evaluation adjunction is Quillen for the derived model. -/
theorem strictSourceOriginalAdjunction_isQuillen
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
      BasedNativePresentation.strictModelCategory
    (strictSourceOriginalAdjunction e a L R adj hR).IsQuillenAdjunction := by
  let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
    BasedNativePresentation.strictModelCategory
  have hNative := BasedNativePresentation.strict_freeAdjunction_isQuillen (A := A) a
  exact { preservesCofibrations := fun X Y f h =>
            (strictSourceFreeArrowClass_iff e a L R adj hR (cofibrations _) f).mpr
              (hNative.preservesCofibrations f h)
          preservesTrivialCofibrations := fun X Y f h =>
            (strictSourceFreeArrowClass_iff e a L R adj hR (trivialCofibrations _) f).mpr
              (hNative.preservesTrivialCofibrations f h) }

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
