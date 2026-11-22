/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.SymmetricAlgebra

/-!
# The complete original tensor and commutative algebra coherence

Both original inverse Hom functions retain every coefficient map. The
actual units, counits and both triangles use the same full free algebras
and the original Kan degree-one generators.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe uA vA uB vB uC vC
variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}

/-- Both entire inverse Hom functions occur in the actual composite adjunction. -/
private theorem compositeAdjunction_inverse (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (X : A) (Y : C) (g : X ⟶ (R₂ ⋙ R₁).obj Y) :
    ((a₁.comp a₂).homEquiv X Y).symm g =
      (a₂.homEquiv (L₁.obj X) Y).symm ((a₁.homEquiv X (R₂.obj Y)).symm g) := by
  have h := Adjunction.comp_homEquiv a₁ a₂
  exact congrArg (fun e => e.symm g) (congrFun (congrFun h X) Y)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison

open CategoryTheory.Sequence CategoryTheory.Operad.SmallFinBijGroupoid

universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj

/-- Every target map preserves the entire original inverse tensor-algebra generator correspondence. -/
theorem tensorAlgebraHomEquiv_symm_natural_target (K : PointedCGWH.{u, v})
    {M Q : Mon SymmetricSequence.{u, v}} (g : degreeOneGenerator K ⟶ M.X) (h : M ⟶ Q) :
    (tensorAlgebraHomEquiv K Q).symm (g ≫ h.hom) =
      (tensorAlgebraHomEquiv K M).symm g ≫ h := by
  apply (tensorAlgebraHomEquiv K Q).injective
  exact ((tensorAlgebraHomEquiv K Q).apply_symm_apply _).trans
    (((congrArg (fun t => t ≫ h.hom) ((tensorAlgebraHomEquiv K M).apply_symm_apply g)).symm).trans
      (tensorAlgebraHomEquiv_natural_target K ((tensorAlgebraHomEquiv K M).symm g) h).symm)

/-- Every coefficient map preserves the entire original inverse tensor-algebra generator correspondence. -/
theorem tensorAlgebraHomEquiv_symm_natural_source {K L : PointedCGWH.{u, v}} (h : K ⟶ L)
    (M : Mon SymmetricSequence.{u, v}) (g : degreeOneGenerator L ⟶ M.X) :
    (tensorAlgebraHomEquiv K M).symm (degreeOneGeneratorFunctor.map h ≫ g) =
      tensorAlgebraFunctor.map h ≫ (tensorAlgebraHomEquiv L M).symm g := by
  apply (tensorAlgebraHomEquiv K M).injective
  exact ((tensorAlgebraHomEquiv K M).apply_symm_apply _).trans
    (((congrArg (fun t => degreeOneGeneratorFunctor.map h ≫ t)
      ((tensorAlgebraHomEquiv L M).apply_symm_apply g)).symm).trans
        (tensorAlgebraHomEquiv_natural_source h M ((tensorAlgebraHomEquiv L M).symm g)).symm)

/-- The complete tensor-algebra inverse keeps both actual original inverse Hom stages. -/
theorem tensorAlgebraAdjunction_inverse (K : PointedCGWH.{u, v})
    (M : Mon SymmetricSequence.{u, v}) (g : K ⟶ tensorAlgebraEvaluation.obj M) :
    (tensorAlgebraAdjunction.homEquiv K M).symm g =
      ((sequenceAdjunction.{u, v}.mapMon.homEquiv (OrderedTensorAlgebra.freeMonoid K) M) :
        (tensorAlgebra K ⟶ M) ≃
          (OrderedTensorAlgebra.freeMonoid K ⟶ (Functor.mapMon U.{u, v}).obj M)).symm
        (((OrderedTensorAlgebra.freeAdjunction.homEquiv K ((Functor.mapMon U.{u, v}).obj M)) :
          (OrderedTensorAlgebra.freeMonoid K ⟶ (Functor.mapMon U.{u, v}).obj M) ≃
            (K ⟶ tensorAlgebraEvaluation.obj M)).symm g) :=
  compositeAdjunction_inverse
    OrderedTensorAlgebra.freeAdjunction sequenceAdjunction.{u, v}.mapMon K M g

/-- The whole original tensor-algebra unit retains the ordered generator and monoidal Kan unit. -/
theorem tensorAlgebraAdjunction_unit_original (K : PointedCGWH.{u, v}) :
    tensorAlgebraAdjunction.{u, v}.unit.app K =
      OrderedTensorAlgebra.freeAdjunction.unit.app K ≫
        OrderedTensorAlgebra.generatorEvaluation.map
          (sequenceAdjunction.{u, v}.mapMon.unit.app (OrderedTensorAlgebra.freeMonoid K)) :=
  Adjunction.comp_unit_app OrderedTensorAlgebra.freeAdjunction sequenceAdjunction.{u, v}.mapMon K

/-- The whole original tensor-algebra counit retains the ordered evaluation and monoidal Kan counit. -/
theorem tensorAlgebraAdjunction_counit_original (M : Mon SymmetricSequence.{u, v}) :
    tensorAlgebraAdjunction.{u, v}.counit.app M =
      (Functor.mapMon G.{u, v}).map
        (OrderedTensorAlgebra.freeAdjunction.counit.app ((Functor.mapMon U.{u, v}).obj M)) ≫
      sequenceAdjunction.{u, v}.mapMon.counit.app M :=
  Adjunction.comp_counit_app OrderedTensorAlgebra.freeAdjunction sequenceAdjunction.{u, v}.mapMon M

/-- Every original coefficient map retains the whole tensor-algebra unit naturality square. -/
theorem tensorAlgebraAdjunction_unit_naturality {K L : PointedCGWH.{u, v}} (h : K ⟶ L) :
    h ≫ tensorAlgebraAdjunction.{u, v}.unit.app L =
      tensorAlgebraAdjunction.{u, v}.unit.app K ≫ tensorAlgebraEvaluation.map (tensorAlgebraFunctor.map h) :=
  tensorAlgebraAdjunction.{u, v}.unit.naturality h

/-- Every original monoid map retains the whole tensor-algebra counit naturality square. -/
theorem tensorAlgebraAdjunction_counit_naturality {M Q : Mon SymmetricSequence.{u, v}} (h : M ⟶ Q) :
    tensorAlgebraFunctor.map (tensorAlgebraEvaluation.map h) ≫ tensorAlgebraAdjunction.{u, v}.counit.app Q =
      tensorAlgebraAdjunction.{u, v}.counit.app M ≫ h :=
  tensorAlgebraAdjunction.{u, v}.counit.naturality h

/-- Both complete tensor-algebra adjunction triangles hold at every original source and target. -/
theorem tensorAlgebraAdjunction_triangles_original
    (K : PointedCGWH.{u, v}) (M : Mon SymmetricSequence.{u, v}) :
    tensorAlgebraFunctor.map (tensorAlgebraAdjunction.{u, v}.unit.app K) ≫
      tensorAlgebraAdjunction.{u, v}.counit.app (tensorAlgebraFunctor.obj K) = 𝟙 (tensorAlgebraFunctor.obj K) ∧
    tensorAlgebraAdjunction.{u, v}.unit.app (tensorAlgebraEvaluation.obj M) ≫
      tensorAlgebraEvaluation.map (tensorAlgebraAdjunction.{u, v}.counit.app M) =
        𝟙 (tensorAlgebraEvaluation.obj M) :=
  ⟨tensorAlgebraAdjunction.{u, v}.left_triangle_components K,
    tensorAlgebraAdjunction.{u, v}.right_triangle_components M⟩

/-- The actual symmetric-algebra inverse is the full original extension of the given coefficient generator. -/
theorem symmetricAlgebraAdjunction_inverse (K : PointedCGWH.{u, v})
    (M : CommMon SymmetricSequence.{u, v}) (g : K ⟶ symmetricAlgebraEvaluation.obj M) :
    (symmetricAlgebraAdjunction.homEquiv K M).symm g =
      SymmetricTensorAlgebra.fromGeneratorMonoid K M g :=
  congrArg (fun e => e.symm g) (SymmetricTensorAlgebra.freeAdjunction_homEquiv K M)

/-- The complete original commutative-algebra unit is its actual degree-one coefficient insertion. -/
theorem symmetricAlgebraAdjunction_unit_original (K : PointedCGWH.{u, v}) :
    symmetricAlgebraAdjunction.{u, v}.unit.app K = (λ_ K).inv :=
  SymmetricTensorAlgebra.freeAdjunction_unit K

/-- The complete original commutative-algebra counit extends the whole identity generator. -/
theorem symmetricAlgebraAdjunction_counit_original (M : CommMon SymmetricSequence.{u, v}) :
    symmetricAlgebraAdjunction.{u, v}.counit.app M =
      SymmetricTensorAlgebra.fromGeneratorMonoid (symmetricAlgebraEvaluation.obj M) M (𝟙 _) :=
  SymmetricTensorAlgebra.freeAdjunction_counit M

/-- Every original coefficient arrow retains the complete symmetric-algebra unit square. -/
theorem symmetricAlgebraAdjunction_unit_naturality {K L : PointedCGWH.{u, v}} (h : K ⟶ L) :
    h ≫ symmetricAlgebraAdjunction.{u, v}.unit.app L =
      symmetricAlgebraAdjunction.{u, v}.unit.app K ≫
        symmetricAlgebraEvaluation.map (symmetricAlgebraFunctor.map h) :=
  symmetricAlgebraAdjunction.{u, v}.unit.naturality h

/-- Every original commutative-monoid arrow retains the complete symmetric-algebra counit square. -/
theorem symmetricAlgebraAdjunction_counit_naturality
    {M Q : CommMon SymmetricSequence.{u, v}} (h : M ⟶ Q) :
    symmetricAlgebraFunctor.map (symmetricAlgebraEvaluation.map h) ≫
      symmetricAlgebraAdjunction.{u, v}.counit.app Q = symmetricAlgebraAdjunction.{u, v}.counit.app M ≫ h :=
  symmetricAlgebraAdjunction.{u, v}.counit.naturality h

/-- Both complete original commutative-algebra triangles hold at every original source and target. -/
theorem symmetricAlgebraAdjunction_triangles_original
    (K : PointedCGWH.{u, v}) (M : CommMon SymmetricSequence.{u, v}) :
    symmetricAlgebraFunctor.map (symmetricAlgebraAdjunction.{u, v}.unit.app K) ≫
      symmetricAlgebraAdjunction.{u, v}.counit.app (symmetricAlgebraFunctor.obj K) =
        𝟙 (symmetricAlgebraFunctor.obj K) ∧
    symmetricAlgebraAdjunction.{u, v}.unit.app (symmetricAlgebraEvaluation.obj M) ≫
      symmetricAlgebraEvaluation.map (symmetricAlgebraAdjunction.{u, v}.counit.app M) =
        𝟙 (symmetricAlgebraEvaluation.obj M) :=
  ⟨symmetricAlgebraAdjunction.{u, v}.left_triangle_components K,
    symmetricAlgebraAdjunction.{u, v}.right_triangle_components M⟩

/-- The whole original generator inclusion into every original commutative symmetric algebra. -/
def symmetricAlgebraGenerator (K : PointedCGWH.{u, v}) : degreeOneGenerator K ⟶ (symmetricAlgebra K).X :=
  symmetricAlgebraHomEquiv K (symmetricAlgebra K) (𝟙 (symmetricAlgebra K))

/-- Every original commutative-monoid morphism is evaluated at the same complete generator inclusion. -/
theorem symmetricAlgebraHomEquiv_generator (K : PointedCGWH.{u, v})
    (M : CommMon SymmetricSequence.{u, v}) (f : symmetricAlgebra K ⟶ M) :
    symmetricAlgebraHomEquiv K M f = symmetricAlgebraGenerator K ≫ f.hom.hom := by
  have h := symmetricAlgebraHomEquiv_natural_target K (𝟙 (symmetricAlgebra K)) f
  exact (congrArg (symmetricAlgebraHomEquiv K M) (Category.id_comp f)).symm.trans h

/-- Every original coefficient arrow preserves the complete tensor-algebra generator inclusion. -/
theorem tensorAlgebraGenerator_naturality {K L : PointedCGWH.{u, v}} (h : K ⟶ L) :
    degreeOneGeneratorFunctor.map h ≫ tensorAlgebraGenerator L =
      tensorAlgebraGenerator K ≫ (tensorAlgebraFunctor.map h).hom := by
  have hs := tensorAlgebraHomEquiv_natural_source h (tensorAlgebra L) (𝟙 (tensorAlgebra L))
  have ht := tensorAlgebraHomEquiv_generator K (tensorAlgebra L) (tensorAlgebraFunctor.map h)
  exact ((congrArg (tensorAlgebraHomEquiv K (tensorAlgebra L)) (Category.comp_id _)).symm.trans hs).symm.trans ht

/-- Every original coefficient arrow preserves the complete commutative-algebra generator inclusion. -/
theorem symmetricAlgebraGenerator_naturality {K L : PointedCGWH.{u, v}} (h : K ⟶ L) :
    degreeOneGeneratorFunctor.map h ≫ symmetricAlgebraGenerator L =
      symmetricAlgebraGenerator K ≫ (symmetricAlgebraFunctor.map h).hom.hom := by
  have hs := symmetricAlgebraHomEquiv_natural_source h (symmetricAlgebra L) (𝟙 (symmetricAlgebra L))
  have ht := symmetricAlgebraHomEquiv_generator K (symmetricAlgebra L) (symmetricAlgebraFunctor.map h)
  exact ((congrArg (symmetricAlgebraHomEquiv K (symmetricAlgebra L)) (Category.comp_id _)).symm.trans hs).symm.trans ht

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
