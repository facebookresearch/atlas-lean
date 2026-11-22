/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Core
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.SymmetricTensorAlgebra

/-!
# The actual native symmetric algebra on the original Kan generator

The complete original sphere sequence is the commutative algebra on its
original freely symmetrized degree-one circle. Its genuine generator Hom
correspondence retains both directions and every original coefficient map.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison

open CategoryTheory.Operad.SmallFinBijGroupoid
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj

/-- The full original commutative symmetric power algebra on every pointed coefficient. -/
def symmetricAlgebraFunctor : PointedCGWH.{u, v} ⥤ CommMon SymmetricSequence.{u, v} :=
  SymmetricTensorAlgebra.freeFunctor

/-- The full original degree-one evaluation on every actual commutative symmetric monoid. -/
def symmetricAlgebraEvaluation : CommMon SymmetricSequence.{u, v} ⥤ PointedCGWH.{u, v} :=
  SymmetricTensorAlgebra.generatorEvaluation

/-- The entire symmetric algebra retains its actual original unit, multiplication and permutation data. -/
def symmetricAlgebra (K : PointedCGWH.{u, v}) : CommMon SymmetricSequence.{u, v} :=
  symmetricAlgebraFunctor.obj K

/-- The genuine original commutative symmetric algebra/evaluation adjunction. -/
def symmetricAlgebraAdjunction : symmetricAlgebraFunctor.{u, v} ⊣ symmetricAlgebraEvaluation.{u, v} :=
  SymmetricTensorAlgebra.freeAdjunction

/-- The evaluation is the complete original forgetful and Kan-generator right functor. -/
theorem symmetricAlgebraEvaluation_original : symmetricAlgebraEvaluation.{u, v} =
    CommMon.forget SymmetricSequence.{u, v} ⋙ degreeOneGeneratorEvaluation.{u, v} := rfl

/-- The actual original symmetric sphere monoid is precisely the full commutative circle algebra. -/
theorem symmetricAlgebraCircle_original :
    symmetricAlgebra PointedCGWH.sphereOne.{u, v} = sphereSequenceCommMon.{u, v} := rfl

/-- Both entire original Hom functions prove the genuine symmetric-algebra generator universal property. -/
def symmetricAlgebraHomEquiv (K : PointedCGWH.{u, v}) (M : CommMon SymmetricSequence.{u, v}) :
    (symmetricAlgebra K ⟶ M) ≃ (degreeOneGenerator K ⟶ M.X) :=
  (symmetricAlgebraAdjunction.homEquiv K M).trans
    (degreeOneGeneratorAdjunction.homEquiv K M.X).symm

/-- The complete forward and inverse symmetric-algebra Hom functions recover every original monoid map. -/
theorem symmetricAlgebraHomEquiv_left_inverse (K : PointedCGWH.{u, v}) (M : CommMon SymmetricSequence.{u, v})
    (f : symmetricAlgebra K ⟶ M) :
    (symmetricAlgebraHomEquiv K M).symm (symmetricAlgebraHomEquiv K M f) = f :=
  (symmetricAlgebraHomEquiv K M).symm_apply_apply f

/-- The complete inverse and forward symmetric-algebra Hom functions recover every original generator map. -/
theorem symmetricAlgebraHomEquiv_right_inverse (K : PointedCGWH.{u, v}) (M : CommMon SymmetricSequence.{u, v})
    (g : degreeOneGenerator K ⟶ M.X) :
    symmetricAlgebraHomEquiv K M ((symmetricAlgebraHomEquiv K M).symm g) = g :=
  (symmetricAlgebraHomEquiv K M).apply_symm_apply g

/-- Every original target monoid arrow preserves the entire symmetric-algebra generator correspondence. -/
theorem symmetricAlgebraHomEquiv_natural_target (K : PointedCGWH.{u, v})
    {M Q : CommMon SymmetricSequence.{u, v}} (f : symmetricAlgebra K ⟶ M) (h : M ⟶ Q) :
    symmetricAlgebraHomEquiv K Q (f ≫ h) = symmetricAlgebraHomEquiv K M f ≫ h.hom.hom := by
  have hT := symmetricAlgebraAdjunction.{u, v}.homEquiv_naturality_right f h
  have hG := degreeOneGeneratorAdjunction.{u, v}.homEquiv_naturality_right_symm
    (symmetricAlgebraAdjunction.homEquiv K M f) h.hom.hom
  exact (congrArg (degreeOneGeneratorAdjunction.homEquiv K Q.X).symm hT).trans hG

/-- Every original coefficient arrow preserves the entire symmetric-algebra generator correspondence. -/
theorem symmetricAlgebraHomEquiv_natural_source {K L : PointedCGWH.{u, v}} (h : K ⟶ L)
    (M : CommMon SymmetricSequence.{u, v}) (f : symmetricAlgebra L ⟶ M) :
    symmetricAlgebraHomEquiv K M (symmetricAlgebraFunctor.map h ≫ f) =
      degreeOneGeneratorFunctor.map h ≫ symmetricAlgebraHomEquiv L M f := by
  have hT := symmetricAlgebraAdjunction.{u, v}.homEquiv_naturality_left h f
  have hG := degreeOneGeneratorAdjunction.{u, v}.homEquiv_naturality_left_symm
    h (symmetricAlgebraAdjunction.homEquiv L M f)
  exact (congrArg (degreeOneGeneratorAdjunction.homEquiv K M.X).symm hT).trans hG


/-- Every whole target map preserves the complete inverse symmetric-generator correspondence. -/
theorem symmetricAlgebraHomEquiv_symm_natural_target (K : PointedCGWH.{u, v})
    {M Q : CommMon SymmetricSequence.{u, v}} (g : degreeOneGenerator K ⟶ M.X) (h : M ⟶ Q) :
    (symmetricAlgebraHomEquiv K Q).symm (g ≫ h.hom.hom) =
      (symmetricAlgebraHomEquiv K M).symm g ≫ h := by
  apply (symmetricAlgebraHomEquiv K Q).injective
  exact ((symmetricAlgebraHomEquiv K Q).apply_symm_apply _).trans
    (((congrArg (fun t => t ≫ h.hom.hom)
      ((symmetricAlgebraHomEquiv K M).apply_symm_apply g)).symm).trans
        (symmetricAlgebraHomEquiv_natural_target K ((symmetricAlgebraHomEquiv K M).symm g) h).symm)

/-- Every whole coefficient map preserves the complete inverse symmetric-generator correspondence. -/
theorem symmetricAlgebraHomEquiv_symm_natural_source {K L : PointedCGWH.{u, v}} (h : K ⟶ L)
    (M : CommMon SymmetricSequence.{u, v}) (g : degreeOneGenerator L ⟶ M.X) :
    (symmetricAlgebraHomEquiv K M).symm (degreeOneGeneratorFunctor.map h ≫ g) =
      symmetricAlgebraFunctor.map h ≫ (symmetricAlgebraHomEquiv L M).symm g := by
  apply (symmetricAlgebraHomEquiv K M).injective
  exact ((symmetricAlgebraHomEquiv K M).apply_symm_apply _).trans
    (((congrArg (fun t => degreeOneGeneratorFunctor.map h ≫ t)
      ((symmetricAlgebraHomEquiv L M).apply_symm_apply g)).symm).trans
        (symmetricAlgebraHomEquiv_natural_source h M ((symmetricAlgebraHomEquiv L M).symm g)).symm)

/-- The original forward symmetric algebra Hom function is its actual complete degree-one coefficient. -/
theorem symmetricAlgebraAdjunction_forward (K : PointedCGWH.{u, v})
    (M : CommMon SymmetricSequence.{u, v}) (f : symmetricAlgebra K ⟶ M) :
    symmetricAlgebraAdjunction.homEquiv K M f =
      (λ_ K).inv ≫ f.hom.hom.natTrans.app (card 1) :=
  congrArg (fun e => e f) (SymmetricTensorAlgebra.freeAdjunction_homEquiv K M)

/-- The whole original circle generator is the generator of the genuine commutative sphere algebra. -/
theorem symmetricSphereGenerator_free_commutative :
    symmetricAlgebraHomEquiv PointedCGWH.sphereOne.{u, v} sphereSequenceCommMon.{u, v}
      (𝟙 sphereSequenceCommMon.{u, v}) = symmetricSphereGenerator.{u, v} :=
  congrArg
    (degreeOneGeneratorAdjunction.homEquiv PointedCGWH.sphereOne.{u, v} sphereSequence.{u, v}).symm
    ((symmetricAlgebraAdjunction_forward PointedCGWH.sphereOne.{u, v} sphereSequenceCommMon.{u, v}
      (𝟙 sphereSequenceCommMon.{u, v})).trans (Category.comp_id _))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
