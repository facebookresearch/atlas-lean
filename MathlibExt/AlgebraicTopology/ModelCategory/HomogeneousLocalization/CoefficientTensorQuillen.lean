/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.CoefficientTensorHom
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer

/-!
# The actual coefficient tensor-Hom adjunction is Quillen

The original monoid axiom, generating families and uniform source smallness
construct the full model on the existing R-module category.  Its actual
created fibration and trivial-fibration classes, the original free internal-
Hom comparison, and the base tensor-Hom Quillen theorem prove the actual
module adjunction Quillen for cofibrant U.

No module model or Quillen result is supplied as an output premise.  No
cofibrancy of the coefficient R, intrinsic module flatness, beta locality or
relative derived tensor conclusion is asserted by this source theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

open CategoryTheory Limits MorphismProperty MonoidalCategory
open CategoryTheory.HomogeneousLocalization
open CategoryTheory.SmallObject
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.CoefficientTensorQuillen

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C] [MonoidAxiom.{w} C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [HasEqualizers C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (R : CommMon C) (U : C) [IsCofibrant U]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (sI : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators R.toMon I))
  (sJ : UniformRelativeSourceSmallness.{w} (ModuleTransfer.leftGenerators R.toMon J))

/-- The actual ordinary module model is the existing full transfer from the original source data. -/
def transfer :
    RightTransfer.FullModelTransfer (Mod.free R.X) (Mod.forget (D := C) R.X) I J sI sJ :=
  ModuleTransfer.fullLeftModuleModelTransfer R.toMon I J hI hJ sI sJ

/-- The original natural internal-Hom comparison gives a whole Arrow isomorphism on every module map. -/
def underlyingArrowIso
    {M N : Mod C R.X} (f : M ⟶ N) :
    Arrow.mk (((CoefficientTensorHom.rightFunctor R U).map f).hom) ≅
      Arrow.mk ((ihom U).map f.hom) :=
  Arrow.isoMk (CoefficientTensorHom.underlyingRightIso R U M)
    (CoefficientTensorHom.underlyingRightIso R U N)
    (Mod.FreeInternalHom.forward_naturality R U f).symm

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Fibrations are preserved by the actual right adjoint, using the created module class. -/
theorem preservesFibrations :
    letI := (transfer R I J hI hJ sI sJ).model
    PreservesFibrations (CoefficientTensorHom.rightFunctor R U) := by
  let t := transfer R I J hI hJ sI sJ
  let _ := t.model
  intro M N f hf
  rw [t.fibrations_eq] at hf ⊢
  change fibrations C (((CoefficientTensorHom.rightFunctor R U).map f).hom)
  have hb : fibrations C ((ihom U).map f.hom) :=
    (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesFibrations f.hom hf
  exact ((fibrations C).arrow_mk_iso_iff (underlyingArrowIso R U f)).mpr hb

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The same actual Arrow comparison preserves every original trivial fibration. -/
theorem preservesTrivialFibrations :
    letI := (transfer R I J hI hJ sI sJ).model
    PreservesTrivialFibrations (CoefficientTensorHom.rightFunctor R U) := by
  let t := transfer R I J hI hJ sI sJ
  let _ := t.model
  intro M N f hf
  rw [t.trivialFibrations_eq] at hf ⊢
  change trivialFibrations C (((CoefficientTensorHom.rightFunctor R U).map f).hom)
  have hb : trivialFibrations C ((ihom U).map f.hom) :=
    (ihomAdjunction_isQuillenAdjunction_of_isCofibrant U).preservesTrivialFibrations f.hom hf
  exact ((trivialFibrations C).arrow_mk_iso_iff (underlyingArrowIso R U f)).mpr hb

/-- The actual ambient coefficient tensor/internal-Hom adjunction is Quillen in the constructed module model. -/
theorem isQuillenAdjunction :
    letI := (transfer R I J hI hJ sI sJ).model
    (CoefficientTensorHom.adjunction R U).IsQuillenAdjunction := by
  let t := transfer R I J hI hJ sI sJ
  let _ := t.model
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations (adj := CoefficientTensorHom.adjunction R U)
    (preservesFibrations R U I J hI hJ sI sJ)
    (preservesTrivialFibrations R U I J hI hJ sI sJ)

end HomotopicalAlgebra.CoefficientTensorQuillen
