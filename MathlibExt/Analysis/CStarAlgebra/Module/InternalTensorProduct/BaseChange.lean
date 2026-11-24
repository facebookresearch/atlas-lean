/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.CanonicalBaseChange

/-!
# Actual nonunital coefficient base change of Hilbert modules

The carrier is the existing balanced quotient, radical quotient and stock
completion for E tensor the target coefficient self-module. The existing
full model, canonical vector map, unital End map and real module-compact
transport are used directly, with the original coefficient orders retained.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra CStarModule.Right RightActions

namespace CStarModule.InternalTensorProduct.BaseChange

universe uB uC uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {C : Type uC} [NonUnitalCStarAlgebra C]
  [PartialOrder Cᵐᵒᵖ] [StarOrderedRing Cᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual left regular target self-module action along the original coefficient hom. -/
def coefficientAction (f : B →⋆ₙₐ[ℂ] C) : B →⋆ₙₐ[ℂ] AdjointableOperator.End C C :=
  (AdjointableOperator.leftRegular (B := C)).comp f

omit [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ] in
/-- The same original left coefficient value, without a unit in either algebra. -/
@[simp]
theorem coefficientAction_apply (f : B →⋆ₙₐ[ℂ] C) (b : B) (c : C) :
    coefficientAction f b c = f b * c := rfl

/-- The genuine existing completed tensor; its carrier universe is max uE uC. -/
abbrev Carrier (f : B →⋆ₙₐ[ℂ] C) := CompletedTensor (E₁ := E) (coefficientAction f)

/-- The original quotient/completion normed-group dictionary. -/
@[instance_reducible]
def normedAddCommGroup (f : B →⋆ₙₐ[ℂ] C) : NormedAddCommGroup (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  exact inferInstance

attribute [local instance] normedAddCommGroup

/-- The original completed complex-space dictionary. -/
@[instance_reducible]
def normedSpace (f : B →⋆ₙₐ[ℂ] C) : NormedSpace ℂ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  exact inferInstance

attribute [local instance] normedSpace

/-- The original completed right target-coefficient action. -/
@[instance_reducible]
def rightAction (f : B →⋆ₙₐ[ℂ] C) : SMul Cᵐᵒᵖ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  letI : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact inferInstance

attribute [local instance] rightAction

/-- The genuine completed Hilbert-module dictionary, on the same original norm and action. -/
@[instance_reducible]
def cstarModule (f : B →⋆ₙₐ[ℂ] C) : CStarModule Cᵐᵒᵖ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  letI : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact completedCStarModule (coefficientAction f)

attribute [local instance] cstarModule

/-- The actual two-quotient/completion pure tensor map. -/
def pure (f : B →⋆ₙₐ[ℂ] C) (x : E) (c : C) : Carrier (E := E) f :=
  completedPure (coefficientAction f) x c

/-- Every full model clause is proved for the same actual completed tensor. -/
theorem isModel (f : B →⋆ₙₐ[ℂ] C) : IsModel (coefficientAction f) (pure (E := E) f) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  let : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  let : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact completed_isModel (coefficientAction f)

/-- Pure coefficient inners are the actual original Gram formula along the given hom. -/
theorem pure_inner (f : B →⋆ₙₐ[ℂ] C) (x y : E) (c d : C) :
    CStarModule.rightInner (B := C) (pure f x c) (pure f y d) =
      star c * f (CStarModule.rightInner (B := B) x y) * d := by
  simpa only [coefficientAction_apply, CStarModule.Right.rightInner_self, mul_assoc] using
    (isModel (E := E) f).2.2.2.2.2.2.1 x y c d

/-- The genuine canonical vector map, defined through strict nonunital factorization. -/
def canonicalMap (f : B →⋆ₙₐ[ℂ] C) : E →L[ℂ] Carrier (E := E) f :=
  IsModel.canonicalBaseChangeMap (isModel (E := E) f)

/-- The exact original coefficient-inner formula of the canonical vector map. -/
@[simp]
theorem canonicalMap_inner (f : B →⋆ₙₐ[ℂ] C) (x y : E) :
    CStarModule.rightInner (B := C) (canonicalMap f x) (canonicalMap f y) =
      f (CStarModule.rightInner (B := B) x y) :=
  IsModel.canonicalBaseChangeMap_inner (isModel (E := E) f) x y

/-- The actual canonical vector map is contractive; no coefficient injectivity is assumed. -/
theorem norm_canonicalMap_le (f : B →⋆ₙₐ[ℂ] C) (x : E) : ‖canonicalMap f x‖ ≤ ‖x‖ :=
  IsModel.norm_canonicalBaseChangeMap_le (isModel (E := E) f) x

/-- Canonical vectors preserve the original right action along the given hom. -/
@[simp]
theorem canonicalMap_right_smul (f : B →⋆ₙₐ[ℂ] C) (x : E) (b : B) :
    canonicalMap f (x <• b) = canonicalMap f x <• f b :=
  IsModel.canonicalBaseChangeMap_right_smul (isModel (E := E) f) x b

/-- Pure tensors are exactly the original canonical images acted on by target coefficients. -/
@[simp]
theorem canonicalMap_pure (f : B →⋆ₙₐ[ℂ] C) (x : E) (c : C) :
    canonicalMap f x <• c = pure f x c :=
  IsModel.canonicalBaseChangeMap_pure (isModel (E := E) f) x c

/-- The same full model constructs the genuine unital End transport. -/
def endomorphismMap (f : B →⋆ₙₐ[ℂ] C) : AdjointableOperator.End B E →⋆ₐ[ℂ]
    AdjointableOperator.End C (Carrier (E := E) f) :=
  IsModel.mapLeftStarAlgHom (isModel (E := E) f)

/-- Every original operator has its actual pure-tensor value. -/
@[simp]
theorem endomorphismMap_pure (f : B →⋆ₙₐ[ℂ] C) (T : AdjointableOperator.End B E)
    (x : E) (c : C) : endomorphismMap f T (pure f x c) = pure f (T x) c :=
  IsModel.mapLeftStarAlgHom_pure (isModel (E := E) f) T x c

/-- Every original operator intertwines the actual canonical vector map. -/
@[simp]
theorem endomorphismMap_canonicalMap (f : B →⋆ₙₐ[ℂ] C) (T : AdjointableOperator.End B E)
    (x : E) : endomorphismMap f T (canonicalMap f x) = canonicalMap f (T x) :=
  IsModel.mapLeftStarAlgHom_canonicalBaseChangeMap (isModel (E := E) f) T x

/-- The real original rank-one maps to the rank-one of actual canonical vector images. -/
theorem endomorphismMap_rankOne (f : B →⋆ₙₐ[ℂ] C) (x y : E) :
    endomorphismMap f (AdjointableOperator.rankOne (B := B) x y) =
      AdjointableOperator.rankOne (B := C) (canonicalMap f x) (canonicalMap f y) :=
  IsModel.mapLeftStarAlgHom_rankOne_baseChange (isModel (E := E) f) x y

/-- Actual module compacts are preserved for any original coefficient hom, including zero. -/
theorem endomorphismMap_mem_compact (f : B →⋆ₙₐ[ℂ] C) {T : AdjointableOperator.End B E}
    (hT : T ∈ AdjointableOperator.compactSubmodule (B := B) (E := E) (F := E)) :
    endomorphismMap f T ∈ AdjointableOperator.compactSubmodule
      (B := C) (E := Carrier (E := E) f) (F := Carrier (E := E) f) :=
  IsModel.mapLeftStarAlgHom_mem_compact_baseChange (isModel (E := E) f) hT

/-- Countable generation is genuinely derived without a target-coefficient CG premise. -/
theorem countablyGenerated (f : B →⋆ₙₐ[ℂ] C)
    (hE : CStarModule.IsCountablyGenerated (B := B) (E := E)) :
    CStarModule.IsCountablyGenerated (B := C) (E := Carrier (E := E) f) :=
  IsModel.countablyGenerated_baseChange (isModel (E := E) f) hE

end CStarModule.InternalTensorProduct.BaseChange
