/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingTruncation
public import MathlibExt.Algebra.Homology.Embedding.PositiveTruncation
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Strict-positive pairings and their cokernels

In a monoidal Abelian category, a pairing of nonnegative chain complexes
with zero degree-one boundaries restricts along their positive-part
inclusions. Its cokernel is the strict-positive quotient complex. The
original degree-zero objects may be nonzero; the two boundary equations
give the inclusions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe v u

namespace HomologicalComplex.ChainGradedPairing

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [CategoryTheory.MonoidalPreadditive C]
  {K₁ K₂ K₃ : ChainComplex C ℕ} (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

local notation "e₊" => ComplexShape.positiveNatEmbedding

/-- Restrict the actual pairing by the earned native inclusions of the whole positive part. -/
def strictPositivePairing :
    ChainGradedPairing (K₁.stupidTrunc e₊) (K₂.stupidTrunc e₊) K₃ :=
  tensorHom (K₁.positiveStupidTruncInclusion h₁)
    (K₂.positiveStupidTruncInclusion h₂) ≫ P

/-- The smart-to-strict tensor comparison retains the original smart restricted pairing. -/
@[reassoc]
theorem smartToStrictPositivePairing :
    tensorHom (K₁.truncLEToStupid e₊) (K₂.truncLEToStupid e₊) ≫
        strictPositivePairing P h₁ h₂ = truncationPairing e₊ P := by
  rw [strictPositivePairing, ← Category.assoc, tensorHom_comp_tensorHom,
    truncLEToStupid_comp_positiveStupidTruncInclusion,
    truncLEToStupid_comp_positiveStupidTruncInclusion]
  rfl

/-- The actual strict-positive pairing has its native cokernel in the category of complexes. -/
def strictPositiveCokernel : ChainComplex C ℕ := cokernel (strictPositivePairing P h₁ h₂)

/-- The native projection from the original target complex. -/
def strictPositiveProjection : K₃ ⟶ strictPositiveCokernel P h₁ h₂ :=
  cokernel.π (strictPositivePairing P h₁ h₂)

/-- The native quotient really kills the original restricted pairing. -/
@[reassoc]
theorem strictPositivePairing_comp_projection :
    strictPositivePairing P h₁ h₂ ≫ strictPositiveProjection P h₁ h₂ = 0 :=
  cokernel.condition _

end HomologicalComplex.ChainGradedPairing
