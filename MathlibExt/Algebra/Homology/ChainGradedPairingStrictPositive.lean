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

/-- Let C be abelian and monoidal with tensor product additive in each variable, and let
P : K₁ ⊗ K₂ → K₃ pair nonnegative chain complexes with d_K₁,1,0 = d_K₂,1,0 = 0.
The quotient by the smart positive truncation is canonically isomorphic to the cokernel
of the pairing on the whole positive stupid truncations. The comparison induces the
identity on the target complex K₃. -/
def truncationQuotientIsoStrictPositiveCokernel :
    truncationQuotient e₊ P ≅ strictPositiveCokernel P h₁ h₂ := by
  let e₁ := K₁.positiveTruncLEToStupidIso h₁
  let e₂ := K₂.positiveTruncLEToStupidIso h₂
  let eT : tensorObj (K₁.truncLE e₊) (K₂.truncLE e₊) ≅
      tensorObj (K₁.stupidTrunc e₊) (K₂.stupidTrunc e₊) :=
    MonoidalCategory.tensorIso e₁ e₂
  refine cokernel.mapIso (truncationPairing e₊ P) (strictPositivePairing P h₁ h₂)
    eT (Iso.refl K₃) ?_
  change truncationPairing e₊ P ≫ 𝟙 K₃ =
    tensorHom (K₁.truncLEToStupid e₊) (K₂.truncLEToStupid e₊) ≫
      strictPositivePairing P h₁ h₂
  rw [Category.comp_id]
  exact (smartToStrictPositivePairing P h₁ h₂).symm

/-- For an abelian monoidal category C with additive tensor product, a pairing P of nonnegative
chain complexes and vanishing degree-one boundaries in both inputs, the smart-positive
projection followed by truncationQuotientIsoStrictPositiveCokernel equals the strict-positive
projection from K₃. -/
@[reassoc]
theorem truncationProjection_isoStrictPositive_hom :
    truncationProjection e₊ P ≫
        (truncationQuotientIsoStrictPositiveCokernel P h₁ h₂).hom =
      strictPositiveProjection P h₁ h₂ := by
  simp only [truncationProjection, strictPositiveProjection,
    truncationQuotientIsoStrictPositiveCokernel, cokernel.mapIso, cokernel.map,
    cokernel.π_desc, Iso.refl_hom, Category.id_comp]

/-- For an abelian monoidal category C with additive tensor product and a nonnegative chain
pairing whose two degree-one boundaries vanish, the strict-positive projection followed by
the inverse comparison equals the smart-positive projection from K₃. -/
@[reassoc]
theorem strictPositiveProjection_isoTruncation_inv :
    strictPositiveProjection P h₁ h₂ ≫
        (truncationQuotientIsoStrictPositiveCokernel P h₁ h₂).inv =
      truncationProjection e₊ P := by
  apply (cancel_mono (truncationQuotientIsoStrictPositiveCokernel P h₁ h₂).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (truncationProjection_isoStrictPositive_hom P h₁ h₂).symm

end HomologicalComplex.ChainGradedPairing
