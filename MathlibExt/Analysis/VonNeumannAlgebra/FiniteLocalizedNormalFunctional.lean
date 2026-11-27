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

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedNormalFunctional

/-!
# Finite sums of projection-localized normal functionals

For a positive bounded functional `ψ`, let star projections `p_i` and vectors `ξ_i` satisfy `Re
ψ(b)≤Re ⟨ξ_i,bξ_i⟩` whenever `0≤b≤p_i`. Each functional `a ↦ ψ(ap_i)` is normal.

For any finite subset `s` of the index type, their sum is a member `ρ_s∈M_*` with `ρ_s(a)=ψ(a
Σ_i∈s p_i)`. Orthogonality of the projections is not required for this finite sum.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Normal functional of a finite projection localization sum.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `p_i ∈ M` be star
projections indexed by an arbitrary type `I`, and `ξ_i ∈ H` satisfy `Re ψ(b)≤Re
⟨ξ_i,bξ_i⟩` whenever `0≤b≤p_i`. for `s : Finset I`, `finiteLocalizedNormalFunctional`
returns `ρ_s∈M_*` with `ρ_s(a)=ψ(a*Σ_i∈s p_i)` for all `a∈M`. No pairwise orthogonality is
assumed. -/
def finiteLocalizedNormalFunctional (M : VonNeumannAlgebra H) {I : Type v} :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : I → M) →
      (hp : ∀ i, IsStarProjection (p i)) → (ξ : I → H) →
      (∀ i, ∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (p i) →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M (ξ i) (ξ i) (b : M)).re) →
      (s : Finset I) → {ρ : normalFunctionalSpace M // ∀ a : M,
        (ρ.val : StrongDual ℂ M) a = ψ.toContinuousLinearMap (a * ∑ i ∈ s, p i)} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal s
  let pieces (i : I) := localizedNormalFunctional M ψ (p i) (hp i) (ξ i) (hlocal i)
  let ρ : normalFunctionalSpace M := ∑ i ∈ s, (pieces i).val
  refine ⟨ρ, ?_⟩
  intro a
  have hvalues (i : I) : ((pieces i).val.val : StrongDual ℂ M) a =
      ψ.toContinuousLinearMap (a * p i) := (pieces i).property a
  change ((∑ i ∈ s, (pieces i).val : normalFunctionalSpace M).val : StrongDual ℂ M) a = _
  simp only [Submodule.coe_sum, sum_apply, hvalues, Finset.mul_sum, map_sum]

end

end VonNeumannAlgebra
