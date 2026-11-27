/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Filtration
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientComparison

/-!
# Total degree and the enveloping Chevalley–Eilenberg differential

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `U = U_R(L)`. On the exterior-first
regular-coefficient term `⋀ⁿ[R] L ⊗[R] U`, total degree is enveloping degree plus exterior
degree. The regular Lie coefficient action is `[x,u] = -uι(x)`.

On `(v₀ ∧ ⋯ ∧ vₙ) ⊗ u`, the differential is the bracket boundary tensored with `u`, plus `∑ᵢ
(-1)^i (v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ) ⊗ uι(vᵢ)`. The action part preserves total degree, while the
bracket part lies in the previous filtration stage. Thus modulo that stage the differential
equals its action part.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The signed regular-coefficient action boundary.

For `v : Fin (n+1) → L` and `u ∈ U_R(L)`, the action boundary of `(⋀ᵢ vᵢ) ⊗ u` is `∑ᵢ (-1)^i
(⋀_(j≠i) vⱼ) ⊗ uι(vᵢ)`, with surviving indices in increasing order. -/
theorem envelopingActionBoundary_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (u : regularCoefficients R L) :
    coefficientActionBoundary R L (regularCoefficients R L) n
        (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] u) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R]
          (u * UniversalEnvelopingAlgebra.ι R (v i))) := by
  rw [coefficientActionBoundary_apply_ιMulti_tmul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [regularCoefficients_lie, pow_succ, mul_smul]
  congr 1
  rw [← TensorProduct.tmul_smul, neg_one_smul, neg_neg]

/-- The bracket-and-action formula for the enveloping differential.

On `(v₀ ∧ ⋯ ∧ vₙ) ⊗ u`, the differential is `d(v₀ ∧ ⋯ ∧ vₙ) ⊗ u` plus the signed deletion sum
`∑ᵢ (-1)^i (v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ) ⊗ uι(vᵢ)`. The enveloping multiplication occurs on the
right of `u`. -/
theorem envelopingDifferential_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (u : regularCoefficients R L) :
    coefficientDifferential R L (regularCoefficients R L) n
        (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] u) =
      differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] u +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R]
            (u * UniversalEnvelopingAlgebra.ι R (v i))) := by
  rw [coefficientDifferential_eq_bracket_add_action, LinearMap.add_apply,
    LinearMap.rTensor_tmul, envelopingActionBoundary_apply_ιMulti_tmul]

/-- The filtration drop of the enveloping bracket boundary.

If a chain in degree `n+1` belongs to total filtration stage `p`, its bracket boundary
tensored with regular coefficients lies in stage `p-1` in degree `n`. The subtraction is in
`ℕ`. -/
theorem envelopingBracketBoundary_mem_lowerFiltration (p n : ℕ)
    {z : (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p (n + 1)) :
    (differential R L n).rTensor (regularCoefficients R L) z ∈
      envelopingFiltration R L (p - 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, v, u, hq, hu, rfl⟩ := hz
      rw [LinearMap.rTensor_tmul]
      exact tmul_mem_envelopingFiltration R L (p - 1) n q
        (differential R L n (exteriorPower.ιMulti R (n + 1) v)) u
        (by omega) hu
  | zero =>
      rw [map_zero]
      exact (envelopingFiltration R L (p - 1) n).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (envelopingFiltration R L (p - 1) n).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (envelopingFiltration R L (p - 1) n).smul_mem r ih

/-- Total-degree preservation by the regular action boundary.

If a regular-coefficient chain in degree `n+1` belongs to total filtration stage `p`, its
action boundary belongs to the same stage `p` in degree `n`. -/
theorem envelopingActionBoundary_mem_filtration (p n : ℕ)
    {z : (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p (n + 1)) :
    coefficientActionBoundary R L (regularCoefficients R L) n z ∈
      envelopingFiltration R L p n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, v, u, hq, hu, rfl⟩ := hz
      rw [envelopingActionBoundary_apply_ιMulti_tmul]
      apply (envelopingFiltration R L p n).sum_mem
      intro i hi
      apply (envelopingFiltration R L p n).smul_mem
      apply ιMulti_tmul_mem_envelopingFiltration R L p n (q + 1)
        (v ∘ i.succAbove) (u * UniversalEnvelopingAlgebra.ι R (v i)) (by omega)
      exact UniversalEnvelopingAlgebra.mul_mem_degreeFiltration R L hu
        (UniversalEnvelopingAlgebra.ι_mem_degreeFiltration R L (v i))
  | zero =>
      rw [map_zero]
      exact (envelopingFiltration R L p n).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (envelopingFiltration R L p n).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (envelopingFiltration R L p n).smul_mem r ih

/-- The filtered enveloping Chevalley–Eilenberg differential.

The coefficient differential sends total filtration stage `p` in degree `n+1` into total
filtration stage `p` in degree `n`. -/
theorem envelopingDifferential_mem_filtration (p n : ℕ)
    {z : (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p (n + 1)) :
    coefficientDifferential R L (regularCoefficients R L) n z ∈
      envelopingFiltration R L p n := by
  rw [coefficientDifferential_eq_bracket_add_action, LinearMap.add_apply]
  exact (envelopingFiltration R L p n).add_mem
    (envelopingFiltration_mono R L n (Nat.sub_le p 1)
      (envelopingBracketBoundary_mem_lowerFiltration R L p n hz))
    (envelopingActionBoundary_mem_filtration R L p n hz)

/-- The leading regular-action term of the enveloping differential.

For a chain in filtration stage `p`, subtracting its action boundary from its full
differential gives an element of stage `p-1` in the target degree. -/
theorem envelopingDifferential_sub_action_mem_lowerFiltration (p n : ℕ)
    {z : (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p (n + 1)) :
    coefficientDifferential R L (regularCoefficients R L) n z -
      coefficientActionBoundary R L (regularCoefficients R L) n z ∈
        envelopingFiltration R L (p - 1) n := by
  have heq : coefficientDifferential R L (regularCoefficients R L) n z -
      coefficientActionBoundary R L (regularCoefficients R L) n z =
        (differential R L n).rTensor (regularCoefficients R L) z := by
    rw [coefficientDifferential_eq_bracket_add_action, LinearMap.add_apply]
    exact sub_eq_iff_eq_add.mpr rfl
  rw [heq]
  exact envelopingBracketBoundary_mem_lowerFiltration R L p n hz

end ChevalleyEilenberg
