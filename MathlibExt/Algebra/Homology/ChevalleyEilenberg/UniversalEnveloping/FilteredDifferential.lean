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
# Total-degree preservation by the enveloping Chevalley–Eilenberg differential

The regular-coefficient differential separates into bracket and action
summands. Negative right regular Lie coefficients give positive right
multiplication with zero-based sign `(-1)^i`. The action preserves total
enveloping-plus-exterior degree, while the bracket lowers it by one.
Modulo the previous filtration stage, the differential is its action summand.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The existing signed native action on the regular coefficients is
positive right multiplication in every exterior degree. -/
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

/-- The original differential has its bracket summand and the
positive right-regular coefficient summands; no differential is supplied. -/
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

/-- The bracket summand lowers total degree by one. -/
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

/-- The coefficient action preserves the total filtration. -/
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

/-- The coefficient CE differential preserves the total-degree
filtration on its original enveloping coefficients. -/
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

/-- Modulo the previous total-degree stage, the original differential is
exactly its right-regular action summand. -/
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
