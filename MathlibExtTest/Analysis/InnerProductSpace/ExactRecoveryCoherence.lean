/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherence

/-! # Tests for `MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherence` -/

open MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition
open MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCoherenceWanted
open scoped InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.ExactRecoveryCoherence

-- Test section: an orthonormal dictionary has coherence `μ = 0`, so `(2m - 1) μ = 0 < 1` and the
-- Exact Recovery Condition holds for every finite support, over `ℝ` or `ℂ`.
example {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (D : ι → E)
    (hD : Orthonormal 𝕜 D) (Λ : Finset ι) {ω : ι} (hω : ω ∉ Λ) :
    ∃ a : Λ → 𝕜,
      ∑ i, a i • D i = (Submodule.span 𝕜 (Set.range fun i : Λ => D i)).starProjection (D ω) ∧
        ∑ i, ‖a i‖ < 1 :=
  exists_erc_of_coherence D hD.1 (μ := 0) (fun _ _ hij => by simp [hD.2 hij]) Λ (by simp) hω

-- Test section: the empty support. The hypothesis reads `-μ < 1`, and the only coefficient
-- vector is empty.
example {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : κ → E)
    (hD : ∀ i, ‖D i‖ = 1) (hμ : ∀ i j, i ≠ j → ‖⟪D i, D j⟫_ℂ‖ ≤ 1 / 2) (ω : κ) :
    ∃ a : (∅ : Finset κ) → ℂ,
      ∑ i, a i • D i =
          (Submodule.span ℂ (Set.range fun i : (∅ : Finset κ) => D i)).starProjection (D ω) ∧
        ∑ i, ‖a i‖ < 1 :=
  exists_erc_of_coherence D hD hμ ∅ (by norm_num) (Finset.notMem_empty ω)

-- Test section: coherence `μ = 1/4` allows supports of size `m = 2`, since `(2 · 2 - 1) / 4 < 1`.
example {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (D : κ → E)
    (hD : ∀ i, ‖D i‖ = 1) (hμ : ∀ i j, i ≠ j → ‖⟪D i, D j⟫_ℝ‖ ≤ 1 / 4) (Λ : Finset κ)
    (hΛ : Λ.card = 2) {ω : κ} (hω : ω ∉ Λ) :
    ∃ a : Λ → ℝ,
      ∑ i, a i • D i = (Submodule.span ℝ (Set.range fun i : Λ => D i)).starProjection (D ω) ∧
        ∑ i, ‖a i‖ < 1 :=
  exists_erc_of_coherence D hD hμ Λ (by rw [hΛ]; norm_num) hω

-- Test section: with the greedy selection step of `ExactRecoveryCondition`, coherence
-- `(2m - 1) μ < 1` makes every nonzero residual in the optimal span strictly more correlated with
-- some optimal atom than with any atom outside the support, so OMP selects an optimal atom.
example {𝕜 E κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (D : κ → E)
    (hD : ∀ i, ‖D i‖ = 1) {μ : ℝ} (hμ : ∀ i j, i ≠ j → ‖⟪D i, D j⟫_𝕜‖ ≤ μ) (Λ : Finset κ)
    [Nonempty Λ] (hm : (2 * (Λ.card : ℝ) - 1) * μ < 1) {ω : κ} (hω : ω ∉ Λ) {r : E}
    (hr : r ∈ Submodule.span 𝕜 (Set.range fun i : Λ => D i)) (hr0 : r ≠ 0) :
    ‖⟪D ω, r⟫_𝕜‖ < Finset.univ.sup' Finset.univ_nonempty (fun i : Λ => ‖⟪D i, r⟫_𝕜‖) := by
  obtain ⟨a, ha, herc⟩ := exists_erc_of_coherence D hD hμ Λ hm hω
  exact norm_inner_lt_sup'_of_erc (fun i : Λ => D i) (D ω) a ha herc hr hr0

-- Test section: the strict inequality `(2m - 1) μ < 1` cannot be relaxed. Two equal unit atoms
-- have coherence `μ = 1`; for the support `{0}` of size `m = 1`, `(2m - 1) μ = 1`, and the only
-- coefficient of the projection of the second atom is `1`, so `∑ᵢ |aᵢ| < 1` fails.
example : ¬ ∃ a : ({0} : Finset (Fin 2)) → ℝ,
    ∑ i, a i • (fun _ : Fin 2 => (1 : ℝ)) i =
        (Submodule.span ℝ (Set.range fun i : ({0} : Finset (Fin 2)) =>
          (fun _ : Fin 2 => (1 : ℝ)) i)).starProjection ((fun _ : Fin 2 => (1 : ℝ)) 1) ∧
      ∑ i, ‖a i‖ < 1 := by
  rintro ⟨a, ha, hlt⟩
  set i₀ : ({0} : Finset (Fin 2)) := ⟨0, Finset.mem_singleton_self 0⟩
  have hsum (f : ({0} : Finset (Fin 2)) → ℝ) : ∑ i, f i = f i₀ :=
    Fintype.sum_eq_single i₀ fun i hi =>
      absurd (Subtype.ext (Finset.mem_singleton.mp i.2)) hi
  have hmem : (1 : ℝ) ∈ Submodule.span ℝ (Set.range fun i : ({0} : Finset (Fin 2)) =>
      (fun _ : Fin 2 => (1 : ℝ)) i) := Submodule.subset_span ⟨i₀, rfl⟩
  rw [Submodule.starProjection_eq_self_iff.mpr hmem, hsum fun i => a i • (1 : ℝ),
    smul_eq_mul, mul_one] at ha
  rw [hsum, ha, norm_one] at hlt
  exact lt_irrefl 1 hlt

end MathlibExtTest.Analysis.InnerProductSpace.ExactRecoveryCoherence
