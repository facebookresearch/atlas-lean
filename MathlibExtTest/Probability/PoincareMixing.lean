/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PoincareMixing
public import MathlibExt.Probability.CanonicalPaths

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for mixing from a Poincaré inequality

`K` is the two-state chain with all transition probabilities `1/2`; its lazy version
`P = (I + K)/2` stays with probability `3/4`. Direct canonical paths give the Poincaré inequality
for `P` with `B = 2` (Sinclair's Theorem 5 route), so the theorem gives
`(2 d_TV(Pᵗ(x, ·), π))² ≤ (1/2)ᵗ`, and `P` is `1/4`-mixed at `t = 2`. (The true distance is
`(1/2)^(t+1)`.) This exercises every hypothesis together.
-/

set_option autoImplicit false

open Matrix
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.MarkovMixing
open MathlibExt.Probability.PoincareMixing

namespace MathlibExtTest.Probability.PoincareMixing

/-- Move to a uniformly random state. -/
noncomputable def K₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- The uniform distribution on two states. -/
noncomputable def unif : Fin 2 → ℝ := fun _ => 1 / 2

theorem unif_pos : ∀ x, 0 < unif x := fun _ => by norm_num [unif]

theorem unif_sum : ∑ x, unif x = 1 := by norm_num [unif, Fin.sum_univ_two]

theorem K₂_stoch : K₂ ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  exact ⟨fun _ _ => by norm_num [K₂], fun _ => by norm_num [K₂, Fin.sum_univ_two]⟩

theorem K₂_rev : ∀ x y, unif x * K₂ x y = unif y * K₂ y x := by
  intro x y; norm_num [K₂, unif]

theorem lazy_apply (x y : Fin 2) :
    ((1 / 2 : ℝ) • (1 + K₂)) x y = if x = y then 3 / 4 else 1 / 4 := by
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num [K₂]

theorem poincare_lazy : ∀ ψ : Fin 2 → ℝ, ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (unif x * unif y) ≤
    2 * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (unif x * ((1 / 2 : ℝ) • (1 + K₂)) x y) :=
  sum_sq_sub_mul_le_of_elongatedPathLoad_le (fun x => (unif_pos x).le) _ (fun _ y => [y])
    (fun _ _ _ => rfl) (by
      intro u v
      rw [lazy_apply]
      fin_cases u <;> fin_cases v <;>
        norm_num [elongatedPathLoad, pathEdges, unif, Fin.sum_univ_two])

/-- The `L²` contraction on the mean-zero function `(1, -1)`: `1/4 ≤ (1/2) · 1`. -/
example : ∑ x, unif x * (((1 / 2 : ℝ) • (1 + K₂)) *ᵥ ![1, -1]) x ^ 2 ≤
    (1 - 1 / 2) * ∑ x, unif x * (![1, -1] : Fin 2 → ℝ) x ^ 2 :=
  sum_mul_sq_mulVec_le_of_poincare unif_pos unif_sum K₂_stoch K₂_rev (by norm_num)
    poincare_lazy (by norm_num [unif, Fin.sum_univ_two])

/-- The total-variation bound at every time. -/
example (x : Fin 2) (t : ℕ) :
    (2 * tvDist (fun y => (((1 / 2 : ℝ) • (1 + K₂)) ^ t) x y) unif) ^ 2 ≤
      (1 - 1 / 2) ^ t * (1 / unif x - 1) :=
  sq_two_mul_tvDist_pow_le unif_pos unif_sum K₂_stoch K₂_rev (by norm_num) poincare_lazy x t

/-- The lazy chain is `1/4`-mixed at time `2`. -/
example : IsMixedAt ((1 / 2 : ℝ) • (1 + K₂)) unif 2 :=
  isMixedAt_of_poincare unif_pos unif_sum K₂_stoch K₂_rev (by norm_num) poincare_lazy
    (fun x => by norm_num [unif])

end MathlibExtTest.Probability.PoincareMixing
