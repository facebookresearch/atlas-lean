/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MulticommodityFlowRapidMixing

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for the low-congestion flow from rapid mixing

On the two-state chain that moves to a uniformly random state at each step, the
hypotheses of Theorem 8 hold with `τ = 1`, and the theorem gives a flow whose load on
the edge `(0, 1)` is at most `16 · (1/2 · 1/2) = 4`. On the one-state chain the
hypotheses hold with `τ = 0`, and the theorem gives a flow of load at most `0`.
-/

set_option autoImplicit false

open Matrix
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.MarkovMixing
open MathlibExt.Probability.Flows MathlibExt.Probability.MulticommodityFlowWanted

namespace MathlibExtTest.Probability.MulticommodityFlowRapidMixing

/-- The two-state chain that moves to a uniformly random state at each step. -/
noncomputable def mixP₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- The uniform distribution on two states. -/
noncomputable def mixUnif : Fin 2 → ℝ := fun _ => 1 / 2

theorem mixUnif_pos : ∀ x, 0 < mixUnif x := fun _ => by norm_num [mixUnif]

theorem mixUnif_sum : ∑ x, mixUnif x = 1 := by norm_num [mixUnif, Fin.sum_univ_two]

theorem mixP₂_stoch : mixP₂ ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun _ _ => by norm_num [mixP₂], fun _ => by norm_num [mixP₂, Fin.sum_univ_two]⟩

theorem mixP₂_rev : ∀ x y, mixUnif x * mixP₂ x y = mixUnif y * mixP₂ y x := by
  intro x y; norm_num [mixP₂, mixUnif]

theorem mixP₂_mul_self : mixP₂ * mixP₂ = mixP₂ := by
  ext i j; norm_num [mixP₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem mixP₂_pow : ∀ t, 1 ≤ t → mixP₂ ^ t = mixP₂ := by
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [pow_succ, ih hn, mixP₂_mul_self]

theorem mixP₂_mixed : ∀ x t, 1 ≤ t → tvDist (fun y => (mixP₂ ^ t) x y) mixUnif ≤ 1 / 4 := by
  intro x t ht
  rw [mixP₂_pow t ht]
  norm_num [tvDist, mixP₂, mixUnif]

/-- Theorem 8 on the two-state chain, with `τ = 1`. -/
example : ∃ F : MulticommodityFlow mixUnif mixP₂,
    ∀ u v, F.load u v ≤ 16 * (1 : ℕ) * (mixUnif u * mixP₂ u v) :=
  exists_multicommodityFlow_load_le_sixteen_mul mixUnif_pos mixUnif_sum mixP₂_stoch
    mixP₂_rev (fun x t ht => mixP₂_mixed x t ht)

/-- The load bound on the edge `(0, 1)` of the two-state chain is at most `4`. -/
example : ∃ F : MulticommodityFlow mixUnif mixP₂, F.load 0 1 ≤ 4 := by
  obtain ⟨F, hF⟩ := exists_multicommodityFlow_load_le_sixteen_mul mixUnif_pos mixUnif_sum
    mixP₂_stoch mixP₂_rev (fun x t ht => mixP₂_mixed x t ht)
  exact ⟨F, by
    have h := hF 0 1
    norm_num [mixUnif, mixP₂] at h ⊢
    exact h⟩

/-- The one-state chain with the constant transition matrix. -/
noncomputable def oneP : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The point mass on the single state. -/
noncomputable def onePi : Fin 1 → ℝ := fun _ => 1

theorem oneP_stoch : oneP ∈ rowStochastic ℝ (Fin 1) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun _ _ => by norm_num [oneP], fun _ => by norm_num [oneP, Fin.sum_univ_one]⟩

theorem oneP_rev : ∀ x y, onePi x * oneP x y = onePi y * oneP y x := by
  intro x y
  fin_cases x
  fin_cases y
  norm_num [oneP, onePi]

theorem oneP_pow : ∀ t, oneP ^ t = oneP := by
  intro t
  induction t with
  | zero =>
    ext i j
    fin_cases i
    fin_cases j
    simp [oneP]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i
    fin_cases j
    simp [oneP, Matrix.mul_apply]

theorem oneP_mixed : ∀ x t, 0 ≤ t →
    tvDist (fun y => (oneP ^ t) x y) onePi ≤ 1 / 4 := by
  intro x t _
  fin_cases x
  rw [oneP_pow]
  norm_num [tvDist, oneP, onePi, Fin.sum_univ_one]

/-- Theorem 8 on the one-state chain, with `τ = 0`: the load bound is `0`. -/
example : ∃ F : MulticommodityFlow onePi oneP,
    ∀ u v, F.load u v ≤ 16 * (0 : ℕ) * (onePi u * oneP u v) :=
  exists_multicommodityFlow_load_le_sixteen_mul (fun _ => by norm_num [onePi])
    (by norm_num [onePi, Fin.sum_univ_one]) oneP_stoch oneP_rev
    (fun x t ht => oneP_mixed x t (Nat.zero_le _))

end MathlibExtTest.Probability.MulticommodityFlowRapidMixing
