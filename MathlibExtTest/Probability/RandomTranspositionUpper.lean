/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RandomTranspositionUpper
import MathlibExt.Probability.GroupWalkTrace
import MathlibExt.Probability.RandomTranspositionRank
import MathlibExt.Probability.RandomTranspositionEstimates

open MathlibExt.Probability.MarkovMixing (tvDist)
open MathlibExt.Probability.RandomWalkFiniteGroup
open MathlibExt.Probability.RandomTranspositionFiltration
open MathlibExt.Probability.RandomTranspositionEstimates
open MathlibExt.Probability.RandomWalkFiniteGroupWanted (diaconis_shahshahani_upper)
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (convPow)

-- A prescribed positive window of w*n extra steps suffices for the corresponding TV error,
-- without requiring that n*log(n)/2 + w*n be an integer.
example : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero n], 10 ≤ n → ∀ w : ℝ, 0 < w →
    n * Real.log n / 2 + w * n ≤ k →
    tvDist (convPow (randomTransposition n) k) (uniform _) ≤ C * Real.exp (-2 * w) := by
  obtain ⟨b, hb, h⟩ := diaconis_shahshahani_upper
  refine ⟨b / 2, by positivity, ?_⟩
  intro n k _ hn w hw hk
  have hn' : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have htime : w ≤ ((k : ℝ) - n * Real.log n / 2) / n := (le_div_iff₀ hn').mpr (by linarith)
  have ht := h n k hn (hw.trans_le htime)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htime (by norm_num : (-2 : ℝ) ≤ 0))
  linarith [mul_le_mul_of_nonneg_left he hb.le]

-- A given transposition on three letters has two ordered endpoint pairs.
example : walkMatrix (randomTransposition 3) (Equiv.swap 0 1) 1 = 2 / 9 := by
  have h1 : (Equiv.swap (0 : Fin 3) 1) ≠ 1 := fun h => by
    simpa using congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) h
  have h2 : (Equiv.swap (0 : Fin 3) 1).IsSwap := ⟨0, 1, by decide, rfl⟩
  simp only [walkMatrix, inv_one, mul_one, randomTransposition, h1, h2, ite_false, ite_true]
  norm_num

-- With a deterministic group step, the new point is obtained by left multiplication.
example {G : Type*} [Group G] [DecidableEq G] (a b : G) :
    walkMatrix (fun g => if g = a then 1 else 0) (a * b) b = 1 := by
  simp [walkMatrix, mul_assoc]

-- The trace bound applies to the random-transposition walk.
example (n k : ℕ) [NeZero n] :
    4 * tvDist (convPow (randomTransposition n) k) (uniform _) ^ 2 ≤
      (walkMatrix (randomTransposition n) ^ (2 * k)).trace - 1 :=
  four_mul_tvDist_sq_le_trace_walkMatrix_pow _ (sum_randomTransposition n)
    (randomTransposition_inv n) k

-- On one position the single ordered pair is the diagonal pair: it acts as the identity.
example (i : Fin 3) (f : Equiv.Perm (Fin 3) → ℝ) (σ : Equiv.Perm (Fin 3)) :
    transSum {i} f σ = f σ := by
  simp [transSum, Equiv.swap_self, ← Equiv.Perm.one_def]

-- symSum over all positions sums over the whole group.
example (f : Equiv.Perm (Fin 3) → ℝ) (σ : Equiv.Perm (Fin 3)) :
    symSum Finset.univ f σ = ∑ τ, f τ := by
  rw [symSum_eq_sum_agree]
  simp

-- Coordinates of the level-2 symmetrisers on 4 letters: C(4,2) * 4^2.
example : Fintype.card (SymRankCoord 4 2) = 96 := by
  rw [card_symRankCoord]; rfl

-- Edge case j = 0: the kernel of symRankMap 0 is the mean-zero functions.
example (f : Equiv.Perm (Fin 3) → ℝ) :
    f ∈ (symRankMap 0).ker ↔ ∑ τ, f τ = 0 := by
  rw [mem_ker_symRankMap_iff (Nat.zero_le _)]
  constructor
  · intro h
    have := congrFun (h Finset.univ (by simp)) 1
    simpa [symSum_eq_sum_agree] using this
  · intro h R hR
    have hR' : R = Finset.univ := Finset.eq_univ_of_card R (by simpa using hR)
    subst hR'
    funext σ
    simpa [symSum_eq_sum_agree] using h

-- The deficit-one upper endpoint is 1 - 2/n.
example (n : ℕ) (hn : 2 ≤ n) : cap n 1 = 1 - 2 / n := by
  have hN : (0 : ℝ) < n := by positivity
  unfold cap
  rw [min_eq_left]
  · field_simp; ring
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [sub_le_sub_iff_left, div_le_div_iff₀ hN (pow_pos hN 2)]
    push_cast; nlinarith

-- oriented keeps nonnegative values and twists negative ones.
example : oriented 4 (1 / 3) = 1 / 3 := by norm_num [oriented]
example : oriented 4 (-(1 / 2)) = 1 := by norm_num [oriented]
