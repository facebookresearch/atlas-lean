/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BinomialReplication
import Mathlib.Tactic.NormNum

/-!
# Tests for binomial-tree replication

* The two-period call example of the Rutgers 640:495 notes (`S₀ = 100`, `u = 1.1`, `d = 0.9`,
  `R = 1.02`, strike `97`): root value `8000/867`, first hedge ratio `35/51`, and replicated payoff
  `24` after two up moves.
* A path-dependent claim paying `1` only after an up move followed by a down move: the wealth is `1`
  on that history and `0` after down-then-up, which reaches the same stock price.
* Horizon zero.
-/

@[expose] public section

open MathlibExt.Probability.Finance.BinomialReplication

namespace MathlibExtTest.Probability.Finance.BinomialReplication

theorem claimValue_call_test :
    claimValue (11 / 10) (9 / 10) (102 / 100)
        (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) 2 [] =
      8000 / 867 := by
  simp only [claimValue, rnProb, price]
  norm_num

theorem hedgeRatio_call_test :
    hedgeRatio 100 (11 / 10) (9 / 10) (102 / 100)
        (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) 2 [] =
      35 / 51 := by
  simp only [hedgeRatio, show List.length ([] : List Bool) = 0 from rfl,
    show (2 : ℕ) - 0 - 1 = 0 + 1 from rfl, claimValue, rnProb, price]
  norm_num

theorem wealth_upup_test :
    wealth 100 (11 / 10) (9 / 10) (102 / 100)
        (claimValue (11 / 10) (9 / 10) (102 / 100)
          (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) 2 [])
        (hedgeRatio 100 (11 / 10) (9 / 10) (102 / 100)
          (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) 2)
        [true, true] = 24 := by
  have h := wealth_hedgeRatio_replicates (S₀ := 100) (u := 11 / 10) (d := 9 / 10)
    (R := 102 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) 2 [true, true] rfl
  have hpay : (fun s => max (price 100 (11 / 10) (9 / 10) s - 97) 0) [true, true] = 24 := by
    simp only [price]
    norm_num
  exact h.trans hpay

theorem wealth_updown_test :
    wealth 100 (11 / 10) (9 / 10) (102 / 100)
        (claimValue (11 / 10) (9 / 10) (102 / 100)
          (fun s => if s = [false, true] then (1 : ℝ) else 0) 2 [])
        (hedgeRatio 100 (11 / 10) (9 / 10) (102 / 100)
          (fun s => if s = [false, true] then (1 : ℝ) else 0) 2)
        [false, true] = 1 := by
  have h := wealth_hedgeRatio_replicates (S₀ := 100) (u := 11 / 10) (d := 9 / 10)
    (R := 102 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => if s = [false, true] then (1 : ℝ) else 0) 2 [false, true] rfl
  rw [h]
  simp

theorem wealth_downup_test :
    wealth 100 (11 / 10) (9 / 10) (102 / 100)
        (claimValue (11 / 10) (9 / 10) (102 / 100)
          (fun s => if s = [false, true] then (1 : ℝ) else 0) 2 [])
        (hedgeRatio 100 (11 / 10) (9 / 10) (102 / 100)
          (fun s => if s = [false, true] then (1 : ℝ) else 0) 2)
        [true, false] = 0 := by
  have h := wealth_hedgeRatio_replicates (S₀ := 100) (u := 11 / 10) (d := 9 / 10)
    (R := 102 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s => if s = [false, true] then (1 : ℝ) else 0) 2 [true, false] rfl
  rw [h]
  simp

theorem wealth_horizon_zero_test {S₀ u d R : ℝ} (_hS₀ : S₀ ≠ 0) (_hu : u ≠ 0) (_hd : d ≠ 0)
    (_hud : u ≠ d) (_hR : R ≠ 0) (V : List Bool → ℝ) :
    wealth S₀ u d R (claimValue u d R V 0 []) (hedgeRatio S₀ u d R V 0) [] = V [] := by
  simp only [wealth, claimValue]

end MathlibExtTest.Probability.Finance.BinomialReplication
