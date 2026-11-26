/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEqRoundInvRemainderAdd

open MetaMathlibExt
open Filter Topology

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEqRoundInvRemainderAdd

-- With β = 0 the largeness hypothesis is automatic since aₙ ≥ 1 > 8/9.
example {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - 0| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) (n : ℕ) :
    (a n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + 0 + 1 / 2⌋ := by
  have h := (eq_round_inv_remainder_add (β := 0) le_rfl hpos hratio hsum).1 n
  apply h
  have h1 : 1 ≤ a n := hpos n
  have ha : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast h1
  calc (8 * (0 + 1 / 3) ^ 2 : ℝ) = 8 / 9 := by norm_num
    _ ≤ 1 := by norm_num
    _ ≤ (a n : ℝ) := ha

example {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - 0| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r)
    (hlim : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + 0 - a n|) atTop (𝓝 0) :=
  (eq_round_inv_remainder_add (β := 0) le_rfl hpos hratio hsum).2 hlim

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEqRoundInvRemainderAdd
