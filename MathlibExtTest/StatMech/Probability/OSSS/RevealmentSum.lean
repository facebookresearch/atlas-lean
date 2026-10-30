/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.RevealmentSum
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.RevealmentSum`

* `sum_reindex_le_card_smul`, `sum_translate_le`, `sum_translate_le_range` for the constant
  function `1` at `n = 2`, `r = 1`.
* `revealment_sum_bound` and `revealment_family_sum_le` on a one-point index set.
-/

@[expose] public section

open StatMech.OSSS

namespace MathlibExtTest.StatMech.Probability.OSSS.RevealmentSum

example : ∑ _k ∈ Finset.Icc 1 2, (1 : ℝ) ≤ 2 * ∑ _j ∈ Finset.range (2 + 1), (1 : ℝ) :=
  sum_translate_le 2 1 (by norm_num) (fun _ => 1) (fun _ => zero_le_one)

example : ∑ _k ∈ Finset.Icc 1 2, (1 : ℝ) ≤ 2 * ∑ _j ∈ Finset.range 2, (1 : ℝ) :=
  sum_translate_le_range 2 1 le_rfl (by norm_num) (fun _ => 1) (fun _ => zero_le_one)

example : ∑ _a ∈ Finset.range 4, (1 : ℝ) ≤ ((2 : ℕ) : ℝ) * ∑ _b ∈ Finset.range 2, (1 : ℝ) :=
  sum_reindex_le_card_smul (Finset.range 4) (fun a => a / 2) (fun _ => 1) (fun _ => zero_le_one)
    (Finset.range 2) (fun a ha => by simp at ha ⊢; omega) 2 (fun b hb => by
      simp only [Finset.mem_range] at hb
      interval_cases b <;> decide)

example : ∑ k ∈ Finset.Icc 1 2, (fun _ : ℕ => (1 : ℝ)) k
    ≤ 2 * ({()} : Finset Unit).sup' (by simp) (fun _ => ∑ _j ∈ Finset.range (2 + 1), (1 : ℝ)) :=
  revealment_sum_bound {()} (by simp) (fun _ _ => 1) (fun _ _ => zero_le_one) 2 1 (by norm_num)
    () (by simp) _ (fun _ => le_rfl)

example : ∑ k ∈ Finset.Icc 1 2, ((fun _ : ℕ => (1 : ℝ)) k + (fun _ : ℕ => (1 : ℝ)) k)
    ≤ 4 * ({()} : Finset Unit).sup' (by simp) (fun _ => ∑ _j ∈ Finset.range (2 + 1), (1 : ℝ)) :=
  revealment_family_sum_le {()} (by simp) (fun _ _ => 1) (fun _ _ => zero_le_one) 2 1 1
    (by norm_num) (by norm_num) () () (by simp) (by simp) _ _ (fun _ => le_rfl) (fun _ => le_rfl)

end MathlibExtTest.StatMech.Probability.OSSS.RevealmentSum
