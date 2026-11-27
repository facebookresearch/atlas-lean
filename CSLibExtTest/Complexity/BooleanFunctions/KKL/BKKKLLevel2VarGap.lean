/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2VarGap
public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for level-two mass versus variance

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2VarGap`:

* `bkt2p_undegree_le_var`, `bkt2p_levelGe2_le_var` and `bkt2p_levelGe2_le_var_and_mil` on a
  general two-variable function at `u = 1/2`, `u' = 1/4`, `k = 2`, and
  `bkt2p_levelGe2_le_var` on the one-variable dictator, where the right side is
  `16 p(1-p)`;
* `bkt2c_gap_vanishes_at_p_half` (the weight gap at `p = 1/2`).

Window predicate: `bkt2p_VarGapCore q` is refuted for every `q > 1/2`
(`vgp_varGapCore_refutable`, tested at `q = 1`). No chain is run from it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLLevel2VarGap

open Finset StatMech StatMech.OSSS StatMech.Probability

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (1 - 1 / 4) ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt2p_undegree_le_var hp0 hp1 φ (by norm_num) (by norm_num) 2

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    (4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (1 / 2 - 1 / 4))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))))
    ∧ (4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * ((2 : ℕ) : ℝ)
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) :=
  bkt2p_levelGe2_le_var_and_mil hp0 hp1 φ (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2

/-- `bkt2p_levelGe2_le_var` on the dictator: the bound is `4 / (1/2 - 1/4) · p(1-p)`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0)
            S) ^ 2
      ≤ 16 * (p * (1 - p)) := by
  have h := bkt2p_levelGe2_le_var hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (u' := 1 / 4) (by norm_num) (by norm_num) (by norm_num) 2
  rw [vgp_dictator_meanVar hp0 hp1] at h
  norm_num at h ⊢
  linarith

example : (1 - (1 / 5 : ℝ)) ^ (2 - 1) - ((1 - 1 / 5) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (2 - 1)
    = 0 :=
  bkt2c_gap_vanishes_at_p_half 2

example : ¬ bkt2p_VarGapCore 1 := vgp_varGapCore_refutable (by norm_num)

end StatMechTest.BooleanFunctions.BKKKLLevel2VarGap
