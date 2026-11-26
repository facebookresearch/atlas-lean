/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2Fourier
public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLMeanInfl

/-!
# Tests for the Fourier–Sobolev lever

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2Fourier`:

* `fs_lever` at `x = 1/2`, `y = 1`, `m = 3` (`3/8 ≤ 7/8`) and `fs_degree_to_undegree` at
  `u = 1/2`, `u' = 0`, `m = 2` (`1 ≤ 2`);
* `bkt2f_targetWeight_levelGe2`, `bkt2f_degreeWeight_le_undegree` and
  `bkt2f_FS_highDegree` at `p = 1/2`, `u = 3/4`, `u' = 1/2`, where the cap hypothesis
  `1 - u' ≤ 4p(1-p)` holds;
* `bkt2f_qnormPow_indicator` and `bkt2f_qnorm_indicator_sq` on the constant-true function
  (the `q`-norm is `1`), and `bkt2f_gap_vanishes_at_p_half`.

Window predicate: `bkt2f_meanInflResidue q` is refuted for every `q > 1/2`
(`bkt2f_meanInflResidue_refutable`, tested at `q = 1`). No chain is run from it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLLevel2Fourier

open Finset StatMech StatMech.OSSS StatMech.Probability

example : (3 : ℝ) * (1 / 2) ^ (3 - 1) * (1 - 1 / 2) ≤ 1 ^ 3 - (1 / 2) ^ 3 :=
  fs_lever (by norm_num) (by norm_num) 3

example : (3 : ℝ) * (1 / 2) ^ (3 - 1) * (1 - 1 / 2) = 3 / 8 := by norm_num

example : ((2 : ℕ) : ℝ) * (1 - 1 / 2) ^ (2 - 1) ≤ (1 - 0) ^ 2 / (1 / 2 - 0) :=
  fs_degree_to_undegree (by norm_num) (by norm_num) 2

example (φ : ConfigSpace (Fin 2) → Bool) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2), (1 - 1 / 2) ^ S.card
        * (ptn_coeff (1 / 2) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (ptn_qnorm (1 / 2) (1 + (1 - 1 / 2) / (4 * (1 / 2) * (1 - 1 / 2)))
          (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 :=
  bkt2f_targetWeight_levelGe2 (by norm_num) (by norm_num) φ (by norm_num) (by norm_num)
    (by norm_num) 2

example (φ : ConfigSpace (Fin 2) → Bool) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (1 - 3 / 4) ^ (S.card - 1)
          * (ptn_coeff (1 / 2) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 / (3 / 4 - 1 / 2)) * ∑ S ∈ univ.filter
          (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
          (1 - 1 / 2) ^ S.card * (ptn_coeff (1 / 2) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 :=
  bkt2f_degreeWeight_le_undegree (by norm_num) (by norm_num) φ 2

example (φ : ConfigSpace (Fin 2) → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (1 - 3 / 4) ^ (S.card - 1)
          * (ptn_coeff (1 / 2) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (3 / 4 - 1 / 2))
        * (ptn_qnorm (1 / 2) (1 + (1 - 1 / 2) / (4 * (1 / 2) * (1 - 1 / 2)))
            (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 :=
  bkt2f_FS_highDegree (by norm_num) (by norm_num) φ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 2

/-- `bkt2f_qnormPow_indicator` on the constant-true function: the `q`-th moment is `1`. -/
example {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ptn_qnormPow p 3 (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω
      then (1 : ℝ) else 0) = 1 := by
  rw [bkt2f_qnormPow_indicator (by norm_num), mil_constTrue_eq,
    OSSS.expect_one (OSSS.bernoulliWeight_isProbWeight hp0 hp1)]

/-- `bkt2f_qnorm_indicator_sq` on the constant-true function: the squared `q`-norm is `1`. -/
example {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (ptn_qnorm p (3 / 2) (fun ω => if (fun _ => true : ConfigSpace (Fin 2) → Bool) ω
      then (1 : ℝ) else 0)) ^ 2 = 1 := by
  rw [bkt2f_qnorm_indicator_sq hp0 hp1 (by norm_num), mil_constTrue_eq,
    OSSS.expect_one (OSSS.bernoulliWeight_isProbWeight hp0 hp1), Real.one_rpow]

example : (1 - (1 / 4 : ℝ)) ^ (3 - 1) - ((1 - 1 / 4) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (3 - 1)
    = 0 :=
  bkt2f_gap_vanishes_at_p_half 3

example : ¬ bkt2f_meanInflResidue 1 := bkt2f_meanInflResidue_refutable (by norm_num)

end StatMechTest.BooleanFunctions.BKKKLLevel2Fourier
