/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeWitness

/-!
# Tests for the two-bit OR witness

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeWitness`:

* `ctp_cfg`, `ctp_OR` and `ctp_f` at small inputs (`decide`, `simp`);
* `ctp_expect_fin2` at the OR indicator: `E_p[OR] = 1 - (1 - p)²`;
* the exact witness numbers at `p = 9/10`: `Inf₀(OR) = 1/10` (`ctp_OR_infl0`), the per-coordinate
  left side `11/200` (`ctp_OR_lhs_eq`), which exceeds `(1/10)^(4/3)` (`ctp_rhs_lt_lhs`);
* `ctp_perCoordHighNoise_false` at `q = 1`, and the reduction
  `mfp2_PerCoordHighNoise q → frh_openResidue q` from
  `ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid`;
* `ctp_engine_holds_at_witness` (the capped estimate at the witness, at the correct noise level);
* `ctp_half_holds_but_window_fails`: its `p = 1/2` half applied to OR at `u = 1/2`, `e = 0`.

`mfp2_PerCoordHighNoise q` is a window statement over `p ∈ (1/2, q)`; it holds for `q ≤ 1/2`
only because the window is empty (recorded below), fails for `q > 9/10`, and is neither proved
nor refuted for `q ∈ (1/2, 9/10]`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.CoupledTensorizeWitness

open StatMech StatMech.OSSS StatMech.Probability

example : ctp_cfg true false 0 = true ∧ ctp_cfg true false 1 = false := ⟨rfl, rfl⟩

example : ctp_OR (ctp_cfg false false) = false := by decide
example : ctp_OR (ctp_cfg false true) = true := by decide
example : ctp_OR (ctp_cfg true true) = true := by decide

example : ctp_f (ctp_cfg false false) = 0 ∧ ctp_f (ctp_cfg true false) = 1 := by simp

example (p : ℝ) : expect (bernoulliWeight p) ctp_f = 1 - (1 - p) ^ 2 := by
  rw [ctp_expect_fin2]; simp; ring

example : infl (bernoulliWeight (9 / 10 : ℝ)) ctp_f 0 = 1 / 10 := ctp_OR_infl0

example :
    ((1 : ℝ) / 10) ^ ((4 : ℝ) / 3)
      < ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S),
          (1 - (1 / 2 : ℝ)) ^ (S.erase 0).card
            * (ptn_coeff (9 / 10 : ℝ) ctp_f S / ptn_sigma (9 / 10)) ^ 2 := by
  rw [ctp_OR_lhs_eq]; exact ctp_rhs_lt_lhs

example : ¬ mfp2_PerCoordHighNoise 1 := ctp_perCoordHighNoise_false (by norm_num)

example (H : mfp2_PerCoordHighNoise 1) : frh_openResidue 1 :=
  (ctp_perCoordHighNoise_unsatisfiable_but_reduction_valid (by norm_num)).2 H

/-- `mfp2_PerCoordHighNoise q` for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma mfp2_perCoordHighNoise_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : mfp2_PerCoordHighNoise q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : frh_openResidue (1 / 2) :=
  mfp2_openResidue_of_perCoordHighNoise (mfp2_perCoordHighNoise_of_le_half le_rfl)

example :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S),
        (Real.sqrt ((3 / 2 - 1) * 4 * (9 / 10) * (1 - 9 / 10)) ^ (S.erase 0).card) ^ 2
          * (ptn_coeff (9 / 10 : ℝ) (fun ω => if ctp_OR ω then (1 : ℝ) else 0) S
              / ptn_sigma (9 / 10)) ^ 2)
      ≤ (infl (bernoulliWeight (9 / 10 : ℝ))
          (fun ω => if ctp_OR ω then (1 : ℝ) else 0) 0) ^ (2 / (3 / 2 : ℝ)) :=
  ctp_engine_holds_at_witness

example :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S),
        (1 - (1 / 2 : ℝ)) ^ (S.erase 0).card
          * (ptn_coeff (1 / 2 : ℝ) (fun ω => if ctp_OR ω then (1 : ℝ) else 0) S
            / ptn_sigma (1 / 2)) ^ 2)
      ≤ (infl (bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if ctp_OR ω then (1 : ℝ) else 0) 0) ^ (2 / (2 - (1 / 2 : ℝ))) :=
  (ctp_half_holds_but_window_fails (q := 1) (by norm_num)).1 ctp_OR (1 / 2) (by norm_num)
    (by norm_num) 0

end StatMechTest.BooleanFunctions.CoupledTensorizeWitness
