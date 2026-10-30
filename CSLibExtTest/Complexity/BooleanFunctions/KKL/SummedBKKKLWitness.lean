/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.SummedBKKKLWitness
public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for the summed BKKKL inequality

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.SummedBKKKLWitness`:

* the two-bit OR data at `p = 9/10`: squared Fourier coefficients, influences
  (`sbk_OR_totalInfl`, `sbk_OR_maxInfl`), and the summed inequality
  `sbk_summed_holds_at_OR` restated numerically as `99/2500 ≤ (1/10)^(1/3) · 1/5`;
* `sbk_summed_half` on the one-variable dictator at `u = 1/2` (`1 ≤ 1`);
* the refutations `sbk_pBiasedMaster_false`, `sbk_lowDegreeMasterResidue_false` and
  `sbk_summed_survives_percoord_fails` at `q = 1`;
* `sbk_engine_integral_eq` at `n = 1`, `s = 1/2` (value `1/4`),
  `sbk_engine_integral_damped`, and `bkt2c_gap_vanishes_at_p_half`.

Conditional statements: `sbk_openResidue_of_lowDegree` and `sbk_kesten_of_lowDegree` assume
`bkt_lowDegreeMasterResidue q`, which fails for `q > 9/10` and is proved for no `q > 1/2`.
`sbk_openResidue_of_lowDegree` is run on the empty window `q = 1/2`. `sbk_kesten_of_lowDegree`
also needs a point `p ∈ (1/2, q)`, so it has no instance available here and is not tested.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.SummedBKKKLWitness

open Finset StatMech StatMech.OSSS StatMech.Probability

example : (ptn_coeff (9 / 10 : ℝ) ctp_f {0}) ^ 2 + (ptn_coeff (9 / 10 : ℝ) ctp_f {1}) ^ 2
    + (ptn_coeff (9 / 10 : ℝ) ctp_f ({0, 1} : Finset (Fin 2))) ^ 2 = 99 / 10000 := by
  rw [sbk_coeff0_sq, sbk_coeff1_sq, sbk_coeff01_sq]; norm_num

example : totalInfl (OSSS.bernoulliWeight (9 / 10 : ℝ)) ctp_f
    = 2 * maxInfl (OSSS.bernoulliWeight (9 / 10 : ℝ)) ctp_f := by
  rw [sbk_OR_totalInfl, sbk_OR_maxInfl]; norm_num

/-- `sbk_summed_holds_at_OR` in numbers. -/
example : (99 : ℝ) / 2500 ≤ ((1 : ℝ) / 10) ^ ((1 : ℝ) / 3) * (1 / 5) := by
  have h := sbk_summed_holds_at_OR
  rwa [sbk_OR_summed_lhs, sbk_OR_maxInfl, sbk_OR_totalInfl,
    show (1 / 2 : ℝ) / (2 - 1 / 2) = 1 / 3 by norm_num] at h

example : (Finset.univ : Finset (Finset (Fin 2))).card = 4 := by rw [sbk_univ_fin2]; decide

/-- `sbk_summed_half` on the dictator at `u = 1/2`: `4σ_{1/2}² = 1 ≤ 1`. -/
example : (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
      * (ptn_coeff (1 / 2 : ℝ)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) S) ^ 2) ≤ 1 := by
  have h := sbk_summed_half (fun ω : ConfigSpace (Fin 1) => ω 0) (u := 1 / 2)
    (by norm_num) (by norm_num)
  rwa [vgp_dictator_maxInfl (by norm_num) (by norm_num), Real.one_rpow,
    vgp_dictator_totalInfl (by norm_num) (by norm_num), one_mul] at h

example : ¬ pro_PBiasedMaster 1 := sbk_pBiasedMaster_false (by norm_num)
example : ¬ bkt_lowDegreeMasterResidue 1 := sbk_lowDegreeMasterResidue_false (by norm_num)
example : ¬ mfp2_PerCoordHighNoise 1 := (sbk_summed_survives_percoord_fails (by norm_num)).1

example : (∫ v in (1 - (1 / 2 : ℝ))..(1 : ℝ), ((1 : ℕ) + 1 : ℝ) * (1 - v) ^ 1) = 1 / 4 := by
  rw [sbk_engine_integral_eq 1]; norm_num

example : (∫ v in (1 - (1 / 2 : ℝ))..(1 : ℝ), ((3 : ℕ) : ℝ) * (1 - v) ^ (3 - 1)) < 1 :=
  sbk_engine_integral_damped (by norm_num) (by norm_num) (by norm_num)

example : (1 - (1 / 3 : ℝ)) ^ (2 - 1) - ((1 - 1 / 3) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (2 - 1)
    = 0 :=
  bkt2c_gap_vanishes_at_p_half 2

/-- `bkt_lowDegreeMasterResidue q` holds vacuously for `q ≤ 1/2`. -/
lemma lowDegree_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : bkt_lowDegreeMasterResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : frh_openResidue (1 / 2) := sbk_openResidue_of_lowDegree (lowDegree_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.SummedBKKKLWitness
