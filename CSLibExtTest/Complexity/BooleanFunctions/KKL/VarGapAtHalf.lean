/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapAtHalf
public import CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedKKLTwoBit
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC

/-!
# Tests for degree weights and the KKL log-gain at `p = 1/2`

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.VarGapAtHalf`, mostly at the `AND` function
on `{0, 1}^Bool`, whose variance at `p = 1/2` is `3/16`, maximal influence `1/2` and total
influence `1`:

* `vgp2_degWeight_eq_half` at `AND`: the degree-weighted Fourier mass is the total influence `1`;
* `vgp2_master_half` at `AND`, `u = 1`: `2 · 1/16 · 4 ≤ (1/2)^1 · 1`;
* the headline `vgp2_kkl_logGain_half` at `AND`: `2 · 3/16 · log 2 ≤ 1`, and
  `vgp2_var_le_half` at `AND` (its hypotheses `0 < maxInfl < 1` hold): `3/16 ≤ 1 / (2 log 2)`;
* `vgp2_logGain_flex` on a one-point index type with `δ = 1/2` and `B = 8`, where the master
  hypothesis holds for every `u ∈ [0, 1]` because `(1/2)^{u/(2-u)} ≥ 1/2`;
* `vgp2_kkl_logGain_of_master` takes `frh_openResidue q`, which this library proves for no
  `q > 1/2` (for `q ≤ 1/2` the window `(1/2, q)` is empty, so the theorem has no instance).
  The test records what the hypothesis would give at `AND`: `2p²(1-p²) log(1/p) ≤ 2p`, which is
  true for every `p ∈ (0, 1)` (`pbkt_twoBit_atom_numeric`), so `AND` is no counterexample.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- `E(1 - E)` of the `AND` indicator at `p = 1/2` is its variance `3/16`. -/
lemma vgp2t_expect_mul_andInd :
    expect νHalf andInd * (1 - expect νHalf andInd) = 3 / 16 := by
  rw [← kkl_var_indicator_eq, var_andFun]

example : (∑ S : Finset Bool, 4 * (S.card : ℝ) * (ptn_coeff (1 / 2 : ℝ) andInd S) ^ 2) = 1 := by
  rw [vgp2_degWeight_eq_half andFun]; exact totalInfl_andInd

/-- `vgp2_master_half` at `AND` and `u = 1`. -/
example : 8 * (1 / 2 : ℝ) ^ 3 * (1 - 1 / 2) ≤ 1 / 2 * 1 := by
  have h := vgp2_master_half andFun (u := 1) zero_le_one le_rfl
  rw [cappedSum_andInd (by norm_num) (by norm_num), vgp2_degWeight_eq_half andFun,
    maxInfl_andInd, totalInfl_andInd] at h
  norm_num at h ⊢

/-- `vgp2_kkl_logGain_half` at `AND`: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16 : ℝ) * Real.log 2 ≤ 1 := by
  have h := vgp2_kkl_logGain_half andFun
  rw [vgp2t_expect_mul_andInd, maxInfl_andInd, totalInfl_andInd] at h
  norm_num at h ⊢
  linarith

/-- `vgp2_var_le_half` at `AND`; both hypotheses on the maximal influence hold. -/
example : (3 / 16 : ℝ) ≤ 1 / (2 * Real.log 2) := by
  have h := vgp2_var_le_half andFun (by rw [maxInfl_andInd]; norm_num)
    (by rw [maxInfl_andInd]; norm_num)
  rw [vgp2t_expect_mul_andInd, maxInfl_andInd, totalInfl_andInd] at h
  norm_num at h ⊢
  exact h

/-- `vgp2_logGain_flex` with one index of degree `1`, weight `1`, `δ = 1/2`, `B = 8`. -/
example : 2 * (∑ _i ∈ Finset.univ.filter (fun _ : Unit => (1 : ℕ) ≠ 0), (1 : ℝ))
    * Real.log (1 / (1 / 2)) ≤ 8 := by
  refine vgp2_logGain_flex (κ := Unit) (d := fun _ => 1) (c := fun _ => 1) (fun _ => zero_le_one)
    (by norm_num) (by norm_num) (fun u hu0 hu1 => ?_)
  have hexp : u / (2 - u) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hpow : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (u / (2 - u)) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp
  rw [Real.rpow_one] at hpow
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, Nat.sub_self, pow_zero]
  linarith

/-- What `frh_openResidue q` would give at `AND` through `vgp2_kkl_logGain_of_master`. -/
example {q : ℝ} (H : frh_openResidue q) {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    2 * (p ^ 2 * (1 - p ^ 2)) * Real.log (1 / p) ≤ 2 * p := by
  have h := vgp2_kkl_logGain_of_master H hp hp1 andFun
  rw [← kkl_var_indicator_eq, var_andInd, maxInfl_andInd_p, totalInfl_andInd_p] at h
  exact h

/-- The same inequality holds unconditionally, so `AND` does not refute `frh_openResidue`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * (p ^ 2 * (1 - p ^ 2)) * Real.log (1 / p) ≤ 2 * p := by
  have h := pbkt_twoBit_atom_numeric hp0 hp1
  nlinarith [h]

end StatMechTest.BooleanFunctions
