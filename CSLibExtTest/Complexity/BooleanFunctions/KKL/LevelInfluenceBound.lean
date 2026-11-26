/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.LevelInfluenceBound
public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for the level-one mass bound

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.LevelInfluenceBound`:

* `lib_optimal_exponent` at `u = 1/2` (both sides equal `1/3`);
* `lib_level1_mass_le` and `lib_capped_optimal_weight` on the one-variable dictator
  `ω ↦ ω 0` at every `p ∈ (0, 1)` and `u = 1/2`: the conclusion is the identity
  `4p(1-p) ≤ 4p(1-p)`, so both bounds are tight on dictators;
* `lib_residue_iff_levelGe2` at `k = 1`, where the level-`≥ 2` sum is empty;
* `lib_levelGe2_budget_pos` at `p = 3/4`, `δ = 1`, `u = 1/2`, and `lib_level1_mass_nonneg`.

Not tested: `lib_levelGe2Residue q` is proved here for no `q > 1/2` (and is neither proved
nor refuted in the library for any such `q`). The test records that it holds vacuously at
`q = 1/2`, where the window `(1/2, q)` is empty, and runs `lib_levelGe2_discharges` on that
degenerate instance.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.LevelInfluenceBound

open Finset StatMech StatMech.OSSS StatMech.Probability

/-- The indicator of the one-variable dictator `ω ↦ ω 0`. -/
noncomputable abbrev dictInd : ConfigSpace (Fin 1) → ℝ := fun ω => if ω 0 then (1 : ℝ) else 0

example : (2 : ℝ) / (2 - 1 / 2) - 1 = (1 / 2) / (2 - 1 / 2) :=
  lib_optimal_exponent (by norm_num) (by norm_num)

example : (1 / 2 : ℝ) / (2 - 1 / 2) = 1 / 3 := by norm_num

/-- `lib_level1_mass_le` on the dictator: its conclusion is `4p(1-p) ≤ 4p(1-p)`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 4 * (p * (1 - p)) ≤ 4 * p * (1 - p) := by
  have h := lib_level1_mass_le hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num)
  rw [vgp_dictator_level1 hp0 hp1, vgp_dictator_maxInfl hp0 hp1, Real.one_rpow,
    vgp_dictator_totalInfl hp0 hp1] at h
  linarith

/-- `lib_capped_optimal_weight` on the dictator: only `S = {0}` contributes. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * ∑ S : Finset (Fin 1), (S.card : ℝ)
        * (((1 - 1 / 2) * (4 * p * (1 - p))) ^ (S.card - 1) * (ptn_coeff p dictInd S) ^ 2)
      ≤ 4 * p * (1 - p) := by
  have h := lib_capped_optimal_weight hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num)
  rw [vgp_dictator_maxInfl hp0 hp1, Real.one_rpow, vgp_dictator_totalInfl hp0 hp1] at h
  simpa using h

/-- `lib_residue_iff_levelGe2` at `k = 1`: the level-`≥ 2` part is the empty sum. -/
example {p B : ℝ} (φ : ConfigSpace (Fin 2) → Bool) (u : ℝ)
    (h : 4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 1 ≤ S.card ∧ S.card ≤ 1),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ B) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ B := by
  have h' := (lib_residue_iff_levelGe2 φ le_rfl (B := B)).mp h
  have hempty : univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 1) = ∅ := by
    ext S; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
  rw [hempty, sum_empty] at h'
  linarith

example : ∃ k : ℕ, 1 ≤ k ∧ 0 ≤ (1 : ℝ) ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
    - 4 * (3 / 4) * (1 - 3 / 4) * (1 - 1 / 2) ^ k
    - 4 * (3 / 4) * (1 - 3 / 4) * (1 : ℝ) ^ ((1 / 2 : ℝ) / (2 - 1 / 2)) :=
  lib_levelGe2_budget_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp)

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ 4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => S.card = 1),
      (ptn_coeff p dictInd S) ^ 2 :=
  (lib_level1_mass_nonneg hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num)).1

/-- `lib_levelGe2Residue q` holds vacuously for `q ≤ 1/2`. -/
lemma lib_levelGe2Residue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : lib_levelGe2Residue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : dtr_lowDegreeResidue (1 / 2) :=
  lib_levelGe2_discharges (lib_levelGe2Residue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.LevelInfluenceBound
