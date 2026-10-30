/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLTruncation
public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for degree truncation of Fourier mass

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLTruncation`:

* the degree-one hypothesis `hdeg` of `bkt_lhs_eq_level1_of_degree1` and
  `bkt_master_holds_degree1` is proved for the one-variable dictator `ω ↦ ω 0` at every
  `p ∈ (0, 1)`; on it the master estimate becomes `4σ_p² ≤ 4σ_p²` (tight);
* `bkt_degree1_witness` (the constant-false function), `bkt_high_part_decay`,
  `bkt_trunc_split`, `bkt_master_endpoint_zero`, `bkt_master_endpoint_one` and
  `bkt_budget_nonneg` at concrete parameters.

Window predicate: `bkt_lowDegreeMasterResidue q` is refuted for `q > 9/10`
(`sbk_lowDegreeMasterResidue_false`) and proved here for no `q > 1/2`. The test records the
degenerate instance `q = 1/2` (empty window) and runs `bkt_master_of_residue` on it.

The maximal influence of the constant-false indicator is `0` and `u / (2 - u) > 0` for
`0 < u < 1`, so `0 < maxInfl ν 0 ^ (u / (2 - u))` never holds; this is checked below.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLTruncation

open Finset StatMech StatMech.OSSS StatMech.Probability

/-- The one-variable dictator has no Fourier mass at degree `≥ 2`. -/
lemma dict_hdeg (p : ℝ) :
    ∀ S : Finset (Fin 1), 2 ≤ S.card →
      ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) S
        = 0 := by
  intro S hS
  have := Finset.card_le_univ S
  simp only [Fintype.card_fin] at this
  omega

/-- The constant-false indicator has maximal influence `0`. -/
lemma maxInfl_constFalse {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) = 0 := by
  unfold maxInfl OSSS.infl OSSS.expect
  simp

/-- `0 < maxInfl ν 0 ^ (u / (2 - u))` never holds for the constant-false indicator. -/
example {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] {p u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ¬ 0 < (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u)) := by
  rw [maxInfl_constFalse, Real.zero_rpow (div_pos hu0 (by linarith)).ne']
  exact lt_irrefl 0

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * (ptn_sigma p) ^ 2 ≤ 1 ^ ((1 / 2 : ℝ) / (2 - 1 / 2)) * (4 * (ptn_sigma p) ^ 2 * 1) := by
  have h := bkt_master_holds_degree1 hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (dict_hdeg p) (u := 1 / 2) (by norm_num) (by norm_num)
  rw [bkt_lhs_eq_level1_of_degree1 _ _ (dict_hdeg p), vgp_dictator_level1 hp0 hp1,
    vgp_dictator_maxInfl hp0 hp1, vgp_dictator_totalInfl hp0 hp1, ← ptn_sigma_sq hp0 hp1] at h
  linarith

example (p : ℝ) : ∀ S : Finset (Fin 3), 2 ≤ S.card →
    ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace (Fin 3) → Bool) ω then (1 : ℝ) else 0)
      S = 0 :=
  bkt_degree1_witness p

/-- `bkt_high_part_decay` on the dictator with cutoff `k = 1`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 1 < S.card),
        (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0)
            S) ^ 2
      ≤ (1 / 2) * (4 * p * (1 - p)) := by
  have h := bkt_high_part_decay hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num) 1
  rw [vgp_dictator_totalInfl hp0 hp1] at h
  norm_num at h ⊢
  linarith

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 1 ≤ S.card ∧ S.card ≤ 2),
            (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        + (1 - 1 / 2) ^ 2 * (4 * p * (1 - p)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt_trunc_split hp0 hp1 φ (by norm_num) (by norm_num) 2

/-- `bkt_master_endpoint_one` on the dictator: `4σ_p² ≤ 4σ_p²`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * (ptn_sigma p) ^ 2 ≤ 1 ^ ((1 : ℝ) / (2 - 1)) * (4 * (ptn_sigma p) ^ 2 * 1) := by
  have h := bkt_master_endpoint_one hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
  rw [bkt_lhs_eq_level1_of_degree1 _ _ (dict_hdeg p), vgp_dictator_level1 hp0 hp1,
    vgp_dictator_maxInfl hp0 hp1, vgp_dictator_totalInfl hp0 hp1, ← ptn_sigma_sq hp0 hp1] at h
  linarith

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (0 : ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ ((0 : ℝ) / (2 - 0))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt_master_endpoint_zero hp0 hp1 φ

example : ∃ k : ℕ, 0 ≤ (1 : ℝ) ^ ((1 / 2 : ℝ) / (2 - 1 / 2)) - (1 - 1 / 2) ^ k :=
  bkt_budget_nonneg (by norm_num) (by norm_num) (by simp)

/-- `bkt_lowDegreeMasterResidue q` holds vacuously for `q ≤ 1/2`. -/
lemma bkt_lowDegreeMasterResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) :
    bkt_lowDegreeMasterResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : pro_PBiasedMaster (1 / 2) :=
  bkt_master_of_residue (bkt_lowDegreeMasterResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.BKKKLTruncation
