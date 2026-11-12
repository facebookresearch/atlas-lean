/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.StoreyBH
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Storey-BH

* concrete values of `storeyPi0Plus1`, `storeyThreshold`, `storeyBHIndex`, `storeyBHRejections`;
* a two-null model with valid, independent p-values on which the FDR theorem applies
  (non-vacuity), with the FDR of each fixed `lam` computed exactly;
* **adversarial adaptive use 1**: choosing `lam` after seeing the p-values breaks FDR control
  (`FDR = 7/27 > 1/4 = q`);
* **adversarial adaptive use 2**: an estimator of `π₀` computed from the same p-value that is
  exactly unbiased, `E[π̂₀] = π₀`, yet BH at `q / π̂₀` has `FDR = 1/3 > 1/4 = q`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.StoreyBH

/-! ### Evaluation helpers for two p-values -/

theorem numBelow_two (v : Fin 2 → ℝ) (t : ℝ) :
    numBelow v t = (if v 0 ≤ t then 1 else 0) + (if v 1 ≤ t then 1 else 0) := by
  rw [numBelow, Finset.card_filter, Fin.sum_univ_two]

theorem numAbove_two (v : Fin 2 → ℝ) (lam : ℝ) :
    (Finset.univ.filter fun j => lam < v j).card =
      (if lam < v 0 then 1 else 0) + (if lam < v 1 then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_two]

/-- For two p-values the Storey-BH index is `2`, `1` or `0` by checking `k = 2`, then `k = 1`. -/
theorem storeyBHIndex_two (q lam : ℝ) (v : Fin 2 → ℝ) :
    storeyBHIndex q lam v =
      if 2 ≤ numBelow v (storeyThreshold q lam v 2) then 2
      else if 1 ≤ numBelow v (storeyThreshold q lam v 1) then 1 else 0 := by
  have hle := storeyBHIndex_le q lam v
  have hnb := storeyBHIndex_le_numBelow q lam v
  split_ifs with h2 h1
  · exact le_antisymm hle (le_storeyBHIndex le_rfl h2)
  · have h1' := le_storeyBHIndex (q := q) (lam := lam) (by norm_num) h1
    interval_cases hk : storeyBHIndex q lam v
    · rfl
    · exact absurd hnb h2
  · interval_cases hk : storeyBHIndex q lam v
    · rfl
    · exact absurd hnb h1
    · exact absurd hnb h2

/-! ### Concrete values -/

/-- p-values `1/9` and `1`. -/
noncomputable def pa : Fin 2 → ℝ := ![1 / 9, 1]

/-- With `lam = 1/9`, one p-value exceeds `lam`, so `π̂₀ = (1 + 1) / ((8/9) · 2) = 9/8`. -/
theorem storeyPi0Plus1_pa : storeyPi0Plus1 (1 / 9) pa = 9 / 8 := by
  rw [storeyPi0Plus1, numAbove_two]; norm_num [pa]

/-- Even when no p-value exceeds `lam`, the `+ 1` keeps `π̂₀ = 1 / ((1 - lam) m) > 0`. -/
theorem storeyPi0Plus1_all_small : storeyPi0Plus1 (1 / 2) (![1 / 9, 1 / 3] : Fin 2 → ℝ) = 1 := by
  rw [storeyPi0Plus1, numAbove_two]; norm_num

/-- At `q = 1/4`, `lam = 1/9`: the thresholds `min (1/9) (q k / (m π̂₀)) = min (1/9) (k/9)` are
capped at `lam = 1/9` already for `k = 1`. -/
theorem storeyThreshold_pa (k : ℕ) (hk : 1 ≤ k) : storeyThreshold (1 / 4) (1 / 9) pa k = 1 / 9 := by
  rw [storeyThreshold, storeyPi0Plus1_pa]
  apply min_eq_left
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  norm_num
  linarith

/-- Storey-BH at `q = 1/4`, `lam = 1/9` rejects exactly one hypothesis of `pa`. -/
theorem storeyBHIndex_pa : storeyBHIndex (1 / 4) (1 / 9) pa = 1 := by
  rw [storeyBHIndex_two, storeyThreshold_pa 2 (by norm_num), storeyThreshold_pa 1 le_rfl,
    numBelow_two]
  norm_num [pa]

/-- The rejected hypothesis is the first one. -/
theorem storeyBHRejections_pa : storeyBHRejections (1 / 4) (1 / 9) pa = {0} := by
  ext i
  rw [mem_storeyBHRejections, storeyBHIndex_pa, storeyThreshold_pa 1 le_rfl]
  fin_cases i <;> norm_num [pa]

/-- Boundary case: if every p-value exceeds `lam`, Storey-BH rejects nothing, whatever `q` and
`m`. -/
theorem storeyBHRejections_eq_empty_of_lt {m : ℕ} (q : ℝ) {lam : ℝ} {v : Fin m → ℝ}
    (hv : ∀ j, lam < v j) : storeyBHRejections q lam v = ∅ :=
  Finset.eq_empty_of_forall_notMem fun i hi =>
    absurd (le_of_mem_storeyBHRejections hi) (not_le.mpr (hv i))

/-! ### A two-null model with valid, independent p-values

Each p-value takes the values `1/9, 1/3, 1` with probabilities `1/9, 2/9, 2/3` (a valid discrete
p-value: `P(p ≤ t) ≤ t`), independently. Both hypotheses are true nulls. -/

/-- Point masses of one p-value. -/
noncomputable def r : Fin 3 → ℝ := ![1 / 9, 2 / 9, 2 / 3]

/-- Values of one p-value. -/
noncomputable def val : Fin 3 → ℝ := ![1 / 9, 1 / 3, 1]

theorem r_nonneg (a : Fin 3) : 0 ≤ r a := by fin_cases a <;> norm_num [r]

theorem sum_ofReal_r : ∑ a, ENNReal.ofReal (r a) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => r_nonneg a, Fin.sum_univ_three]
  norm_num [r]

/-- The law of one p-value. -/
noncomputable def ν : Measure (Fin 3) :=
  (PMF.ofFintype (fun a => ENNReal.ofReal (r a)) sum_ofReal_r).toMeasure

instance : IsProbabilityMeasure ν := by unfold ν; infer_instance

/-- The joint law: two independent copies. -/
noncomputable def μ : Measure (Fin 3 × Fin 3) := ν.prod ν

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The two p-values. -/
noncomputable def P : Fin 2 → Fin 3 × Fin 3 → ℝ := ![fun ω => val ω.1, fun ω => val ω.2]

theorem ν_apply (S : Set (Fin 3)) : ν S = ENNReal.ofReal (∑ a, S.indicator r a) := by
  rw [ν, PMF.toMeasure_apply_fintype, ENNReal.ofReal_sum_of_nonneg fun a _ => by
    by_cases h : a ∈ S <;> simp [h, r_nonneg]]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a ∈ S <;> simp [h]

theorem μ_real_singleton (a b : Fin 3) : μ.real {(a, b)} = r a * r b := by
  rw [measureReal_def, μ, ← Set.singleton_prod_singleton, Measure.prod_prod, ν_apply, ν_apply,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => by
      by_cases h : x ∈ ({a} : Set (Fin 3)) <;> simp [h, r_nonneg]),
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => by
      by_cases h : x ∈ ({b} : Set (Fin 3)) <;> simp [h, r_nonneg])]
  simp [Set.indicator_apply]

theorem measurable_P (i : Fin 2) : Measurable (P i) := by
  fin_cases i
  · exact (measurable_of_countable val).comp measurable_fst
  · exact (measurable_of_countable val).comp measurable_snd

/-- Expectations in the model are finite weighted sums over the nine value pairs. -/
theorem integral_eq_sum (F : (Fin 2 → ℝ) → ℝ) :
    ∫ ω, F (fun i => P i ω) ∂μ = ∑ a, ∑ b, r a * r b * F ![val a, val b] := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [μ_real_singleton, smul_eq_mul]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Both p-values are valid. -/
theorem isValidPValue_P (i : Fin 2) : IsValidPValue μ (P i) := by
  intro t ht
  have hS : ν {a | val a ≤ t} ≤ ENNReal.ofReal t := by
    rw [ν_apply]
    apply ENNReal.ofReal_le_ofReal
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Fin.sum_univ_three]
    obtain ⟨ht0, ht1⟩ := ht
    split_ifs with h0 h1 h2 <;> norm_num [r, val] at * <;> linarith
  fin_cases i
  · have : {ω : Fin 3 × Fin 3 | P 0 ω ≤ t} = {a | val a ≤ t} ×ˢ Set.univ := by
      ext ω; simp [P]
    simpa [this, μ, Measure.prod_prod] using hS
  · have : {ω : Fin 3 × Fin 3 | P 1 ω ≤ t} = Set.univ ×ˢ {a | val a ≤ t} := by
      ext ω; simp [P]
    simpa [this, μ, Measure.prod_prod] using hS

theorem indepFun_P_rest_zero :
    IndepFun (P 0) (fun ω (j : {j : Fin 2 // j ≠ 0}) => P j ω) μ := by
  have h := indepFun_prod (μ := ν) (ν := ν) (X := val)
    (Y := fun b (_ : {j : Fin 2 // j ≠ 0}) => val b)
    (measurable_of_countable _) (measurable_of_countable _)
  have e : (fun ω (j : {j : Fin 2 // j ≠ 0}) => P j ω) = fun ω _ => val ω.2 := by
    funext ω j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact absurd rfl hj
    · rfl
  rw [e]
  exact h

theorem indepFun_P_rest_one :
    IndepFun (P 1) (fun ω (j : {j : Fin 2 // j ≠ 1}) => P j ω) μ := by
  have h := (indepFun_prod (μ := ν) (ν := ν) (Y := val)
    (X := fun b (_ : {j : Fin 2 // j ≠ 1}) => val b)
    (measurable_of_countable _) (measurable_of_countable _)).symm
  have e : (fun ω (j : {j : Fin 2 // j ≠ 1}) => P j ω) = fun ω _ => val ω.1 := by
    funext ω j
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · rfl
    · exact absurd rfl hj
  rw [e]
  exact h

/-- Each p-value is independent of the other one (the hypothesis of the theorem). -/
theorem indepFun_P_rest (i : Fin 2) :
    IndepFun (P i) (fun ω (j : {j // j ≠ i}) => P j ω) μ := by
  fin_cases i
  · exact indepFun_P_rest_zero
  · exact indepFun_P_rest_one

/-- **Non-vacuity of the theorem.** On this model every fixed `lam ∈ [0, 1)` gives Storey-BH at
`q = 1/4` false discovery rate at most `1/4`. -/
theorem fdr_fixed_lam_le {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (storeyBHRejections (1 / 4) lam fun i => P i ω)
      ∂μ ≤ 1 / 4 :=
  integral_falseDiscoveryProportion_storeyBHRejections_le μ P measurable_P Finset.univ
    (fun i _ => indepFun_P_rest i) (fun i _ => isValidPValue_P i) (by norm_num) hlam0 hlam1

/-! ### Exact FDR of each fixed `lam`, and of choosing `lam` after seeing the data -/

theorem fdp_univ (R : Finset (Fin 2)) :
    falseDiscoveryProportion Finset.univ R = (R.card : ℝ) / max (R.card : ℝ) 1 := by
  simp [falseDiscoveryProportion]

/-- Storey-BH index at `q = 1/4`, `lam = 1/9` on the nine value pairs: two rejections if both
p-values are `1/9`, one if exactly one is, none otherwise. -/
theorem storeyBHIndex_lam_ninth (a b : Fin 3) :
    storeyBHIndex (1 / 4) (1 / 9) ![val a, val b] =
      if a = 0 ∧ b = 0 then 2 else if a = 0 ∨ b = 0 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp only [storeyBHIndex_two, storeyThreshold_eq (two_ne_zero : (2 : ℕ) ≠ 0), numAbove_two,
      numBelow_two] <;> norm_num [val]

/-- Storey-BH index at `q = 1/4`, `lam = 1/3`: two rejections iff both p-values are `≤ 1/3`. -/
theorem storeyBHIndex_lam_third (a b : Fin 3) :
    storeyBHIndex (1 / 4) (1 / 3) ![val a, val b] = if a ≠ 2 ∧ b ≠ 2 then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp only [storeyBHIndex_two, storeyThreshold_eq (two_ne_zero : (2 : ℕ) ≠ 0), numAbove_two,
      numBelow_two] <;> norm_num [val]

/-- With `lam = 1/9` fixed, `FDR = P(some p-value = 1/9) = 17/81 ≤ 1/4`. -/
theorem fdr_lam_ninth :
    ∫ ω, falseDiscoveryProportion Finset.univ (storeyBHRejections (1 / 4) (1 / 9) fun i => P i ω)
      ∂μ = 17 / 81 := by
  rw [integral_eq_sum (fun v => falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 4) (1 / 9) v))]
  simp only [fdp_univ, card_storeyBHRejections (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 9 : ℝ) ≤ 1), storeyBHIndex_lam_ninth, Fin.sum_univ_three]
  norm_num [r]

/-- With `lam = 1/3` fixed, `FDR = P(both p-values ≤ 1/3) = 1/9 ≤ 1/4`. -/
theorem fdr_lam_third :
    ∫ ω, falseDiscoveryProportion Finset.univ (storeyBHRejections (1 / 4) (1 / 3) fun i => P i ω)
      ∂μ = 1 / 9 := by
  rw [integral_eq_sum (fun v => falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 4) (1 / 3) v))]
  simp only [fdp_univ, card_storeyBHRejections (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 3 : ℝ) ≤ 1), storeyBHIndex_lam_third, Fin.sum_univ_three]
  norm_num [r]

/-- **A naive adaptive choice of the tuning parameter**: after seeing the p-values, use whichever
of `lam = 1/9` and `lam = 1/3` gives more rejections. -/
noncomputable def lamHat (v : Fin 2 → ℝ) : ℝ :=
  if (storeyBHRejections (1 / 4) (1 / 9) v).card < (storeyBHRejections (1 / 4) (1 / 3) v).card
  then 1 / 3 else 1 / 9

theorem card_storeyBHRejections_lamHat (v : Fin 2 → ℝ) :
    (storeyBHRejections (1 / 4) (lamHat v) v).card =
      max (storeyBHIndex (1 / 4) (1 / 9) v) (storeyBHIndex (1 / 4) (1 / 3) v) := by
  have h9 := card_storeyBHRejections (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 9 : ℝ) ≤ 1) v
  have h3 := card_storeyBHRejections (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 3 : ℝ) ≤ 1) v
  unfold lamHat
  split_ifs with h <;> omega

/-- **Adversarial adaptive use: the failure, computed exactly.** On the same model, where each
fixed `lam` has `FDR ≤ 1/4` (`fdr_fixed_lam_le`; exactly `17/81` and `1/9` for the two candidates),
choosing `lam` after seeing the p-values gives `FDR = 7/27`. -/
theorem fdr_lamHat :
    ∫ ω, falseDiscoveryProportion Finset.univ
      (storeyBHRejections (1 / 4) (lamHat fun i => P i ω) fun i => P i ω) ∂μ = 7 / 27 := by
  rw [integral_eq_sum (fun v => falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 4) (lamHat v) v))]
  simp only [fdp_univ, card_storeyBHRejections_lamHat, storeyBHIndex_lam_ninth,
    storeyBHIndex_lam_third, Fin.sum_univ_three]
  norm_num [r]

/-- The post-hoc choice of `lam` violates FDR control at `q = 1/4`. -/
theorem fdr_lamHat_gt : (1 / 4 : ℝ) < ∫ ω, falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 4) (lamHat fun i => P i ω) fun i => P i ω) ∂μ := by
  rw [fdr_lamHat]; norm_num

/-! ### Conservative in expectation is not enough

One true null with the law `ν` above, and an estimator `π̂₀` computed from the same p-value that is
exactly unbiased, `E[π̂₀] = 1 = π₀`. BH at the plug-in level `q / π̂₀` has FDR `1/3 > 1/4 = q`:
`π̂₀` is small exactly when the p-value is moderately small. Storey's estimator avoids this
because, on `{p i ≤ lam}`, it does not depend on `p i` at all (`storeyPi0Plus1_update_zero`). -/

/-- An estimator of `π₀` that reads the p-value it is used to test. -/
noncomputable def piHat : Fin 3 → ℝ := ![1, 3 / 4, 13 / 12]

theorem ν_real_singleton (a : Fin 3) : ν.real {a} = r a := by
  rw [measureReal_def, ν_apply, ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => by
    by_cases h : x ∈ ({a} : Set (Fin 3)) <;> simp [h, r_nonneg])]
  simp [Set.indicator_apply]

/-- `π̂₀` is exactly unbiased for `π₀ = 1`. -/
theorem integral_piHat : ∫ a, piHat a ∂ν = 1 := by
  rw [integral_fintype Integrable.of_finite, Fin.sum_univ_three]
  simp only [ν_real_singleton, smul_eq_mul]
  norm_num [r, piHat]

theorem bhIndex_one (α : ℝ) (v : Fin 1 → ℝ) :
    bhIndex α v = if 1 ≤ numBelow v (α * ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) then 1 else 0 := by
  have hle := bhIndex_le α v
  have hnb := bhIndex_le_numBelow α v
  split_ifs with h
  · exact le_antisymm hle (le_bhIndex le_rfl h)
  · interval_cases hk : bhIndex α v
    · rfl
    · exact absurd hnb h

theorem numBelow_one (v : Fin 1 → ℝ) (t : ℝ) : numBelow v t = if v 0 ≤ t then 1 else 0 := by
  rw [numBelow, Finset.card_filter, Fin.sum_univ_one]

/-- **Adversarial adaptive use 2.** BH at the plug-in level `q / π̂₀` with an unbiased but
data-dependent `π̂₀` has FDR `1/3` at `q = 1/4`. -/
theorem fdr_plugIn_piHat :
    ∫ a, falseDiscoveryProportion {0} (bhRejections ((1 / 4) / piHat a) ![val a]) ∂ν = 1 / 3 := by
  rw [integral_fintype Integrable.of_finite, Fin.sum_univ_three]
  have hfdp (R : Finset (Fin 1)) :
      falseDiscoveryProportion {0} R = (R.card : ℝ) / max (R.card : ℝ) 1 := by
    rw [falseDiscoveryProportion, Finset.inter_eq_left.mpr fun x _ => by
      simp [Fin.fin_one_eq_zero x]]
  have hpi (a : Fin 3) : 0 ≤ (1 / 4) / piHat a := by fin_cases a <;> norm_num [piHat]
  simp only [ν_real_singleton, smul_eq_mul, hfdp, card_bhRejections (hpi _), bhIndex_one,
    numBelow_one]
  norm_num [r, piHat, val]

theorem fdr_plugIn_piHat_gt :
    (1 / 4 : ℝ) < ∫ a, falseDiscoveryProportion {0} (bhRejections ((1 / 4) / piHat a) ![val a]) ∂ν
    := by
  rw [fdr_plugIn_piHat]; norm_num

/-! ### Conservativeness of Storey's estimator in the model -/

/-- In the two-null model, main's conservativeness lemma `TwoGroupsTesting.le_integral_storeyPi0`
gives `E[π̂₀(1/3)] ≥ |H0| / m = 1` for Storey's (2002) estimator. -/
theorem one_le_integral_storeyPi0 :
    (1 : ℝ) ≤ ∫ ω, TwoGroupsTesting.storeyPi0 (1 / 3) (fun i => P i ω) ∂μ := by
  have h := TwoGroupsTesting.le_integral_storeyPi0 (μ := μ) measurable_P (H0 := Finset.univ)
    (fun i _ => isValidPValue_P i) (t := 1 / 3) (by norm_num) (by norm_num)
  simpa using h

/-- The bridge between the two estimators on a concrete vector: with `lam = 1/9`, `pa` has one
p-value above `lam`, so `π̂₀ = 1 / ((8/9) · 2) = 9/16` without the `+ 1` and `9/8` with it. -/
example : TwoGroupsTesting.storeyPi0 (1 / 9) pa = 9 / 16 := by
  have h := storeyPi0Plus1_eq_storeyPi0_add (1 / 9) pa
  rw [storeyPi0Plus1_pa] at h
  norm_num at h
  linarith

/-- The leave-one-out estimator bound `∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m` holds in the model. -/
theorem sum_integral_inv_storeyPi0Plus1_update_le_two :
    ∑ i, ∫ ω, (storeyPi0Plus1 (1 / 3) (Function.update (fun j => P j ω) i 0))⁻¹ ∂μ ≤ 2 := by
  have h := sum_integral_inv_storeyPi0Plus1_update_le μ P measurable_P Finset.univ
    (fun i _ => indepFun_P_rest i) (fun i _ => isValidPValue_P i) (lam := 1 / 3)
    (by norm_num) (by norm_num)
  simpa using h

/-- The iIndepFun corollary is usable too: mutually independent p-values satisfy the per-null
independence hypothesis (`indepFun_rest_of_iIndepFun`). -/
example {Ω : Type*} [MeasurableSpace Ω] (μ' : Measure Ω) [IsProbabilityMeasure μ']
    (p : Fin 3 → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ')
    (hnull : ∀ i, IsValidPValue μ' (p i)) :
    ∫ ω, falseDiscoveryProportion Finset.univ (storeyBHRejections (1 / 10) (1 / 2)
      fun i => p i ω) ∂μ' ≤ 1 / 10 :=
  integral_falseDiscoveryProportion_storeyBHRejections_le_of_iIndepFun μ' p hp hindep _
    (fun i _ => hnull i) (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.StoreyBH
