/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.Fano

@[expose] public section

/-!
# Tests for Fano's inequality

Two concrete hypotheses on `Bool`: a fair coin and a coin biased
towards `true` with probability `3 / 4`. Their pairwise `klDiv`
values are computed exactly, the identity estimator's average error
is `3 / 8`, and Fano's bound instantiates on them. A second case has
common zero support (both hypotheses `PMF.pure false`, divergence
`0`, error `1 / 2`), and a third shows the disjoint point masses
`pure false` / `pure true` have infinite `klDiv` — the case where a
bare finite sum would wrongly give `0`.
-/

set_option autoImplicit false

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.LearningTheory.Fano

/-- A fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

/-- A coin biased towards `true` with probability `3 / 4`. -/
noncomputable def biased : PMF Bool :=
  PMF.ofFintype (fun b ↦ ((cond b (3 / 4) (1 / 4) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, ← ENNReal.coe_one,
      ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num)

theorem fair_apply (b : Bool) : (fair b).toReal = 1 / 2 := by
  simp [fair]

theorem biased_apply (b : Bool) :
    (biased b).toReal = cond b (3 / 4) (1 / 4) := by
  cases b <;> simp [biased]

theorem fair_ne_zero (a : Bool) : fair a ≠ 0 := by
  simp [fair]

theorem biased_ne_zero (a : Bool) : biased a ≠ 0 := by
  cases a <;> simp [biased]

/-- The two coin hypotheses: `false` is fair, `true` is biased. -/
noncomputable def coinHyp : Bool → PMF Bool := fun i => cond i biased fair

theorem coinHyp_supp : ∀ i j a, (coinHyp j a) = 0 → (coinHyp i a) = 0 := by
  intro i j a h
  cases j <;> simp only [coinHyp, Bool.cond_false, Bool.cond_true] at h
  · exact (fair_ne_zero a h).elim
  · exact (biased_ne_zero a h).elim

/-- The divergence of the fair coin from the biased coin, in nats. -/
theorem klDiv_fair_biased :
    (klDiv fair.toMeasure biased.toMeasure).toReal =
      1 / 2 * Real.log ((1 / 2) / (1 / 4)) + 1 / 2 * Real.log ((1 / 2) / (3 / 4)) := by
  have hpq : ∀ a, biased a = 0 → fair a = 0 := fun a h ↦ (biased_ne_zero a h).elim
  rw [toReal_klDiv_toMeasure hpq, Fintype.sum_bool, fair_apply, fair_apply]
  simp [biased]
  norm_num
  ring

/-- The divergence of the biased coin from the fair coin, in nats. -/
theorem klDiv_biased_fair :
    (klDiv biased.toMeasure fair.toMeasure).toReal =
      1 / 4 * Real.log ((1 / 4) / (1 / 2)) + 3 / 4 * Real.log ((3 / 4) / (1 / 2)) := by
  have hpq : ∀ a, fair a = 0 → biased a = 0 := fun a h ↦ (fair_ne_zero a h).elim
  rw [toReal_klDiv_toMeasure hpq, Fintype.sum_bool]
  simp [biased, fair]
  norm_num
  ring

/-- Every pairwise divergence of the two coin hypotheses is at most
the sum of the two cross divergences. -/
theorem coinHyp_kl_le (i j : Bool) :
    (klDiv (coinHyp i).toMeasure (coinHyp j).toMeasure).toReal ≤
      (klDiv fair.toMeasure biased.toMeasure).toReal +
        (klDiv biased.toMeasure fair.toMeasure).toReal := by
  cases i <;> cases j <;> simp only [coinHyp, Bool.cond_false, Bool.cond_true]
  · rw [klDiv_self, ENNReal.toReal_zero]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  · rw [klDiv_self, ENNReal.toReal_zero]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The identity estimator's average error on the two coin hypotheses
is `3 / 8`: it errs with probability `1 / 2` on the fair coin (the
`true` observation) and `1 / 4` on the biased coin (the `false`
observation). -/
theorem coinHyp_error :
    (∑ i, (∑ a ∈ Finset.univ.filter (fun a => id a ≠ i), (coinHyp i a).toReal)) /
        Fintype.card Bool = 3 / 8 := by
  rw [Fintype.sum_bool]
  have h1 : Finset.univ.filter (fun a : Bool => id a ≠ false) = {true} := by decide
  have h2 : Finset.univ.filter (fun a : Bool => id a ≠ true) = {false} := by decide
  rw [h1, h2, Finset.sum_singleton, Finset.sum_singleton]
  simp only [coinHyp, Bool.cond_false, Bool.cond_true, fair_apply, biased_apply,
    Bool.cond_false, Bool.cond_true]
  norm_num [Fintype.card_bool]

/-- Fano's inequality on the two concrete coin hypotheses: the average
error is `3 / 8` and the bound instantiates with the computed
divergences. -/
example :
    (∑ i, (∑ a ∈ Finset.univ.filter (fun a => id a ≠ i), (coinHyp i a).toReal)) /
        Fintype.card Bool = 3 / 8 ∧
      1 - (((klDiv fair.toMeasure biased.toMeasure).toReal +
          (klDiv biased.toMeasure fair.toMeasure).toReal) + Real.log 2) /
          Real.log (Fintype.card Bool) ≤ 3 / 8 := by
  refine ⟨coinHyp_error, ?_⟩
  have h := fano_finite coinHyp id (by decide) coinHyp_supp _ coinHyp_kl_le
  rwa [coinHyp_error] at h

/-- Common zero support: both hypotheses are `PMF.pure false`, so every
pairwise divergence is `0`. -/
example :
    ∀ i j : Bool,
      (klDiv ((fun _ : Bool => PMF.pure false) i).toMeasure
          ((fun _ : Bool => PMF.pure false) j).toMeasure).toReal ≤ 0 := by
  intro i j
  simp [klDiv_self]

/-- Common zero support, Fano's bound: with the constant estimator
`fun _ => false` the average error is `1 / 2`, and the `β = 0` Fano
bound gives `0 ≤ 1 / 2`. -/
example :
    (∑ i, (∑ a ∈ Finset.univ.filter
        (fun a => (fun _ : Bool => false) a ≠ i),
        ((fun _ : Bool => PMF.pure false) i a).toReal)) / Fintype.card Bool = 1 / 2 ∧
      1 - ((0 : ℝ) + Real.log 2) / Real.log (Fintype.card Bool) ≤ 1 / 2 := by
  refine ⟨?_, ?_⟩
  · have h_inner_false :
        (∑ a ∈ Finset.univ.filter (fun a => (fun _ : Bool => false) a ≠ false),
          ((fun _ : Bool => PMF.pure false) false a).toReal) = 0 := by
      have hf : Finset.univ.filter (fun a => (fun _ : Bool => false) a ≠ false) = ∅ := by
        decide
      rw [hf, Finset.sum_empty]
    have h_inner_true :
        (∑ a ∈ Finset.univ.filter (fun a => (fun _ : Bool => false) a ≠ true),
          ((fun _ : Bool => PMF.pure false) true a).toReal) = 1 := by
      have hf : Finset.univ.filter (fun a => (fun _ : Bool => false) a ≠ true) =
          Finset.univ := by decide
      rw [hf]
      simp [PMF.pure_apply]
    rw [Fintype.sum_bool, h_inner_false, h_inner_true]
    norm_num [Fintype.card_bool]
  · have hlog : Real.log (Fintype.card Bool : ℝ) = Real.log 2 := by
      rw [Fintype.card_bool]
      norm_num
    rw [hlog, zero_add]
    have : (Real.log 2) / Real.log 2 = 1 :=
      div_self (Real.log_pos one_lt_two).ne'
    rw [this]
    norm_num

/-- Disjoint point masses have infinite `klDiv`: a bare finite sum
would give `0` here (`1 / 0 = 0`, `Real.log 0 = 0`), which is why the
theorem is stated with `klDiv`. -/
example :
    klDiv (PMF.pure false).toMeasure (PMF.pure true).toMeasure = ⊤ := by
  rw [klDiv_of_not_ac]
  intro hac
  have hq : (PMF.pure true).toMeasure {false} = 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.pure_apply]
  have hp : (PMF.pure false).toMeasure {false} = 1 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.pure_apply]
  have h0 := hac hq
  rw [hp] at h0
  exact one_ne_zero h0

end MathlibExtTest.Probability.LearningTheory.Fano
