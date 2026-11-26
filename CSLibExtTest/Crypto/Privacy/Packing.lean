/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Privacy.Packing
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for the packing lower bound

* Randomized response on one bit is `log 3`-differentially private and satisfies the hypotheses
  of `DifferentiallyPrivate.packing` with two databases one step apart (non-vacuity).
* A fair coin attains `N = 2 e^{ε k}` with `ε = 0`, `k = 0` and `N = 2`, so the factor `2` is
  sharp.
* With `k = 0` the bound says that no probability measure gives mass `1 / 2` to three disjoint
  events.
* The consequence `k ≥ log (N / 2) / ε` with `ε = log 2` and `N = 8`, and the form of Dwork and
  Roth's Lemma 8.4.
-/

namespace CSLibExtTest.Crypto.Privacy.Packing

open Function MeasureTheory Cslib.Crypto.Privacy
open scoped ENNReal NNReal

/-- Randomized response on one bit: report the bit with probability `3 / 4` and its negation with
probability `1 / 4`. -/
noncomputable def randResp (b : Bool) : PMF Bool :=
  PMF.ofFintype (fun c ↦ ((if c = b then 3 / 4 else 1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
    cases b <;> norm_num)

/-- Randomized response with probabilities `3 / 4` and `1 / 4` is `log 3`-differentially private
for any two databases. -/
theorem randResp_differentiallyPrivate :
    DifferentiallyPrivate (fun _ _ : Bool ↦ True) (fun b ↦ (randResp b).toMeasure)
      (Real.log 3) 0 := by
  intro x y _ S _
  rw [Real.exp_log (by norm_num), add_zero, PMF.toMeasure_apply_fintype,
    PMF.toMeasure_apply_fintype, Finset.mul_sum]
  gcongr with c
  by_cases hc : c ∈ S
  · simp only [Set.indicator_of_mem hc, randResp, PMF.ofFintype_apply]
    rw [show ENNReal.ofReal 3 = ((3 : ℝ≥0) : ℝ≥0∞) by norm_num, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    split_ifs <;> norm_num
  · simp [Set.indicator_of_notMem hc]

/-- Non-vacuity: randomized response puts mass `3 / 4` on `{b}` from the bit `b`, so the two
bits, one step apart, with the disjoint events `{false}` and `{true}`, satisfy the hypotheses of
the packing bound with `ε = log 3`, `k = 1` and `N = 2`. -/
example : ((2 : ℕ) : ℝ) ≤ 2 * Real.exp (Real.log 3 * (1 : ℕ)) := by
  refine (randResp_differentiallyPrivate.packing (d₀ := false) (k := 1) (d := ![false, true])
    (S := fun i ↦ {![false, true] i}) (fun i ↦ ⟨fun j ↦ if j = 0 then ![false, true] i else false,
      by simp, by simp, fun _ _ ↦ trivial⟩) (fun _ ↦ measurableSet_singleton _) ?_ ?_).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp only [randResp, PMF.ofFintype_apply, ↓reduceIte]
    rw [← ENNReal.coe_two, ← ENNReal.coe_inv two_ne_zero, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe]
    norm_num

/-- A fair coin. -/
noncomputable def fairCoin : PMF Bool :=
  PMF.ofFintype (fun _ ↦ 2⁻¹) (by rw [Fintype.sum_bool, ENNReal.inv_two_add_inv_two])

/-- The factor `2` is sharp: a fair coin, released whatever the database, is `0`-differentially
private and gives mass `1 / 2` to each of the disjoint events `{false}` and `{true}`, so with
`ε = 0`, `k = 0` and `N = 2` the bound `N ≤ 2 e^{ε k}` holds with equality. -/
example : ((2 : ℕ) : ℝ) = 2 * Real.exp ((0 : ℝ) * (0 : ℕ)) := by
  have h : DifferentiallyPrivate (fun _ _ : Unit ↦ True) (fun _ ↦ fairCoin.toMeasure) 0 0 :=
    fun _ _ _ _ _ ↦ by simp
  refine le_antisymm (h.packing (d₀ := ()) (k := 0) (d := fun _ ↦ ())
    (S := fun i ↦ {![false, true] i}) (fun _ ↦ ⟨fun _ ↦ (), rfl, rfl, by simp⟩)
    (fun _ ↦ measurableSet_singleton _) ?_ fun i ↦ ?_).1 (by simp)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), fairCoin,
      PMF.ofFintype_apply]

/-- With `k = 0` the bound is the pigeonhole principle for probability: no probability measure
gives mass at least `1 / 2` to three pairwise disjoint measurable events. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Fin 3 → Set Ω} (hS : ∀ i, MeasurableSet (S i)) (hdisj : Pairwise (Disjoint on S)) :
    ¬ ∀ i, 2⁻¹ ≤ μ (S i) := by
  intro hprob
  have h : DifferentiallyPrivate (fun _ _ : Unit ↦ True) (fun _ ↦ μ) 0 0 := fun _ _ _ _ _ ↦ by
    simp
  have := (h.packing (d₀ := ()) (k := 0) (d := fun _ ↦ ())
    (fun _ ↦ ⟨fun _ ↦ (), rfl, rfl, by simp⟩) hS hdisj hprob).1
  norm_num at this

/-- The consequence: an `ε`-differentially private mechanism with `ε = log 2` that separates
`8` databases, each within `k` steps of `d₀`, needs `k ≥ log 4 / log 2 = 2`. -/
example {X Ω : Type*} [MeasurableSpace Ω] {Adj : X → X → Prop} {M : X → Measure Ω}
    (h : DifferentiallyPrivate Adj M (Real.log 2) 0) {d₀ : X} [IsProbabilityMeasure (M d₀)]
    {k : ℕ} {d : Fin 8 → X}
    (hd : ∀ i, ∃ z : ℕ → X, z 0 = d i ∧ z k = d₀ ∧ ∀ j < k, Adj (z j) (z (j + 1)))
    {S : Fin 8 → Set Ω} (hS : ∀ i, MeasurableSet (S i)) (hdisj : Pairwise (Disjoint on S))
    (hprob : ∀ i, 2⁻¹ ≤ M (d i) (S i)) : 2 ≤ k := by
  have h2 := (h.packing hd hS hdisj hprob).2 (Real.log_pos one_lt_two)
  have h4 : Real.log ((8 : ℕ) / 2) = 2 * Real.log 2 := by
    rw [show ((8 : ℕ) : ℝ) / 2 = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
  rw [h4, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one] at h2
  exact_mod_cast h2

/-- The conclusion of Dwork and Roth's Lemma 8.4, `ε ≥ ln 2 · (s - 1) / k`, cleared of the
division: `2 ^ s` databases, each joined to the first by a chain of `k` steps (as databases at
pairwise distance at most `k` are), with disjoint events of probability at least `1 / 2`, force
`ln 2 · (s - 1) ≤ ε k`. -/
example {X Ω : Type*} [MeasurableSpace Ω] {Adj : X → X → Prop} {M : X → Measure Ω} {ε : ℝ}
    (h : DifferentiallyPrivate Adj M ε 0) {s k : ℕ} {d : Fin (2 ^ s) → X}
    [IsProbabilityMeasure (M (d 0))]
    (hd : ∀ i, ∃ z : ℕ → X, z 0 = d i ∧ z k = d 0 ∧ ∀ j < k, Adj (z j) (z (j + 1)))
    {S : Fin (2 ^ s) → Set Ω} (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (Disjoint on S)) (hprob : ∀ i, 2⁻¹ ≤ M (d i) (S i)) :
    Real.log 2 * (s - 1) ≤ ε * k := by
  have hN := (h.packing hd hS hdisj hprob).1
  have hlog := Real.log_le_log (by positivity) hN
  rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow] at hlog
  linarith

end CSLibExtTest.Crypto.Privacy.Packing
