/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary

/-! # Stationary path laws of finite continuous-time Markov chains -/

@[expose] public section

open Finset Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [DiscreteMeasurableSpace ι] {Q : Matrix ι ι ℝ}

omit [DecidableEq ι] [Fintype ι] in
private theorem measurable_path [Finite ι] (i : ι) :
    Measurable (fun ω => ctmcPath Q i ω : (ℕ → (ι → ι) × ℝ) → ℝ≥0 → ι) :=
  Measurable.of_eval fun t => measurable_ctmcPath i t

/-- Mix the path laws of a finite continuous-time Markov chain over its initial state.
The law started at `i` is the pushforward of the driving-step measure by `ctmcPath Q i`;
its coefficient is `ENNReal.ofReal (π i)`. If `π` is a probability vector, this mixture is a
probability measure. -/
noncomputable def ctmcPathMeasure (hQ : IsRateMatrix Q) (π : ι → ℝ) : Measure (ℝ≥0 → ι) :=
  Measure.sum fun i => ENNReal.ofReal (π i) •
    (ctmcInputMeasure hQ).map (fun ω => ctmcPath Q i ω)

private theorem pathMeasure_probability (hQ : IsRateMatrix Q) {π : ι → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1) :
    IsProbabilityMeasure (ctmcPathMeasure hQ π) := by
  constructor
  rw [ctmcPathMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp_rw [smul_apply, Measure.map_apply (measurable_path _) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ i), hsum, ENNReal.ofReal_one]

private theorem pathMeasure_real_apply (hQ : IsRateMatrix Q) {π : ι → ℝ}
    (hπ : ∀ i, 0 ≤ π i) {S : Set (ℝ≥0 → ι)} (hS : MeasurableSet S) :
    (ctmcPathMeasure hQ π).real S =
      ∑ i, π i * (ctmcInputMeasure hQ).real ((fun ω => ctmcPath Q i ω) ⁻¹' S) := by
  rw [measureReal_def, ctmcPathMeasure, Measure.sum_apply _ hS, tsum_fintype]
  simp_rw [smul_apply, Measure.map_apply (measurable_path _) hS, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top (ctmcInputMeasure hQ) _))]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hπ _), measureReal_def]

private theorem pathMeasure_real_fdd (hQ : IsRateMatrix Q) {π : ι → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hstat : π ᵥ* Q = 0) {n : ℕ}
    (s : Fin (n + 1) → ℝ≥0) (j : Fin (n + 1) → ι) :
    (ctmcPathMeasure hQ π).real {x | ∀ k, x (∑ l ∈ Iic k, s l) = j k} =
      π (j 0) * ∏ k : Fin n, ctmcTransition Q (s k.succ) (j k.castSucc) (j k.succ) := by
  let S : Set (ℝ≥0 → ι) := {x | ∀ k, x (∑ l ∈ Iic k, s l) = j k}
  have hS : MeasurableSet S := by
    dsimp [S]
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun (measurable_pi_apply _)
      measurable_const
  have hsplit (i : ι) :
      (ctmcInputMeasure hQ).real ((fun ω => ctmcPath Q i ω) ⁻¹' S) =
        ctmcTransition Q (s 0) i (j 0) *
          ∏ k : Fin n, ctmcTransition Q (s k.succ) (j k.castSucc) (j k.succ) := by
    change (ctmcInputMeasure hQ).real {ω | ∀ k, ctmcPath Q i ω (∑ l ∈ Iic k, s l) = j k} = _
    rw [hQ.ctmcInputMeasure_real_ctmcPath_fdd, Fin.prod_univ_succ]
    congr 1
  have hfirst : ∑ i, π i * ctmcTransition Q (s 0) i (j 0) = π (j 0) :=
    congrFun ((vecMul_eq_zero_iff_forall_vecMul_ctmcTransition π Q).mp hstat (s 0)) (j 0)
  change (ctmcPathMeasure hQ π).real S = _
  rw [pathMeasure_real_apply hQ hπ hS]
  simp_rw [hsplit, ← mul_assoc]
  rw [← sum_mul, hfirst]

private theorem shifted_prefix_eq {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (ht : Monotone t) (h : ℝ≥0) (k : Fin (n + 1)) :
    ∑ l ∈ Iic k, Fin.cons (t 0 + h) (fun j => t j.succ - t j.castSucc) l = t k + h := by
  induction k using Fin.induction with
  | zero =>
    have hzero : Iic (0 : Fin (n + 1)) = {0} := by ext l; simp
    simp [hzero]
  | succ j ih =>
    have herase : (Iic j.succ).erase j.succ = Iic j.castSucc := by
      ext l
      simp only [mem_erase, mem_Iic]
      change (l ≠ j.succ ∧ l.val ≤ j.val + 1) ↔ l.val ≤ j.val
      simp only [ne_eq, Fin.ext_iff, Fin.val_succ]
      omega
    rw [← add_sum_erase _ _ (mem_Iic.mpr le_rfl), herase, ih, Fin.cons_succ]
    rw [← add_assoc, tsub_add_cancel_of_le (ht (Fin.castSucc_le_succ j))]

/-- **A stationary initial law makes a finite continuous-time Markov chain stationary.**
Let `π` be a probability vector with `π Q = 0`. The mixture of the fixed-start path laws is a
probability measure, each one-time marginal has masses `π j`, and the joint probability of
any finite sequence of state observations at nondecreasing times is unchanged when all times
are shifted by the same nonnegative amount. This includes repeated times and the empty
sequence. See Sigman, *Continuous-Time Markov Chains*, §1.10, Proposition 1.2. -/
theorem ctmcPathMeasure_stationary (hQ : IsRateMatrix Q) {π : ι → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1) (hstat : π ᵥ* Q = 0) :
    IsProbabilityMeasure (ctmcPathMeasure hQ π) ∧
    (∀ (t : ℝ≥0) (j : ι), (ctmcPathMeasure hQ π).real {x | x t = j} = π j) ∧
    (∀ {n : ℕ} (t : Fin n → ℝ≥0), Monotone t → ∀ (j : Fin n → ι) (h : ℝ≥0),
      (ctmcPathMeasure hQ π).real {x | ∀ k, x (t k + h) = j k} =
        (ctmcPathMeasure hQ π).real {x | ∀ k, x (t k) = j k}) := by
  refine ⟨pathMeasure_probability hQ hπ hsum, ?_, ?_⟩
  · intro t j
    rw [pathMeasure_real_apply hQ hπ
      (measurableSet_eq_fun (measurable_pi_apply t) measurable_const)]
    change ∑ i, π i * (ctmcInputMeasure hQ).real {ω | ctmcPath Q i ω t = j} = π j
    simp_rw [hQ.ctmcInputMeasure_real_ctmcPath_eq]
    exact congrFun ((vecMul_eq_zero_iff_forall_vecMul_ctmcTransition π Q).mp hstat t) j
  · intro n t ht j h
    cases n with
    | zero => simp
    | succ n =>
      let s (h' : ℝ≥0) : Fin (n + 1) → ℝ≥0 :=
        Fin.cons (t 0 + h') (fun k => t k.succ - t k.castSucc)
      have ht' (h' : ℝ≥0) (k : Fin (n + 1)) : ∑ l ∈ Iic k, s h' l = t k + h' :=
        shifted_prefix_eq t ht h' k
      have hfd (h' : ℝ≥0) :
          (ctmcPathMeasure hQ π).real {x | ∀ k, x (t k + h') = j k} =
            π (j 0) * ∏ k : Fin n, ctmcTransition Q ((t k.succ - t k.castSucc : ℝ≥0) : ℝ)
              (j k.castSucc) (j k.succ) := by
        simpa only [ht', s, Fin.cons_succ] using pathMeasure_real_fdd hQ hπ hstat (s h') j
      simpa only [add_zero] using (hfd h).trans (hfd 0).symm

end ProbabilityTheory
