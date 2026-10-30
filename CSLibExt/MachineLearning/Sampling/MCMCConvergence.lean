/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.GibbsSampling
public import MathlibExt.Probability.FiniteMarkovChainConvergence

/-!
# Convergence of Metropolis–Hastings and Gibbs samplers on a finite state space

`MetropolisHastings.lean` and `GibbsSampling.lean` prove that the target `π` is stationary for
the Metropolis–Hastings step and for a systematic-scan Gibbs sweep. This file proves that the
chains **converge** to `π`: their transition matrices are primitive under the stated hypotheses,
so the convergence theorem `exists_tvDist_pow_le` (Levin, Peres and Wilmer, Theorem 4.9) applies.

## Main results

* `mhMatrix π Q`: the transition matrix `(x, y) ↦ P(x, y)` of the Metropolis–Hastings chain;
  `mhMatrix_mem_rowStochastic`, `vecMul_mhMatrix` (`π` is stationary).
* `isPrimitive_mhMatrix`: for a target with full support and a proposal `Q` whose transition
  matrix is primitive and whose support is symmetric (`Q x y ≠ 0 → Q y x ≠ 0`), the
  Metropolis–Hastings matrix is primitive. `exists_tvDist_mhMatrix_pow_le`: **the
  Metropolis–Hastings chain converges to `π`** geometrically fast in total variation.
* `gibbsSweepMatrix π hπ l`: the transition matrix of the systematic-scan Gibbs sweep along the
  list `l`; `gibbsSweepMatrix_pos`: if `l` visits every coordinate, every entry is positive.
  `exists_tvDist_gibbsSweepMatrix_pow_le`: **the systematic-scan Gibbs sampler converges to
  `π`** geometrically fast in total variation.

## References

* D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, 2nd ed., American
  Mathematical Society, 2017, Theorem 4.9.
* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004,
  Chapters 7 and 10.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.MarkovMixing MathlibExt.Probability.FiniteMarkovChainConvergence
open scoped ENNReal

/-- The probabilities of a law on a finite type, as reals, sum to `1`. -/
theorem sum_toReal_pmf {β : Type*} [Fintype β] (π : PMF β) : ∑ y, (π y).toReal = 1 := by
  have h : ∑ y, π y = 1 := by simpa [tsum_fintype] using π.tsum_coe
  rw [← ENNReal.toReal_sum fun y _ => PMF.apply_ne_top π y, h, ENNReal.toReal_one]

section MetropolisHastings

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The transition matrix `P(x, y) = mhStep π Q x y` of the Metropolis–Hastings chain, as a real
matrix. -/
noncomputable def mhMatrix (π : PMF α) (Q : α → PMF α) : Matrix α α ℝ :=
  Matrix.of fun x y => (mhStep π Q x y).toReal

/-- The Metropolis–Hastings matrix is stochastic. -/
theorem mhMatrix_mem_rowStochastic (π : PMF α) (Q : α → PMF α) :
    mhMatrix π Q ∈ rowStochastic ℝ α :=
  mem_rowStochastic_iff_sum.2 ⟨fun _ _ => ENNReal.toReal_nonneg, fun _ => sum_toReal_pmf _⟩

omit [DecidableEq α] in
/-- The target is stationary for the Metropolis–Hastings matrix. -/
theorem vecMul_mhMatrix (π : PMF α) (Q : α → PMF α) :
    (fun x => (π x).toReal) ᵥ* mhMatrix π Q = fun x => (π x).toReal := by
  funext y
  have h := congrArg (fun p : PMF α => p y) (bind_mhStep π Q)
  simp only [PMF.bind_apply, tsum_fintype] at h
  simp only [vecMul, dotProduct, mhMatrix, Matrix.of_apply]
  rw [← h, ENNReal.toReal_sum fun x _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top π x) (PMF.apply_ne_top _ y)]
  simp only [ENNReal.toReal_mul]

/-- Entries of powers of an entrywise nonnegative matrix are nonnegative. -/
private theorem pow_apply_nonneg {β : Type*} [Fintype β] [DecidableEq β] {A : Matrix β β ℝ}
    (hA : ∀ x y, 0 ≤ A x y) (k : ℕ) (x y : β) : 0 ≤ (A ^ k) x y := by
  induction k generalizing y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (hA z y)

/-- If the positive entries of a nonnegative matrix `A` are positive entries of a nonnegative
matrix `B`, the same holds for all their powers. -/
private theorem pow_apply_pos_of_pattern {β : Type*} [Fintype β] [DecidableEq β]
    {A B : Matrix β β ℝ} (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (hAB : ∀ x y, 0 < A x y → 0 < B x y) (k : ℕ) (x y : β) (h : 0 < (A ^ k) x y) :
    0 < (B ^ k) x y := by
  induction k generalizing y with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply] at h ⊢
    obtain ⟨z, -, hz⟩ : ∃ z ∈ Finset.univ, 0 < (A ^ k) x z * A z y := by
      by_contra hc
      push Not at hc
      exact absurd (Finset.sum_nonpos hc) (not_le.mpr h)
    have h1 : 0 < (A ^ k) x z := pos_of_mul_pos_left hz (hA z y)
    have h2 : 0 < A z y := pos_of_mul_pos_right hz (pow_apply_nonneg hA k x z)
    exact Finset.sum_pos' (fun w _ => mul_nonneg (pow_apply_nonneg hB k x w) (hB w y))
      ⟨z, Finset.mem_univ _, mul_pos (ih z h1) (hAB z y h2)⟩

/-- For a target with full support and a proposal with primitive transition matrix and symmetric
support, the Metropolis–Hastings matrix is primitive. -/
theorem isPrimitive_mhMatrix {π : PMF α} (hπ : ∀ x, π x ≠ 0) {Q : α → PMF α}
    (hQs : ∀ x y, Q x y ≠ 0 → Q y x ≠ 0)
    (hQp : (Matrix.of fun x y => (Q x y).toReal).IsPrimitive) :
    (mhMatrix π Q).IsPrimitive := by
  have hpat : ∀ x y, 0 < (Q x y).toReal → 0 < mhMatrix π Q x y := by
    intro x y hxy
    have hQ : Q x y ≠ 0 := fun h => by simp [h] at hxy
    simp only [mhMatrix, Matrix.of_apply]
    refine ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _)
    by_cases hxy' : x = y
    · subst hxy'
      have hle : Q x x * 1 ≤ mhStep π Q x x := by
        rw [mhStep, PMF.bind_apply]
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum x)
        congr 1
        have : (fun b : Bool => cond b x x) = Function.const Bool x := by
          funext b; cases b <;> rfl
        rw [this, PMF.map_const, PMF.pure_apply]
        simp
      rw [mul_one] at hle
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hQ) hle).ne'
    · rw [mhStep_apply_of_ne hxy']
      refine mul_ne_zero hQ ?_
      rw [mhAccept]
      refine (lt_min one_pos ?_).ne'
      exact ENNReal.div_pos (mul_ne_zero (hπ y) (hQs x y hQ))
        (ENNReal.mul_ne_top (PMF.apply_ne_top π x) (PMF.apply_ne_top _ _))
  obtain ⟨hQn, k, hk, hQk⟩ := hQp
  have hMn : ∀ x y, 0 ≤ mhMatrix π Q x y := fun _ _ => ENNReal.toReal_nonneg
  exact ⟨hMn, k, hk, fun x y => pow_apply_pos_of_pattern hQn hMn hpat k x y (hQk x y)⟩

/-- **The Metropolis–Hastings chain converges to its target**: under the hypotheses of
`isPrimitive_mhMatrix`, there are `C` and `0 ≤ ρ < 1` with `d_TV(Pⁿ(x, ·), π) ≤ C ρⁿ` for every
start `x`. -/
theorem exists_tvDist_mhMatrix_pow_le {π : PMF α} (hπ : ∀ x, π x ≠ 0) {Q : α → PMF α}
    (hQs : ∀ x y, Q x y ≠ 0 → Q y x ≠ 0)
    (hQp : (Matrix.of fun x y => (Q x y).toReal).IsPrimitive) :
    ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : α),
      tvDist (fun y => (mhMatrix π Q ^ n) x y) (fun y => (π y).toReal) ≤ C * ρ ^ n :=
  exists_tvDist_pow_le (mhMatrix_mem_rowStochastic π Q) (isPrimitive_mhMatrix hπ hQs hQp)
    (fun _ => ENNReal.toReal_nonneg) (sum_toReal_pmf π) (vecMul_mhMatrix π Q)

end MetropolisHastings

section Gibbs

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The transition matrix `P(x, y) = gibbsSweep π hπ l x {y}` of the systematic-scan Gibbs
sweep along `l`, as a real matrix. -/
noncomputable def gibbsSweepMatrix (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (l : List ι) :
    Matrix (ι → S) (ι → S) ℝ :=
  Matrix.of fun x y => (gibbsSweep π hπ l x {y}).toReal

/-- The Gibbs sweep matrix is stochastic. -/
theorem gibbsSweepMatrix_mem_rowStochastic (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (l : List ι) :
    gibbsSweepMatrix π hπ l ∈ rowStochastic ℝ (ι → S) := by
  refine mem_rowStochastic_iff_sum.2 ⟨fun _ _ => ENNReal.toReal_nonneg, fun x => ?_⟩
  simp only [gibbsSweepMatrix, Matrix.of_apply]
  rw [← ENNReal.toReal_sum fun _ _ => measure_ne_top _ _, sum_measure_singleton,
    Finset.coe_univ, measure_univ, ENNReal.toReal_one]

omit [DecidableEq S] in
/-- The target is stationary for the Gibbs sweep matrix. -/
theorem vecMul_gibbsSweepMatrix (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (l : List ι) :
    (fun x => (π x).toReal) ᵥ* gibbsSweepMatrix π hπ l = fun x => (π x).toReal := by
  funext y
  have h : (π.toMeasure.bind (gibbsSweep π hπ l)) {y} = π.toMeasure {y} := by
    rw [(invariant_gibbsSweep π hπ l).def]
  rw [Measure.bind_apply (measurableSet_singleton y)
    (gibbsSweep π hπ l).measurable.aemeasurable, lintegral_fintype,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)] at h
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  simp only [vecMul, dotProduct, gibbsSweepMatrix, Matrix.of_apply]
  rw [← h, ENNReal.toReal_sum fun x _ =>
    ENNReal.mul_ne_top (measure_ne_top _ _) (PMF.apply_ne_top π x)]
  simp only [ENNReal.toReal_mul, mul_comm]

omit [DecidableEq S] in
/-- If the sweep visits every coordinate, every transition probability of the sweep is
positive. -/
theorem gibbsSweepMatrix_pos (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) {l : List ι}
    (hl : ∀ i, i ∈ l) (x y : ι → S) : 0 < gibbsSweepMatrix π hπ l x y := by
  classical
  have key : ∀ (l : List ι) (x : ι → S),
      0 < gibbsSweep π hπ l x {fun j => if j ∈ l then y j else x j} := by
    intro l
    induction l with
    | nil =>
      intro x
      simp [gibbsSweep, ProbabilityTheory.Kernel.id_apply]
    | cons i l ih =>
      intro x
      set x' := Function.update x i (y i)
      have hz : (fun j => if j ∈ i :: l then y j else x j) =
          fun j => if j ∈ l then y j else x' j := by
        funext j
        by_cases hjl : j ∈ l
        · simp [hjl]
        · by_cases hji : j = i
          · subst hji; simp [x']
          · simp [hjl, hji, x']
      rw [hz, gibbsSweep_cons_apply, Measure.bind_apply (measurableSet_singleton _)
        (gibbsSweep π hπ l).measurable.aemeasurable, lintegral_fintype]
      have hstep : 0 < gibbsStep π hπ i x x' := by
        rw [gibbsStep_apply, ite_eq_left_of_eq_true _ _ (eq_true (by simp [x']))]
        exact ENNReal.div_pos (hπ x') (condNorm_ne_top π i x)
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => zero_le)
        (Finset.mem_univ x'))
      rw [pmfKernel_apply, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      exact ENNReal.mul_pos (ih x').ne' hstep.ne'
  have hy : (fun j => if j ∈ l then y j else x j) = y := by
    funext j; simp [hl j]
  have := key l x
  rw [hy] at this
  exact ENNReal.toReal_pos this.ne' (measure_ne_top _ _)

/-- **The systematic-scan Gibbs sampler converges to its target**: if the sweep visits every
coordinate, there are `C` and `0 ≤ ρ < 1` with `d_TV(Pⁿ(x, ·), π) ≤ C ρⁿ` for every start `x`. -/
theorem exists_tvDist_gibbsSweepMatrix_pow_le (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0)
    {l : List ι} (hl : ∀ i, i ∈ l) :
    ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : ι → S),
      tvDist (fun y => (gibbsSweepMatrix π hπ l ^ n) x y) (fun y => (π y).toReal) ≤
        C * ρ ^ n := by
  refine exists_tvDist_pow_le (gibbsSweepMatrix_mem_rowStochastic π hπ l) ?_
    (fun _ => ENNReal.toReal_nonneg) (sum_toReal_pmf π) (vecMul_gibbsSweepMatrix π hπ l)
  exact ⟨fun x y => (gibbsSweepMatrix_pos π hπ hl x y).le, 1, one_pos,
    fun x y => by simpa using gibbsSweepMatrix_pos π hπ hl x y⟩

end Gibbs

end Cslib.MachineLearning.Sampling
