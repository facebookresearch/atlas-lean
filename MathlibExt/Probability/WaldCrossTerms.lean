/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Cross terms in Wald's second equation

When expanding the square of a stopped partial sum `S_T = ∑_{i < T} X_i`,
Wald's second equation splits into a diagonal part and a cross part:

`(∑_{i<T} X_i)² = ∑_{i<T} X_i² + 2 ∑_{i<T} ∑_{j<i} X_j · X_i`.

The diagonal part is Wald's equation applied to the squared sequence
`Y_i = X_i²` (batch 5's `wald_equation`, not re-proved here). This file
ports the cross part from v1: each individual cross term
`E[X_j · X_i · 1_{T > i}]` with `j < i` vanishes, and hence the total
cross-term contribution vanishes under the absolute-summability hypothesis
for the stopped cross-term series; summand measurability is derived internally.

## Source

This formalizes the cross-term lemmas of
`v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean`:
`cross_pair_integral_zero`, `wald_cross_terms_zero`, and
`sum_sq_expansion`, proved there. Batch 14 proved `wald_second_equation`
itself by a different route (Fatou + truncation) and ported none of these
three statements; they appear in no earlier batch's committed file, in
base `MathlibExt`, or in Mathlib.

## Scope

`MathlibExt/Probability/WaldDiagonalTerms.lean` provides the diagonal term
`wald_diagonal_terms` and the integrability lemma `integrable_stopped_sum_sq_diag`.
It applies the canonical `MeasureTheory.wald_equation` and
`MeasureTheory.wald_integrable_stopped_sum` from
`MathlibExt/Probability/WaldEquation.lean` to the squared sequence. These diagonal
APIs complement the cross-term results in this module and the existing
`MeasureTheory.wald_second_equation`.

The one place v1's `wald_cross_terms_zero` relies on a helper from
`WaldEquation.lean` (`sum_range_eq_tsum_ite`, which batch 5 carries as a
private lemma) is proved inline here as an unnamed `have`, and the one
place it relies on `measurable_of_isStoppingTime` is replaced by a
direct argument from `IsStoppingTime.measurableSet_gt`.

The total-cross-term APIs use canonical one-step adaptedness. Earlier-coordinate
measurability follows by filtration monotonicity, and v1's summand measurability
condition (`haesm`) follows from stopping-time measurability and coordinate
integrability. The general theorem retains only v1's absolute-summability
condition (`hsumm`) as extra analytic bookkeeping. The bounded theorem discharges
that remaining condition because the sums are finite and the terms vanish past
the bound. Batch 14's description notes that v1 left this bookkeeping undischarged.

## Main results

* `MathlibExt.Probability.WaldCrossTerms.cross_pair_integral_zero`:
  for identically distributed, mean-zero `X` and a stopping time `T`, with `X_i`
  independent of the filtration at time `i` and each `X_j` measurable
  with respect to the filtration at time `i > j`,
  `E[X_j · X_i · 1_{T > i}] = 0`.
* `MathlibExt.Probability.WaldCrossTerms.wald_cross_terms_zero`:
  the total cross-term contribution `E[∑_{i<T} ∑_{j<i} X_j · X_i]`
  vanishes under canonical one-step adaptedness and absolute summability;
  summand measurability is derived internally.
* `MathlibExt.Probability.WaldCrossTerms.wald_cross_terms_zero_of_bounded`:
  the same conclusion for a stopping time bounded by a constant, with
  no summability or measurability hypotheses.
* `MathlibExt.Probability.WaldCrossTerms.sum_sq_expansion`:
  the algebraic expansion of `(∑_{i<n} f i)²` into diagonal and
  cross terms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal

namespace MathlibExt.Probability.WaldCrossTerms

/-- A single cross term `E[X_j · X_i · 1_{T > i}]` (with `j < i`) vanishes
when the `X_i` are identically distributed with zero mean and `X_i` is independent of
`(X_j, 1_{T > i})`. -/
theorem cross_pair_integral_zero
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ j k, j < k → @Measurable Ω ℝ (f k) inferInstance (X j))
    (j i : ℕ) (hji : j < i) :
    ∫ ω, (if i < T ω then X j ω * X i ω else 0) ∂μ = 0 := by
  have h_eq : (fun ω => if i < T ω then X j ω * X i ω else 0) =
      fun ω => (X j ω * Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ)) ω) * X i ω := by
    ext ω; simp only [Set.indicator, Set.mem_ofPred_eq]; split_ifs <;> ring
  rw [h_eq]
  set g : Ω → ℝ := fun ω => X j ω * Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ)) ω
  have hind_meas : @MeasurableSet Ω (f i) {ω | i < T ω} := by
    have hset : {ω : Ω | i < T ω} = {ω : Ω | (i : WithTop ℕ) < (T ω : WithTop ℕ)} := by
      ext ω; simp
    rw [hset]; exact hT.measurableSet_gt i
  have hg_meas : @Measurable Ω ℝ (f i) inferInstance g :=
    (hadapt j i hji).mul (@Measurable.indicator Ω ℝ {ω | i < T ω} (fun _ => (1 : ℝ))
      (f i) inferInstance _ (@measurable_const ℝ Ω inferInstance (f i) (a := 1)) hind_meas)
  have hindep : IndepFun (X i) g μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (hXf i)
      (MeasurableSpace.comap_le_iff_le_map.mpr hg_meas.le_map)
  have hmean_i : ∫ ω, X i ω ∂μ = 0 := by rw [(hX_iid i 0).integral_eq]; exact hmean
  rw [hindep.symm.integral_fun_mul_eq_mul_integral
    (hg_meas.mono (f.le i) le_rfl).aestronglyMeasurable
    ((hX_iid i 0).integrable_iff.mpr hX_int).aestronglyMeasurable, hmean_i, mul_zero]

/-- The full cross-term contribution to `E[(S_T)^2]` vanishes:
`E[∑_{i < T} ∑_{j < i} X_j X_i] = 0` for identically distributed, mean-zero variables,
with each `X_i` independent of the filtration at time `i` and measurable at time
`i + 1`, given absolute summability of the stopped cross-term series. -/
theorem wald_cross_terms_zero
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (X k))
    (hsumm : ∑' n, ∫⁻ ω,
      ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ ≠ ⊤) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
      X j ω * X i ω) ∂μ = 0 := by
  have hadapt_past : ∀ j k, j < k → @Measurable Ω ℝ (f k) inferInstance (X j) :=
    fun j _ hjk => (hadapt j).mono (f.mono (Nat.succ_le_of_lt hjk)) le_rfl
  have hX_aesm : ∀ i, AEStronglyMeasurable (X i) μ :=
    fun i => ((hX_iid i 0).integrable_iff.mpr hX_int).aestronglyMeasurable
  have haesm : ∀ n, AEStronglyMeasurable
      (fun ω => if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0) μ := by
    intro n
    have hset : MeasurableSet {ω : Ω | n < T ω} := by
      have hsetEq : {ω : Ω | n < T ω} =
          {ω : Ω | (n : WithTop ℕ) < (T ω : WithTop ℕ)} := by
        ext ω
        simp
      rw [hsetEq]
      exact (f.le n) _ (hT.measurableSet_gt n)
    have h_ind_eq : (fun ω => if n < T ω then
        ∑ j ∈ Finset.range n, X j ω * X n ω else 0) =
        Set.indicator {ω | n < T ω} (fun ω => ∑ j ∈ Finset.range n, X j ω * X n ω) := by
      ext ω
      simp [Set.indicator, Set.mem_ofPred_eq]
    rw [h_ind_eq]
    apply AEStronglyMeasurable.indicator _ hset
    have hsum : (fun ω => ∑ j ∈ Finset.range n, X j ω * X n ω) =
        ∑ j ∈ Finset.range n, (fun ω => X j ω * X n ω) := by
      funext ω
      rw [Finset.sum_apply]
    rw [hsum]
    exact Finset.aestronglyMeasurable_sum _ (fun j _ => (hX_aesm j).mul (hX_aesm n))
  have h_eq : (fun ω => ∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
      X j ω * X i ω) =
      (fun ω => ∑' i, if i < T ω then ∑ j ∈ Finset.range i, X j ω * X i ω else 0) := by
    ext ω
    -- Inline form of the finite-sum-to-tsum identity (batch 5 carries it
    -- as a private lemma; it is not re-ported here).
    rw [tsum_eq_sum (s := Finset.range (T ω))]
    · exact Finset.sum_congr rfl (fun x hx => by simp [Finset.mem_range.mp hx])
    · intro i hi
      split_ifs with h
      · exact absurd h (Finset.mem_range.not.mp hi)
      · rfl
  rw [h_eq]
  rw [integral_tsum haesm hsumm]
  have each_zero : ∀ i, ∫ ω, (if i < T ω then ∑ j ∈ Finset.range i,
      X j ω * X i ω else 0) ∂μ = 0 := by
    intro i
    have h_dist : (fun ω => if i < T ω then ∑ j ∈ Finset.range i,
        X j ω * X i ω else 0) =
        (fun ω => ∑ j ∈ Finset.range i, if i < T ω then X j ω * X i ω else 0) := by
      ext ω; split_ifs <;> simp
    rw [h_dist, integral_finsetSum]
    · apply Finset.sum_eq_zero; intro j hj
      exact cross_pair_integral_zero hX_iid hX_int hmean hT hXf hadapt_past j i
        (Finset.mem_range.mp hj)
    · intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      have hj_int : Integrable (X j) μ := (hX_iid j 0).integrable_iff.mpr hX_int
      have hi_int : Integrable (X i) μ := (hX_iid i 0).integrable_iff.mpr hX_int
      have hindep : IndepFun (X i) (X j) μ := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right (hXf i)
          (MeasurableSpace.comap_le_iff_le_map.mpr (hadapt_past j i hji).le_map)
      have hprod : Integrable (fun ω => X j ω * X i ω) μ := by
        show Integrable (X j * X i) μ; exact hindep.symm.integrable_mul hj_int hi_int
      have h_eq_ind : (fun ω => if i < T ω then X j ω * X i ω else 0) =
          Set.indicator {ω | i < T ω} (fun ω => X j ω * X i ω) := by
        ext ω; simp [Set.indicator, Set.mem_ofPred_eq]
      rw [h_eq_ind]
      have hset : MeasurableSet {ω : Ω | i < T ω} := by
        have hsetEq : {ω : Ω | i < T ω} =
            {ω : Ω | (i : WithTop ℕ) < (T ω : WithTop ℕ)} := by
          ext ω; simp
        rw [hsetEq]
        exact (f.le i) _ (hT.measurableSet_gt i)
      exact hprod.indicator hset
  simp only [each_zero, tsum_zero]

/-- Algebraic identity expanding the square of a finite sum into diagonal and
cross-term contributions: `(∑_{i<n} f i)^2 = ∑_{i<n} (f i)^2 + 2 ∑_{i<n} ∑_{j<i} f j · f i`. -/
theorem sum_sq_expansion (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, f i) ^ 2 =
      ∑ i ∈ Finset.range n, (f i) ^ 2 +
        2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, f j * f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]; rw [add_sq', ih]
    have h1 : (2 * ∑ i ∈ Finset.range n, f i) * f n =
        2 * (∑ j ∈ Finset.range n, f j * f n) := by
      rw [mul_assoc]; congr 1; exact Finset.sum_mul (Finset.range n) f (f n)
    rw [h1]; linarith

/-- The total cross-term contribution vanishes for a stopping time bounded
by a constant, with no extra summability or measurability hypotheses:
the sums are finite, and every term past the bound is zero. -/
theorem wald_cross_terms_zero_of_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (X k))
    {N : ℕ} (hT_bdd : ∀ ω, T ω ≤ N) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
      X j ω * X i ω) ∂μ = 0 := by
  have hadapt_past : ∀ j k, j < k → @Measurable Ω ℝ (f k) inferInstance (X j) :=
    fun j _ hjk => (hadapt j).mono (f.mono (Nat.succ_le_of_lt hjk)) le_rfl
  have hset_meas : ∀ n, MeasurableSet {ω : Ω | n < T ω} := by
    intro n
    have hsetEq : {ω : Ω | n < T ω} =
        {ω : Ω | (n : WithTop ℕ) < (T ω : WithTop ℕ)} := by
      ext ω; simp
    rw [hsetEq]
    exact (f.le n) _ (hT.measurableSet_gt n)
  have hX_int_all : ∀ i, Integrable (X i) μ :=
    fun i => (hX_iid i 0).integrable_iff.mpr hX_int
  -- The `n`-th summand, written with an indicator.
  have h_ind_eq : ∀ n, (fun ω => if n < T ω then
      ∑ j ∈ Finset.range n, X j ω * X n ω else 0) =
      Set.indicator {ω | n < T ω}
        (fun ω => ∑ j ∈ Finset.range n, X j ω * X n ω) := by
    intro n; ext ω; simp [Set.indicator, Set.mem_ofPred_eq]
  have h_int_each : ∀ n, Integrable
      (fun ω => if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0) μ := by
    intro n
    rw [h_ind_eq n]
    apply Integrable.indicator _ (hset_meas n)
    apply integrable_finsetSum
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hindep : IndepFun (X n) (X j) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (hXf n)
        (MeasurableSpace.comap_le_iff_le_map.mpr (hadapt_past j n hjn).le_map)
    show Integrable (X j * X n) μ
    exact hindep.symm.integrable_mul (hX_int_all j) (hX_int_all n)
  have hsumm : ∑' n, ∫⁻ ω,
      ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ ≠ ⊤ := by
    have h_tsum_eq : (∑' n, ∫⁻ ω,
        ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ) =
        ∑ n ∈ Finset.range (N + 1), ∫⁻ ω,
          ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ := by
      apply tsum_eq_sum
      intro n hn
      have hnN : N < n := by
        have hnot : ¬ n < N + 1 := fun h => hn (Finset.mem_range.mpr h)
        omega
      have hf0 : ∀ ω, (if n < T ω then
          ∑ j ∈ Finset.range n, X j ω * X n ω else 0) = (0 : ℝ) := by
        intro ω
        split_ifs with h
        · exact absurd (lt_of_lt_of_le h (hT_bdd ω)) (not_lt.mpr hnN.le)
        · rfl
      simp only [hf0, enorm_zero, lintegral_zero]
    rw [h_tsum_eq]
    rw [ENNReal.sum_ne_top]
    intro n _
    exact (h_int_each n).hasFiniteIntegral.ne
  exact wald_cross_terms_zero hX_iid hX_int hmean hT hXf hadapt hsumm

end MathlibExt.Probability.WaldCrossTerms
