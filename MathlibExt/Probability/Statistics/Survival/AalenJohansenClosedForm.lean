/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenCLT
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Closed-form Greenwood and Aalen–Johansen covariance entries

The fixed-grid joint central limit theorem `AalenJohansenCLT.tendstoInDistribution_estimator`
identifies the asymptotic covariance of the joint Kaplan–Meier / Aalen–Johansen estimator as the
covariance of the influence vector `influence μ m w = fderiv (ajMap m) (cellMean μ) (cellVector w)`
of one subject (`AalenJohansenCLT.covariance_limit`). This file evaluates that covariance in
closed form.

Write `e_{l,c} = P(X = l, δ = 1, J = c)`, `d_l = ∑_c e_{l,c}` and `y_l = P(X ≥ l)` for the
coordinates of the mean cell vector `cellMean μ` (`X = min T C`, `δ = 1[T ≤ C]`),
`λ_{l,c} = e_{l,c} / y_l`, `S(j)` the product-limit survival, `S(l-)` the survival just before
`l`, and `F_c(j)` the Aalen–Johansen cumulative incidence of the mean cell vector.

## Main definitions

* `cellIncrement u v l c = v_{l,c} - λ_{l,c} v_l`: for `v = cellVector w` the one-subject
  increment `1[X = l, δ = 1, J = c] - λ_{l,c} 1[X ≥ l]`.
* `kmCoeff`, `ajCoeff`, `influenceCoeff`: the coefficients of the derivative of `ajMap` in these
  increments; `survivalBefore` and `cumIncidence` give `S(l-)` and `F_c(l)` at every grid index.
* `incrementCov u γ γ'`: the Gram form
  `∑_l (∑_c γ_{l,c} γ'_{l,c} e_{l,c} - (∑_c γ_{l,c} e_{l,c}) (∑_c γ'_{l,c} e_{l,c}) / y_l)`.

## Main results

* `fderiv_ajMap_apply`: the derivative of `ajMap m` is
  `v ↦ ∑_{l,c} influenceCoeff u m a l c · cellIncrement u v l c`.
* `covariance_incrementSum`: increment sums of one subject have covariance `incrementCov`
  (increments at distinct grid indices are uncorrelated; at one index they are multinomial).
* `covariance_influence_eq_incrementCov`, `covariance_limit_eq_incrementCov`: **all entries** of
  the influence covariance and of the covariance of the Gaussian limit, in closed form.
* `covariance_influence_km`, `covariance_limit_km`: **Greenwood's formula**
  `Cov(S(j), S(j')) = S(j) S(j') ∑_{l ≤ j ∧ j'} d_l / (y_l (y_l - d_l))`.
* `covariance_influence_aj`: the **Aalen–Johansen covariance**
  `Cov(F_c(j), F_{c'}(j')) = ∑_{l ≤ j ∧ j'} [ΔF_c ΔF_{c'} d_l / (y_l (y_l - d_l))
    - ΔF_c S(l-) e_{l,c'} / y_l² - ΔF_{c'} S(l-) e_{l,c} / y_l²
    + S(l-)² ([c = c'] e_{l,c} y_l - e_{l,c} e_{l,c'}) / y_l³]`, with `ΔF_c = F_c(j) - F_c(l)`.
* `covariance_influence_km_aj`: the cross entry
  `Cov(S(j), F_c(j')) = S(j) ∑_{l ≤ j ∧ j'} [(F_c(j') - F_c(l)) d_l / (y_l (y_l - d_l))
    - S(l-) e_{l,c} / y_l²]`.

## Scope

Fixed grid and horizon `m` with `P(X ≥ m) ≠ 0`, the hypotheses of the merged joint CLT. The
general closed form `covariance_influence_eq_incrementCov` needs nothing more. The explicit
entry formulas assume `d_l ≠ y_l` at the grid indices `l ≤ j ∧ j'` they sum over, the domain of
the textbook denominators `y_l - d_l`. For `l < m` this is automatic
(`sum_cellMean_inl_ne_inr_of_lt`: `y_l - d_l ≥ P(X ≥ m) > 0`), so the hypothesis only binds at
`l = j = j' = m`. These are population (asymptotic) covariances at the mean
cell vector; the plug-in identification of Greenwood's data *estimate*
`KaplanMeier.CensoredData.greenwoodVariance` with `n⁻¹` times this formula at the empirical cell
means is not stated here.

## References

Bibliographic details and section/theorem numbers below are as recalled and have not been
checked against the printed sources (no page numbers are given); read them as "cf.".

* cf. M. Greenwood, *The natural duration of cancer*, Reports on Public Health and Medical
  Subjects 33, HMSO, London (1926).
* cf. O. O. Aalen and S. Johansen, *An empirical transition matrix for non-homogeneous Markov
  chains based on censored observations*, Scand. J. Statist. 5 (1978), 141–150.
* cf. P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section IV.3 (Kaplan–Meier, Greenwood's formula) and Section IV.4
  (Aalen–Johansen, asymptotic covariance).
* cf. A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 3.1 (delta method).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AalenJohansenClosedForm

open MeasureTheory ProbabilityTheory Filter Finset Topology
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.AalenJohansenCLT

variable {k r : ℕ}

/-- The cause-`c` ratio `u_{l,c} / u_l` of a cell vector `u` at grid index `l`; at the mean cell
vector it is the observable cause-specific hazard `P(X = l, δ = 1, J = c) / P(X ≥ l)`. -/
noncomputable def cellRatio (u : EuclideanSpace ℝ (Cell k r)) (l : Fin k) (c : Fin r) : ℝ :=
  u (Sum.inl (l, c)) / u (Sum.inr l)

/-- The cause-`c` increment `v_{l,c} - (u_{l,c} / u_l) v_l` of a cell vector `v` at grid index `l`,
centred by the ratios of `u`. For `v = cellVector w` it is the one-subject martingale increment
`1[X = l, δ = 1, J = c] - λ_{l,c} 1[X ≥ l]`. -/
noncomputable def cellIncrement (u v : EuclideanSpace ℝ (Cell k r)) (l : Fin k) (c : Fin r) :
    ℝ :=
  v (Sum.inl (l, c)) - cellRatio u l c * v (Sum.inr l)

private lemma hasDerivAt_line (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- The derivative of one Kaplan–Meier factor along the line `u + t v` at `t = 0`. -/
theorem hasDerivAt_factor_line {u : EuclideanSpace ℝ (Cell k r)} {l : Fin k}
    (hl : u (Sum.inr l) ≠ 0) (v : EuclideanSpace ℝ (Cell k r)) :
    HasDerivAt (fun t : ℝ => factor (u + t • v) l)
      (-(∑ c, cellIncrement u v l c) / u (Sum.inr l)) 0 := by
  have hN : HasDerivAt (fun t : ℝ => ∑ c, (u (Sum.inl (l, c)) + t * v (Sum.inl (l, c))))
      (∑ c, v (Sum.inl (l, c))) 0 :=
    HasDerivAt.fun_sum fun c _ => hasDerivAt_line _ _
  have h := (hN.div (hasDerivAt_line (u (Sum.inr l)) (v (Sum.inr l))) (by simpa using hl)).const_sub
    1
  simp only [factor, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  convert h using 1
  simp only [zero_mul, add_zero, cellIncrement, cellRatio, sum_sub_distrib, ← sum_mul, ← sum_div]
  field_simp

/-- The derivative of one Aalen–Johansen ratio `u_{l,c} / u_l` along the line `u + t v` at
`t = 0`. -/
theorem hasDerivAt_ratio_line {u : EuclideanSpace ℝ (Cell k r)} {l : Fin k}
    (hl : u (Sum.inr l) ≠ 0) (v : EuclideanSpace ℝ (Cell k r)) (c : Fin r) :
    HasDerivAt (fun t : ℝ => (u + t • v) (Sum.inl (l, c)) / (u + t • v) (Sum.inr l))
      (cellIncrement u v l c / u (Sum.inr l)) 0 := by
  have h := (hasDerivAt_line (u (Sum.inl (l, c))) (v (Sum.inl (l, c)))).div
    (hasDerivAt_line (u (Sum.inr l)) (v (Sum.inr l))) (by simpa using hl)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  convert h using 1
  simp only [zero_mul, add_zero, cellIncrement, cellRatio]
  field_simp

/-! ### The derivative of the Aalen–Johansen map in increment coordinates -/

/-- The **Kaplan–Meier influence coefficient** at grid index `l` for the survival at `j`:
`-(∏_{i ≤ j, i ≠ l} factor u i) / u_l` for `l ≤ j`, and `0` for `l > j`. When the factor at
`l` is nonzero it is `-S(j) / (u_l (1 - h_l))` (`kmCoeff_eq`). -/
noncomputable def kmCoeff (u : EuclideanSpace ℝ (Cell k r)) (j l : Fin k) : ℝ :=
  if l ≤ j then -(∏ i ∈ (univ.filter (· ≤ j)).erase l, factor u i) / u (Sum.inr l) else 0

/-- The **Aalen–Johansen influence coefficient** of the cause-`c'` increment at grid index `l` for
the cumulative incidence of cause `c` at `j`:
`([l ≤ j, c' = c] S(l-) - ∑_{l < l' ≤ j} (∏_{i < l', i ≠ l} factor u i) λ_{l',c}) / u_l`.
When the factor at `l ≤ j` is nonzero the sum is `(F_c(j) - F_c(l)) / (1 - h_l)` (`ajCoeff_eq`). -/
noncomputable def ajCoeff (u : EuclideanSpace ℝ (Cell k r)) (j : Fin k) (c : Fin r) (l : Fin k)
    (c' : Fin r) : ℝ :=
  (if l ≤ j ∧ c' = c then (∏ i ∈ univ.filter (· < l), factor u i) / u (Sum.inr l) else 0) -
    (∑ l' ∈ univ.filter (fun l' => l' ≤ j ∧ l < l'),
      (∏ i ∈ (univ.filter (· < l')).erase l, factor u i) * cellRatio u l' c) / u (Sum.inr l)

/-- The **influence coefficients** of the joint estimator coordinate `a`: the derivative of
`ajMap m` at `u` is `v ↦ ∑_{l, c'} influenceCoeff u m a l c' · cellIncrement u v l c'`
(`fderiv_ajMap_apply`). -/
noncomputable def influenceCoeff (u : EuclideanSpace ℝ (Cell k r)) (m : Fin k) :
    Coord k r m → Fin k → Fin r → ℝ
  | (none, j) => fun l _ => kmCoeff u j.1 l
  | (some c, j) => ajCoeff u j.1 c

/-- The coordinate `a` of the derivative of `ajMap m` is the derivative along lines. -/
theorem fderiv_ajMap_apply_of_hasDerivAt {m : Fin k} {u : EuclideanSpace ℝ (Cell k r)}
    (hu : ∀ l ≤ m, u (Sum.inr l) ≠ 0) (v : EuclideanSpace ℝ (Cell k r)) (a : Coord k r m)
    {g : ℝ → ℝ} {d : ℝ} (hg : ∀ t : ℝ, ajMap m (u + t • v) a = g t) (h : HasDerivAt g d 0) :
    fderiv ℝ (ajMap m) u v a = d := by
  have h' : HasDerivAt (fun t : ℝ => ajMap m (u + t • v) a) d 0 := by
    simpa only [hg] using h
  have hg : HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hL := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (differentiableAt_ajMap m hu).hasFDerivAt hg
    (by simp)
  exact ((hasDerivAt_pi.1 hL) a).unique h'

/-- **The derivative of the Aalen–Johansen map in increment coordinates.** If the at-risk
coordinates of `u` up to the horizon are nonzero, every coordinate of the derivative of `ajMap m`
at `u` is a linear combination of the cause-specific increments `cellIncrement u v l c'`, with
the coefficients `influenceCoeff u m a l c'`. -/
theorem fderiv_ajMap_apply {m : Fin k} {u : EuclideanSpace ℝ (Cell k r)}
    (hu : ∀ l ≤ m, u (Sum.inr l) ≠ 0) (v : EuclideanSpace ℝ (Cell k r)) (a : Coord k r m) :
    fderiv ℝ (ajMap m) u v a =
      ∑ l, ∑ c', influenceCoeff u m a l c' * cellIncrement u v l c' := by
  classical
  have hF : ∀ l ≤ m, HasDerivAt (fun t : ℝ => factor (u + t • v) l)
      (-(∑ c, cellIncrement u v l c) / u (Sum.inr l)) 0 := fun l hl =>
    hasDerivAt_factor_line (hu l hl) v
  rcases a with ⟨_ | c, j⟩
  · have h := HasDerivAt.fun_finsetProd (u := univ.filter (· ≤ j.1)) (x := (0 : ℝ))
      (f := fun l t => factor (u + t • v) l) fun l hl =>
        hF l (le_trans (mem_filter.1 hl).2 j.2)
    rw [fderiv_ajMap_apply_of_hasDerivAt hu v (none, j) (fun t => rfl) h]
    simp only [zero_smul, add_zero, smul_eq_mul, influenceCoeff, kmCoeff]
    rw [sum_filter]
    refine sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [← mul_sum]
      ring
    · simp
  · have hjm : ∀ l ∈ univ.filter (· ≤ j.1), l ≤ m := fun l hl =>
      le_trans (mem_filter.1 hl).2 j.2
    have h := HasDerivAt.fun_sum (u := univ.filter (· ≤ j.1)) (x := (0 : ℝ)) fun l hl =>
      (HasDerivAt.fun_finsetProd (u := univ.filter (· < l)) (x := (0 : ℝ))
        (f := fun i t => factor (u + t • v) i) fun i hi =>
          hF i (le_trans (mem_filter.1 hi).2.le (hjm l hl))).mul
        (hasDerivAt_ratio_line (hu l (hjm l hl)) v c)
    rw [fderiv_ajMap_apply_of_hasDerivAt hu v (some c, j) (fun t => rfl) h]
    simp only [zero_smul, add_zero, smul_eq_mul, influenceCoeff, ajCoeff, sub_mul,
      sum_sub_distrib, sum_add_distrib]
    -- the direct `S(l-)` part
    have h1 : ∑ l, ∑ c', (if l ≤ j.1 ∧ c' = c then
          (∏ i ∈ univ.filter (· < l), factor u i) / u (Sum.inr l) else 0) *
          cellIncrement u v l c' =
        ∑ l ∈ univ.filter (· ≤ j.1),
          (∏ i ∈ univ.filter (· < l), factor u i) * (cellIncrement u v l c / u (Sum.inr l)) := by
      rw [sum_filter]
      refine sum_congr rfl fun l _ => ?_
      by_cases hl : l ≤ j.1
      · simp only [hl, true_and, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
        ring
      · simp [hl]
    -- the part through the earlier Kaplan–Meier factors, after exchanging the two sums
    have h2 : ∑ l, ∑ c', (∑ l' ∈ univ.filter (fun l' => l' ≤ j.1 ∧ l < l'),
          (∏ i ∈ (univ.filter (· < l')).erase l, factor u i) * cellRatio u l' c) /
            u (Sum.inr l) * cellIncrement u v l c' =
        -∑ l ∈ univ.filter (· ≤ j.1), (∑ i ∈ univ.filter (· < l),
          (∏ i' ∈ (univ.filter (· < l)).erase i, factor u i') *
            (-(∑ c', cellIncrement u v i c') / u (Sum.inr i))) *
          ((u (Sum.inl (l, c))) / u (Sum.inr l)) := by
      simp only [sum_mul, sum_div, ← sum_neg_distrib]
      rw [sum_comm' (t' := univ) (s' := fun i => univ.filter (fun l => l ≤ j.1 ∧ i < l))
        (fun l i => by simp)]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun l _ => ?_
      rw [← mul_sum]
      simp only [neg_div, sum_neg_distrib, ← sum_div, cellRatio]
      ring
    rw [h1, h2]
    ring

/-! ### The covariance of increment sums -/

/-- The **increment Gram form** of two coefficient arrays `γ, γ'` at a cell vector `u`:
`∑_l (∑_c γ_{l,c} γ'_{l,c} u_{l,c} - (∑_c γ_{l,c} u_{l,c}) (∑_c γ'_{l,c} u_{l,c}) / u_l)`. At the
mean cell vector it is the covariance of the two increment sums of one subject
(`covariance_incrementSum`): the increments at distinct grid indices are uncorrelated, and at one
grid index they have the multinomial covariance. -/
noncomputable def incrementCov (u : EuclideanSpace ℝ (Cell k r)) (γ γ' : Fin k → Fin r → ℝ) :
    ℝ :=
  ∑ l, (∑ c, γ l c * γ' l c * u (Sum.inl (l, c)) -
    (∑ c, γ l c * u (Sum.inl (l, c))) * (∑ c, γ' l c * u (Sum.inl (l, c))) / u (Sum.inr l))

section Gram

variable {μ : Measure ((Fin k × Fin r) × Fin k)}

private lemma cellVector_inl (w : (Fin k × Fin r) × Fin k) (j : Fin k) (c : Fin r) :
    cellVector w (Sum.inl (j, c)) =
      if min w.1.1 w.2 = j ∧ w.1.1 ≤ w.2 ∧ w.1.2 = c then 1 else 0 := rfl

private lemma cellVector_inr (w : (Fin k × Fin r) × Fin k) (j : Fin k) :
    cellVector w (Sum.inr j) = if j ≤ min w.1.1 w.2 then 1 else 0 := rfl

/-- At the mean cell vector the ratio times the at-risk mass is the event mass,
`λ_{l,c} P(X ≥ l) = P(X = l, δ = 1, J = c)`, also when `P(X ≥ l) = 0` (then both masses are `0`). -/
theorem cellRatio_mul_cellMean [IsFiniteMeasure μ] (l : Fin k) (c : Fin r) :
    cellRatio (cellMean μ) l c * cellMean μ (Sum.inr l) = cellMean μ (Sum.inl (l, c)) := by
  simp only [cellRatio]
  by_cases hy : cellMean μ (Sum.inr l) = 0
  · have hle : causeEventMass μ l c ≤ causeAtRiskMass μ l :=
      measureReal_mono (μ := μ) fun w hw => hw.1.symm.le
    have h0 : 0 ≤ causeEventMass μ l c := measureReal_nonneg
    change causeAtRiskMass μ l = 0 at hy
    change causeEventMass μ l c / causeAtRiskMass μ l * causeAtRiskMass μ l = causeEventMass μ l c
    rw [hy] at hle ⊢
    simp only [div_zero, zero_mul]
    linarith
  · field_simp

private lemma integral_cellVector_apply [IsProbabilityMeasure μ] (i : Cell k r) :
    ∫ w, cellVector w i ∂μ = cellMean μ i := by
  have h : ∫ w, cellVector w ∂μ = cellMean μ := integral_cellVector (Y := id) HasLaw.id
  rw [← h]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (Integrable.of_finite (μ := μ) (f := fun w => cellVector (k := k) (r := r) w))

private lemma integral_linear [IsProbabilityMeasure μ] (l : Fin k) (α : Fin r → ℝ) (β : ℝ) :
    ∫ w, (∑ c, α c * cellVector w (Sum.inl (l, c)) + β * cellVector w (Sum.inr l)) ∂μ =
      ∑ c, α c * cellMean μ (Sum.inl (l, c)) + β * cellMean μ (Sum.inr l) := by
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_finsetSum _ fun c _ => Integrable.of_finite]
  simp only [integral_const_mul, integral_cellVector_apply]

/-- The increment sum of one subject `w` at grid index `l` with coefficients `γ`. -/
private noncomputable def incr (u : EuclideanSpace ℝ (Cell k r)) (γ : Fin k → Fin r → ℝ)
    (l : Fin k) (w : (Fin k × Fin r) × Fin k) : ℝ :=
  ∑ c, γ l c * cellIncrement u (cellVector w) l c

private lemma incr_eq (u : EuclideanSpace ℝ (Cell k r)) (γ : Fin k → Fin r → ℝ) (l : Fin k)
    (w : (Fin k × Fin r) × Fin k) :
    incr u γ l w = ∑ c, γ l c * cellVector w (Sum.inl (l, c)) +
      (-∑ c, γ l c * cellRatio u l c) * cellVector w (Sum.inr l) := by
  simp only [incr, cellIncrement, mul_sub, sum_sub_distrib, neg_mul, sum_mul]
  simp only [mul_assoc, sub_eq_add_neg]

private lemma incr_mul_incr_of_lt (u : EuclideanSpace ℝ (Cell k r)) (γ γ' : Fin k → Fin r → ℝ)
    {l l' : Fin k} (hll : l < l') (w : (Fin k × Fin r) × Fin k) :
    incr u γ l w * incr u γ' l' w = (-∑ c, γ l c * cellRatio u l c) * incr u γ' l' w := by
  by_cases h : l' ≤ min w.1.1 w.2
  · congr 1
    have h1 : ¬ (min w.1.1 w.2 = l) := fun he => (not_le.2 hll) (he ▸ h)
    have h2 : l ≤ min w.1.1 w.2 := hll.le.trans h
    simp [incr_eq, cellVector_inl, cellVector_inr, h1, h2]
  · have h0 : incr u γ' l' w = 0 := by
      have h1 : ¬ (min w.1.1 w.2 = l') := fun he => h he.symm.le
      simp [incr_eq, cellVector_inl, cellVector_inr, h1, h]
    rw [h0, mul_zero, mul_zero]

private lemma incr_mul_incr_self (u : EuclideanSpace ℝ (Cell k r)) (γ γ' : Fin k → Fin r → ℝ)
    (l : Fin k) (w : (Fin k × Fin r) × Fin k) :
    incr u γ l w * incr u γ' l w =
      ∑ c, (γ l c * γ' l c - (∑ c, γ' l c * cellRatio u l c) * γ l c -
          (∑ c, γ l c * cellRatio u l c) * γ' l c) * cellVector w (Sum.inl (l, c)) +
        ((∑ c, γ l c * cellRatio u l c) * (∑ c, γ' l c * cellRatio u l c)) *
          cellVector w (Sum.inr l) := by
  simp only [incr_eq, cellVector_inl, cellVector_inr]
  by_cases h0 : min w.1.1 w.2 = l ∧ w.1.1 ≤ w.2
  · have h2 : l ≤ min w.1.1 w.2 := h0.1.symm.le
    simp only [h0.1, h0.2, true_and, le_refl, ite_true, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ]
    ring
  · have h1 : ∀ c, ¬ (min w.1.1 w.2 = l ∧ w.1.1 ≤ w.2 ∧ w.1.2 = c) := fun c hc =>
      h0 ⟨hc.1, hc.2.1⟩
    simp only [h1, ite_false, mul_zero, sum_const_zero, zero_add]
    split_ifs <;> ring

/-- **Covariance of increment sums.** For one subject `w` with law `μ`, the increment sums
`∑_{l, c} γ_{l,c} N_{l,c}(w)` and `∑_{l, c} γ'_{l,c} N_{l,c}(w)`, where
`N_{l,c}(w) = 1[X = l, δ = 1, J = c] - λ_{l,c} 1[X ≥ l]` is the one-subject increment centred at
the mean cell vector, have covariance `incrementCov (cellMean μ) γ γ'`. The increments at
distinct grid indices are uncorrelated (`X ≥ l'` forces `X ≠ l` and `X ≥ l` when `l < l'`), and
at one grid index they have the multinomial covariance
`e_{l,c} 1[c = c'] - e_{l,c} e_{l,c'} / y_l`. -/
theorem covariance_incrementSum [IsProbabilityMeasure μ] (γ γ' : Fin k → Fin r → ℝ) :
    cov[fun w => ∑ l, ∑ c, γ l c * cellIncrement (cellMean μ) (cellVector w) l c,
      fun w => ∑ l, ∑ c, γ' l c * cellIncrement (cellMean μ) (cellVector w) l c; μ] =
      incrementCov (cellMean μ) γ γ' := by
  classical
  change cov[fun w => ∑ l, incr (cellMean μ) γ l w,
    fun w => ∑ l, incr (cellMean μ) γ' l w; μ] = _
  have hsum : ∀ (γ : Fin k → Fin r → ℝ) l, ∑ c, γ l c * cellMean μ (Sum.inl (l, c)) =
      (∑ c, γ l c * cellRatio (cellMean μ) l c) * cellMean μ (Sum.inr l) := fun γ l => by
    simp only [sum_mul, mul_assoc, cellRatio_mul_cellMean]
  have hmean : ∀ (γ : Fin k → Fin r → ℝ) l, ∫ w, incr (cellMean μ) γ l w ∂μ = 0 := by
    intro γ l
    simp_rw [incr_eq]
    rw [integral_linear, hsum]
    ring
  have hcross : ∀ l l', ∫ w, incr (cellMean μ) γ l w * incr (cellMean μ) γ' l' w ∂μ =
      if l = l' then ∑ c, γ l c * γ' l c * cellMean μ (Sum.inl (l, c)) -
        (∑ c, γ l c * cellMean μ (Sum.inl (l, c))) *
          (∑ c, γ' l c * cellMean μ (Sum.inl (l, c))) / cellMean μ (Sum.inr l) else 0 := by
    intro l l'
    rcases lt_trichotomy l l' with h | rfl | h
    · simp_rw [incr_mul_incr_of_lt _ _ _ h]
      rw [integral_const_mul, hmean, mul_zero]
      simp [h.ne]
    · simp_rw [incr_mul_incr_self]
      rw [integral_linear, ite_true]
      have hlin : ∑ c, (γ l c * γ' l c - (∑ c, γ' l c * cellRatio (cellMean μ) l c) * γ l c -
          (∑ c, γ l c * cellRatio (cellMean μ) l c) * γ' l c) * cellMean μ (Sum.inl (l, c)) =
          ∑ c, γ l c * γ' l c * cellMean μ (Sum.inl (l, c)) -
            (∑ c, γ' l c * cellRatio (cellMean μ) l c) *
              ∑ c, γ l c * cellMean μ (Sum.inl (l, c)) -
            (∑ c, γ l c * cellRatio (cellMean μ) l c) *
              ∑ c, γ' l c * cellMean μ (Sum.inl (l, c)) := by
        simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      rw [hlin, hsum γ, hsum γ']
      by_cases hy : cellMean μ (Sum.inr l) = 0
      · simp [hy]
      · field_simp
        ring
    · simp_rw [mul_comm (incr (cellMean μ) γ l _), incr_mul_incr_of_lt _ _ _ h]
      rw [integral_const_mul, hmean, mul_zero]
      simp [h.ne']
  rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete,
    integral_finsetSum _ fun l _ => Integrable.of_finite]
  simp only [hmean, sum_const_zero, zero_mul, sub_zero, Pi.mul_apply, sum_mul_sum]
  rw [integral_finsetSum _ fun l _ => Integrable.of_finite]
  simp only [integral_finsetSum _ fun _ _ => Integrable.of_finite, hcross, sum_ite_eq, mem_univ,
    ite_true]
  rfl

end Gram

/-! ### The influence coefficients when every factor is nonzero -/

/-- The product-limit survival just before grid index `l`, `S(l-) = ∏_{i < l} factor u i`. -/
noncomputable def survivalBefore (u : EuclideanSpace ℝ (Cell k r)) (l : Fin k) : ℝ :=
  ∏ i ∈ univ.filter (· < l), factor u i

/-- The Aalen–Johansen cumulative incidence of cause `c` at any grid index `j`,
`F_c(j) = ∑_{l ≤ j} S(l-) λ_{l,c}`; up to the horizon it is the coordinate `(some c, j)` of
`ajMap` (`ajMap_some_eq_cumIncidence`). -/
noncomputable def cumIncidence (u : EuclideanSpace ℝ (Cell k r)) (c : Fin r) (j : Fin k) : ℝ :=
  ∑ l ∈ univ.filter (· ≤ j), survivalBefore u l * cellRatio u l c

/-- The cause-`c` coordinate of `ajMap` is `cumIncidence`. -/
theorem ajMap_some_eq_cumIncidence {m : Fin k} (u : EuclideanSpace ℝ (Cell k r)) (c : Fin r)
    (j : {j : Fin k // j ≤ m}) : ajMap m u (some c, j) = cumIncidence u c j.1 := rfl

/-- The Kaplan–Meier coordinate of `ajMap` is the product of the factors up to `j`. -/
theorem ajMap_none_eq {m : Fin k} (u : EuclideanSpace ℝ (Cell k r)) (j : {j : Fin k // j ≤ m}) :
    ajMap m u (none, j) = ∏ i ∈ univ.filter (· ≤ j.1), factor u i := rfl

/-- The Kaplan–Meier influence coefficient when the factor at `l ≤ j` is nonzero:
`-S(j) / ((1 - h_l) u_l)`. -/
theorem kmCoeff_eq {u : EuclideanSpace ℝ (Cell k r)} {j l : Fin k} (hl : l ≤ j)
    (hf : factor u l ≠ 0) :
    kmCoeff u j l = -(∏ i ∈ univ.filter (· ≤ j), factor u i) / (factor u l * u (Sum.inr l)) := by
  have hmem : l ∈ univ.filter (· ≤ j) := by simpa using hl
  simp only [kmCoeff, hl, ite_true]
  rw [← prod_erase_mul _ _ hmem]
  by_cases hy : u (Sum.inr l) = 0
  · simp [hy]
  · field_simp

/-- The Kaplan–Meier influence coefficient vanishes beyond `j`. -/
theorem kmCoeff_of_not_le {u : EuclideanSpace ℝ (Cell k r)} {j l : Fin k} (hl : ¬ l ≤ j) :
    kmCoeff u j l = 0 := by
  simp [kmCoeff, hl]

/-- The Aalen–Johansen influence coefficient vanishes beyond `j`. -/
theorem ajCoeff_of_not_le {u : EuclideanSpace ℝ (Cell k r)} {j l : Fin k} (hl : ¬ l ≤ j)
    (c c' : Fin r) : ajCoeff u j c l c' = 0 := by
  have h0 : univ.filter (fun l' => l' ≤ j ∧ l < l') = ∅ := by
    ext l'
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
    exact fun h1 h2 => hl (h2.le.trans h1)
  simp [ajCoeff, hl, h0]

/-- The cumulative incidence accrued after `l`: for `l ≤ j`,
`F_c(j) - F_c(l) = ∑_{l < l' ≤ j} S(l'-) λ_{l',c}`. -/
theorem cumIncidence_sub_cumIncidence (u : EuclideanSpace ℝ (Cell k r)) (c : Fin r)
    {j l : Fin k} (hl : l ≤ j) :
    cumIncidence u c j - cumIncidence u c l =
      ∑ l' ∈ univ.filter (fun l' => l' ≤ j ∧ l < l'), survivalBefore u l' * cellRatio u l' c := by
  rw [cumIncidence, ← sum_filter_add_sum_filter_not _ (· ≤ l), filter_filter, filter_filter,
    cumIncidence]
  have h1 : univ.filter (fun l' => l' ≤ j ∧ l' ≤ l) = univ.filter (· ≤ l) := by
    ext l'
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hl, h⟩⟩
  have h2 : univ.filter (fun l' => l' ≤ j ∧ ¬ l' ≤ l) =
      univ.filter (fun l' => l' ≤ j ∧ l < l') := by
    ext l'
    simp only [mem_filter, mem_univ, true_and, not_le]
  rw [h1, h2]
  ring

/-- The Aalen–Johansen influence coefficient when the factor at `l ≤ j` is nonzero:
`[c' = c] S(l-) / u_l - (F_c(j) - F_c(l)) / ((1 - h_l) u_l)`. -/
theorem ajCoeff_eq {u : EuclideanSpace ℝ (Cell k r)} {j l : Fin k} (hl : l ≤ j)
    (hf : factor u l ≠ 0) (c c' : Fin r) :
    ajCoeff u j c l c' = (if c' = c then survivalBefore u l / u (Sum.inr l) else 0) -
      (cumIncidence u c j - cumIncidence u c l) / (factor u l * u (Sum.inr l)) := by
  have hprod : ∀ l' ∈ univ.filter (fun l' => l' ≤ j ∧ l < l'),
      (∏ i ∈ (univ.filter (· < l')).erase l, factor u i) * cellRatio u l' c =
        survivalBefore u l' * cellRatio u l' c / factor u l := fun l' hl' => by
    have hmem : l ∈ univ.filter (· < l') := by simpa using (mem_filter.1 hl').2.2
    rw [survivalBefore, ← prod_erase_mul _ _ hmem]
    field_simp
  rw [ajCoeff, sum_congr rfl hprod, ← sum_div, ← cumIncidence_sub_cumIncidence u c hl]
  by_cases hc : c' = c
  · simp only [hl, hc, and_self, ite_true]
    rw [div_div]
    rfl
  · simp only [hc, and_false, ite_false]
    rw [div_div]

/-! ### The covariance of the influence vector -/

section Influence

variable {μ : Measure ((Fin k × Fin r) × Fin k)}

/-- **Closed form of the influence covariance, all entries.** For a subject law `μ` with
`P(min T C ≥ m) ≠ 0`, the covariance of two coordinates `a, b` of the influence vector of one
subject is the increment Gram form of their influence coefficients at the mean cell vector. -/
theorem covariance_influence_eq_incrementCov [IsProbabilityMeasure μ] (m : Fin k)
    (hm : causeAtRiskMass μ m ≠ 0) (a b : Coord k r m) :
    cov[fun w => influence μ m w a, fun w => influence μ m w b; μ] =
      incrementCov (cellMean μ) (influenceCoeff (cellMean μ) m a)
        (influenceCoeff (cellMean μ) m b) := by
  have hu : ∀ l ≤ m, cellMean μ (Sum.inr l) ≠ 0 := fun l hl =>
    causeAtRiskMass_ne_zero_of_le hl hm
  simp only [influence, fderiv_ajMap_apply hu]
  exact covariance_incrementSum _ _

/-- **Closed form of the influence covariance under the subject law of a sample.** If `W 0` has
law `μ` under `P`, the covariance of the influence coordinates `a, b` of `W 0` is the increment
Gram form `incrementCov` of the influence coefficients at the mean cell vector. -/
theorem covariance_influence_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W₀ : Ω → (Fin k × Fin r) × Fin k} (hW : HasLaw W₀ μ P) (m : Fin k)
    (hm : causeAtRiskMass μ m ≠ 0) (a b : Coord k r m) :
    cov[fun ω => influence μ m (W₀ ω) a, fun ω => influence μ m (W₀ ω) b; P] =
      incrementCov (cellMean μ) (influenceCoeff (cellMean μ) m a)
        (influenceCoeff (cellMean μ) m b) := by
  have : IsProbabilityMeasure μ := hW.isProbabilityMeasure_iff.1 inferInstance
  rw [hW.covariance_fun_comp (f := fun w => influence μ m w a)
    (g := fun w => influence μ m w b) Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  exact covariance_influence_eq_incrementCov m hm a b

/-- **Closed-form covariance of the joint Gaussian limit.** If `Y` is the limit vector of the
joint Kaplan–Meier and Aalen–Johansen central limit theorem (`tendstoInDistribution_estimator`),
then for all coordinates `a, b`, `Cov(Yₐ, Y_b)` is the increment Gram form of the influence
coefficients at the mean cell vector. -/
theorem covariance_limit_eq_incrementCov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℕ → Ω → (Fin k × Fin r) × Fin k} (hW : HasLaw (W 0) μ P)
    (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    {Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ}
    (hY : ∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
      (gaussianReal 0 (Var[fun ω => ∑ a, s a * influence μ m (W 0 ω) a; P]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell k r)))) (a b : Coord k r m) :
    cov[fun z => Y z a, fun z => Y z b; stdGaussian (EuclideanSpace ℝ (Cell k r))] =
      incrementCov (cellMean μ) (influenceCoeff (cellMean μ) m a)
        (influenceCoeff (cellMean μ) m b) :=
  (covariance_limit m hY hW.aemeasurable a b).trans (covariance_influence_comp hW m hm a b)

private lemma gram_summand (e α α' : Fin r → ℝ) (B B' y : ℝ) :
    ∑ x, (α x - B) * (α' x - B') * e x -
        (∑ x, (α x - B) * e x) * (∑ x, (α' x - B') * e x) / y =
      ∑ x, α x * α' x * e x - B' * ∑ x, α x * e x - B * ∑ x, α' x * e x +
        B * B' * ∑ x, e x -
        (∑ x, α x * e x - B * ∑ x, e x) * (∑ x, α' x * e x - B' * ∑ x, e x) / y := by
  have h1 : ∑ x, (α x - B) * (α' x - B') * e x = ∑ x, α x * α' x * e x -
      B' * ∑ x, α x * e x - B * ∑ x, α' x * e x + B * B' * ∑ x, e x := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  have h2 : ∀ (β : Fin r → ℝ) (C : ℝ), ∑ x, (β x - C) * e x = ∑ x, β x * e x - C * ∑ x, e x :=
    fun β C => by
      simp only [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
  rw [h1, h2, h2]

/-- **The textbook denominator is positive before the horizon.** If `P(X ≥ m) ≠ 0` and `l < m`,
then `d_l ≠ y_l`: indeed `y_l - d_l = P(X > l) + P(X = l, δ = 0) ≥ P(X ≥ m) > 0`. This discharges
the hypothesis `hd` of `covariance_influence_km`, `covariance_influence_aj` and
`covariance_influence_km_aj` at every summed index `l < m`. -/
theorem sum_cellMean_inl_ne_inr_of_lt [IsFiniteMeasure μ] {l m : Fin k} (hlm : l < m)
    (hm : causeAtRiskMass μ m ≠ 0) :
    ∑ c, cellMean μ (Sum.inl (l, c)) ≠ cellMean μ (Sum.inr l) := by
  classical
  intro h
  change ∑ c, causeEventMass μ l c = causeAtRiskMass μ l at h
  set D : Set ((Fin k × Fin r) × Fin k) := {ω | min ω.1.1 ω.2 = l ∧ ω.1.1 ≤ ω.2}
  set B : Set ((Fin k × Fin r) × Fin k) := {ω | m ≤ min ω.1.1 ω.2}
  have hD : ∑ c, causeEventMass μ l c = μ.real D := by
    have : D = ⋃ c ∈ (univ : Finset (Fin r)),
        {ω : (Fin k × Fin r) × Fin k | min ω.1.1 ω.2 = l ∧ ω.1.1 ≤ ω.2 ∧ ω.1.2 = c} := by
      ext ω; simp [D]
    rw [this, measureReal_biUnion_finset]
    · rfl
    · intro c _ c' _ hcc'
      exact Set.disjoint_left.2 fun ω h1 h2 => hcc' (h1.2.2.symm.trans h2.2.2)
    · intro c _; exact MeasurableSet.of_discrete
  have hdisj : Disjoint D B := Set.disjoint_left.2 fun ω h1 h2 =>
    absurd (h1.1 ▸ h2 : m ≤ l) (not_le.2 hlm)
  have hsub : D ∪ B ⊆ {ω | l ≤ min ω.1.1 ω.2} := by
    rintro ω (h1 | h2)
    · exact h1.1.symm.le
    · exact hlm.le.trans h2
  have h1 := measureReal_union (μ := μ) hdisj MeasurableSet.of_discrete
  have h2 := measureReal_mono (μ := μ) hsub
  have h3 : (0 : ℝ) ≤ μ.real B := measureReal_nonneg
  have h4 : μ.real B ≠ 0 := hm
  rw [h1] at h2
  change μ.real D + μ.real B ≤ causeAtRiskMass μ l at h2
  rw [← h, hD] at h2
  linarith [lt_of_le_of_ne h3 (Ne.symm h4)]

private lemma factor_cellMean_eq [IsFiniteMeasure μ] {l : Fin k}
    (hy : cellMean μ (Sum.inr l) ≠ 0) :
    factor (cellMean μ) l = (cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c))) /
      cellMean μ (Sum.inr l) := by
  rw [factor]
  field_simp

/-- **Greenwood's formula for the asymptotic covariance of Kaplan–Meier.** With
`d_l = P(X = l, δ = 1)` and `y_l = P(X ≥ l)` the observed event and at-risk masses, and
`d_l ≠ y_l` at every `l ≤ j ∧ j'`, the influence covariance of the Kaplan–Meier coordinates at
`j, j' ≤ m` is `S(j) S(j') ∑_{l ≤ j ∧ j'} d_l / (y_l (y_l - d_l))`. -/
theorem covariance_influence_km [IsProbabilityMeasure μ] (m : Fin k)
    (hm : causeAtRiskMass μ m ≠ 0) (j j' : {j : Fin k // j ≤ m})
    (hd : ∀ l, l ≤ j.1 → l ≤ j'.1 →
      ∑ c, cellMean μ (Sum.inl (l, c)) ≠ cellMean μ (Sum.inr l)) :
    cov[fun w => influence μ m w (none, j), fun w => influence μ m w (none, j'); μ] =
      ajMap m (cellMean μ) (none, j) * ajMap m (cellMean μ) (none, j') *
        ∑ l ∈ univ.filter (fun l => l ≤ j.1 ∧ l ≤ j'.1),
          (∑ c, cellMean μ (Sum.inl (l, c))) / (cellMean μ (Sum.inr l) *
            (cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)))) := by
  rw [covariance_influence_eq_incrementCov m hm, incrementCov, mul_sum, sum_filter]
  refine sum_congr rfl fun l _ => ?_
  simp only [influenceCoeff]
  by_cases hl : l ≤ j.1 ∧ l ≤ j'.1
  · have hy : cellMean μ (Sum.inr l) ≠ 0 := causeAtRiskMass_ne_zero_of_le (hl.1.trans j.2) hm
    have hyd : cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)) ≠ 0 :=
      sub_ne_zero.2 (hd l hl.1 hl.2).symm
    have hf : factor (cellMean μ) l ≠ 0 := by
      rw [factor_cellMean_eq hy]
      exact div_ne_zero hyd hy
    simp only [hl, and_self, ite_true]
    rw [kmCoeff_eq hl.1 hf, kmCoeff_eq hl.2 hf, ← mul_sum, ← mul_sum, ← mul_sum,
      factor_cellMean_eq hy, ajMap_none_eq, ajMap_none_eq]
    field_simp
  · simp only [hl, ite_false]
    rcases not_and_or.1 hl with h | h
    · simp [kmCoeff_of_not_le h]
    · simp [kmCoeff_of_not_le h]

/-- **Closed-form asymptotic covariance of two Aalen–Johansen cumulative incidences.** With
`e_{l,c} = P(X = l, δ = 1, J = c)`, `d_l = ∑_c e_{l,c}`, `y_l = P(X ≥ l)`, `S(l-)` the
product-limit survival before `l` and `F_c` the Aalen–Johansen cumulative incidences of the mean
cell vector, and `d_l ≠ y_l` at every `l ≤ j ∧ j'`, the influence covariance of the coordinates
`F_c(j)` and `F_{c'}(j')` is
`∑_{l ≤ j ∧ j'} [(F_c(j) - F_c(l)) (F_{c'}(j') - F_{c'}(l)) d_l / (y_l (y_l - d_l))
  - (F_c(j) - F_c(l)) S(l-) e_{l,c'} / y_l² - (F_{c'}(j') - F_{c'}(l)) S(l-) e_{l,c} / y_l²
  + S(l-)² ([c = c'] e_{l,c} y_l - e_{l,c} e_{l,c'}) / y_l³]`. -/
theorem covariance_influence_aj [IsProbabilityMeasure μ] (m : Fin k)
    (hm : causeAtRiskMass μ m ≠ 0) (c c' : Fin r) (j j' : {j : Fin k // j ≤ m})
    (hd : ∀ l, l ≤ j.1 → l ≤ j'.1 →
      ∑ c, cellMean μ (Sum.inl (l, c)) ≠ cellMean μ (Sum.inr l)) :
    cov[fun w => influence μ m w (some c, j), fun w => influence μ m w (some c', j'); μ] =
      ∑ l ∈ univ.filter (fun l => l ≤ j.1 ∧ l ≤ j'.1),
        ((cumIncidence (cellMean μ) c j.1 - cumIncidence (cellMean μ) c l) *
            (cumIncidence (cellMean μ) c' j'.1 - cumIncidence (cellMean μ) c' l) *
            (∑ c, cellMean μ (Sum.inl (l, c))) / (cellMean μ (Sum.inr l) *
              (cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)))) -
          (cumIncidence (cellMean μ) c j.1 - cumIncidence (cellMean μ) c l) *
            survivalBefore (cellMean μ) l * cellMean μ (Sum.inl (l, c')) /
              cellMean μ (Sum.inr l) ^ 2 -
          (cumIncidence (cellMean μ) c' j'.1 - cumIncidence (cellMean μ) c' l) *
            survivalBefore (cellMean μ) l * cellMean μ (Sum.inl (l, c)) /
              cellMean μ (Sum.inr l) ^ 2 +
          survivalBefore (cellMean μ) l ^ 2 *
            ((if c = c' then cellMean μ (Sum.inl (l, c)) else 0) * cellMean μ (Sum.inr l) -
              cellMean μ (Sum.inl (l, c)) * cellMean μ (Sum.inl (l, c'))) /
            cellMean μ (Sum.inr l) ^ 3) := by
  rw [covariance_influence_eq_incrementCov m hm, incrementCov, sum_filter]
  refine sum_congr rfl fun l _ => ?_
  simp only [influenceCoeff]
  by_cases hl : l ≤ j.1 ∧ l ≤ j'.1
  · have hy : cellMean μ (Sum.inr l) ≠ 0 := causeAtRiskMass_ne_zero_of_le (hl.1.trans j.2) hm
    have hyd : cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)) ≠ 0 :=
      sub_ne_zero.2 (hd l hl.1 hl.2).symm
    have hf : factor (cellMean μ) l ≠ 0 := by
      rw [factor_cellMean_eq hy]
      exact div_ne_zero hyd hy
    simp only [hl, and_self, ite_true]
    simp_rw [ajCoeff_eq hl.1 hf c, ajCoeff_eq hl.2 hf c']
    rw [gram_summand (fun x => cellMean μ (Sum.inl (l, x)))
      (fun x => if x = c then survivalBefore (cellMean μ) l / cellMean μ (Sum.inr l) else 0)
      (fun x => if x = c' then survivalBefore (cellMean μ) l / cellMean μ (Sum.inr l) else 0)]
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    rw [factor_cellMean_eq hy]
    by_cases hc : c = c'
    · subst hc
      simp only [ite_true]
      field_simp
      ring
    · simp only [hc, ite_false]
      field_simp
      ring
  · simp only [hl, ite_false]
    rcases not_and_or.1 hl with h | h
    · simp [ajCoeff_of_not_le h]
    · simp [ajCoeff_of_not_le h]

/-- **Closed-form asymptotic covariance of Kaplan–Meier with an Aalen–Johansen cumulative
incidence.** In the notation of `covariance_influence_aj`, with `d_l ≠ y_l` at every
`l ≤ j ∧ j'`, the influence covariance of `S(j)` and `F_c(j')` is
`S(j) ∑_{l ≤ j ∧ j'} [(F_c(j') - F_c(l)) d_l / (y_l (y_l - d_l)) - S(l-) e_{l,c} / y_l²]`. -/
theorem covariance_influence_km_aj [IsProbabilityMeasure μ] (m : Fin k)
    (hm : causeAtRiskMass μ m ≠ 0) (c : Fin r) (j j' : {j : Fin k // j ≤ m})
    (hd : ∀ l, l ≤ j.1 → l ≤ j'.1 →
      ∑ c, cellMean μ (Sum.inl (l, c)) ≠ cellMean μ (Sum.inr l)) :
    cov[fun w => influence μ m w (none, j), fun w => influence μ m w (some c, j'); μ] =
      ajMap m (cellMean μ) (none, j) *
        ∑ l ∈ univ.filter (fun l => l ≤ j.1 ∧ l ≤ j'.1),
          ((cumIncidence (cellMean μ) c j'.1 - cumIncidence (cellMean μ) c l) *
              (∑ c, cellMean μ (Sum.inl (l, c))) / (cellMean μ (Sum.inr l) *
                (cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)))) -
            survivalBefore (cellMean μ) l * cellMean μ (Sum.inl (l, c)) /
              cellMean μ (Sum.inr l) ^ 2) := by
  rw [covariance_influence_eq_incrementCov m hm, incrementCov, mul_sum, sum_filter]
  refine sum_congr rfl fun l _ => ?_
  simp only [influenceCoeff]
  by_cases hl : l ≤ j.1 ∧ l ≤ j'.1
  · have hy : cellMean μ (Sum.inr l) ≠ 0 := causeAtRiskMass_ne_zero_of_le (hl.1.trans j.2) hm
    have hyd : cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)) ≠ 0 :=
      sub_ne_zero.2 (hd l hl.1 hl.2).symm
    have hf : factor (cellMean μ) l ≠ 0 := by
      rw [factor_cellMean_eq hy]
      exact div_ne_zero hyd hy
    simp only [hl, and_self, ite_true]
    have hk : kmCoeff (cellMean μ) j.1 l = 0 - (∏ i ∈ univ.filter (· ≤ j.1),
        factor (cellMean μ) i) / (factor (cellMean μ) l * cellMean μ (Sum.inr l)) := by
      rw [kmCoeff_eq hl.1 hf]
      ring
    simp_rw [hk, ajCoeff_eq hl.2 hf c]
    rw [gram_summand (fun x => cellMean μ (Sum.inl (l, x))) (fun _ => 0)
      (fun x => if x = c then survivalBefore (cellMean μ) l / cellMean μ (Sum.inr l) else 0)]
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, sum_const_zero, mul_zero,
      sub_zero, zero_sub]
    rw [factor_cellMean_eq hy, ajMap_none_eq]
    field_simp
    ring
  · simp only [hl, ite_false]
    rcases not_and_or.1 hl with h | h
    · simp [kmCoeff_of_not_le h]
    · simp [ajCoeff_of_not_le h]

/-- The covariance of two coordinates of the joint Gaussian limit `Y` (as produced by
`tendstoInDistribution_estimator`) is the influence covariance under the subject law `μ`; the
entry theorems `covariance_influence_km`, `covariance_influence_aj` and
`covariance_influence_km_aj` then give it in closed form. -/
theorem covariance_limit_eq_covariance_influence {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : ℕ → Ω → (Fin k × Fin r) × Fin k}
    (hW : HasLaw (W 0) μ P) (m : Fin k) {Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ}
    (hY : ∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
      (gaussianReal 0 (Var[fun ω => ∑ a, s a * influence μ m (W 0 ω) a; P]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell k r)))) (a b : Coord k r m) :
    cov[fun z => Y z a, fun z => Y z b; stdGaussian (EuclideanSpace ℝ (Cell k r))] =
      cov[fun w => influence μ m w a, fun w => influence μ m w b; μ] := by
  rw [covariance_limit m hY hW.aemeasurable a b]
  exact hW.covariance_fun_comp (f := fun w => influence μ m w a)
    (g := fun w => influence μ m w b) Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable

/-- **Greenwood's formula for the joint Gaussian limit.** If `Y` is the limit vector of the joint
Kaplan–Meier and Aalen–Johansen central limit theorem for i.i.d. subjects with law `μ`
(`tendstoInDistribution_estimator`), and `d_l ≠ y_l` at every `l ≤ j ∧ j'`, then
`Cov(Y_{S(j)}, Y_{S(j')}) = S(j) S(j') ∑_{l ≤ j ∧ j'} d_l / (y_l (y_l - d_l))`; for `j = j'` this
is Greenwood's asymptotic variance `S(j)² ∑_{l ≤ j} d_l / (y_l (y_l - d_l))`. -/
theorem covariance_limit_km {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℕ → Ω → (Fin k × Fin r) × Fin k} (hW : HasLaw (W 0) μ P)
    (m : Fin k) (hm : causeAtRiskMass μ m ≠ 0)
    {Y : EuclideanSpace ℝ (Cell k r) → Coord k r m → ℝ}
    (hY : ∀ s : Coord k r m → ℝ, HasLaw (fun z => ∑ a, s a * Y z a)
      (gaussianReal 0 (Var[fun ω => ∑ a, s a * influence μ m (W 0 ω) a; P]).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Cell k r)))) (j j' : {j : Fin k // j ≤ m})
    (hd : ∀ l, l ≤ j.1 → l ≤ j'.1 →
      ∑ c, cellMean μ (Sum.inl (l, c)) ≠ cellMean μ (Sum.inr l)) :
    cov[fun z => Y z (none, j), fun z => Y z (none, j');
        stdGaussian (EuclideanSpace ℝ (Cell k r))] =
      ajMap m (cellMean μ) (none, j) * ajMap m (cellMean μ) (none, j') *
        ∑ l ∈ univ.filter (fun l => l ≤ j.1 ∧ l ≤ j'.1),
          (∑ c, cellMean μ (Sum.inl (l, c))) / (cellMean μ (Sum.inr l) *
            (cellMean μ (Sum.inr l) - ∑ c, cellMean μ (Sum.inl (l, c)))) := by
  have : IsProbabilityMeasure μ := hW.isProbabilityMeasure_iff.1 inferInstance
  rw [covariance_limit_eq_covariance_influence hW m hY]
  exact covariance_influence_km m hm j j' hd

end Influence

end MathlibExt.Probability.Statistics.AalenJohansenClosedForm
