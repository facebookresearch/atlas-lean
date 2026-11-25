/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# De Moivre–Laplace limit theorem

If `X₁, X₂, …` are independent identically distributed `{0, 1}`-valued
random variables with mean `p ∈ (0, 1)` and `Sₙ = X₁ + ⋯ + Xₙ`, then the
standardized sums `(Sₙ − np) / √(np(1 − p))` converge in distribution to the
standard normal law, and in particular, for `a ≤ b`,
`P{a ≤ (Sₙ − np) / √(np(1 − p)) ≤ b} → Φ(b) − Φ(a)`, where the right-hand
side is the standard normal mass of `[a, b]`.

## Source

This formalizes the target "Theorem (DeMoivre-Laplace limit theorem)"
(Lecture 12) of `v1/Atlas/TheoryOfProbability/targets.yaml`: "Let `Xᵢ` be
i.i.d. random variables. Write `Sₙ = ∑_{i=1}^n Xᵢ`. Suppose each `Xᵢ` is `1`
with probability `p` and `0` with probability `q = 1 − p`. Then
`lim_{n→∞} P{a ≤ (Sₙ − np)/√(npq) ≤ b} → Φ(b) − Φ(a)`." Its v1
formalization is `v1/Atlas/TheoryOfProbability/code/DeMoivreLaplace.lean`
(`deMoivreLaplace_clt`), proved there by a direct characteristic-function
computation for the binomial law.

## Relation to Mathlib

Mathlib has the general central limit theorem
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`) but no
De Moivre–Laplace theorem: a search for `DeMoivre` / `deMoivre` in Mathlib
finds only De Moivre's formula for complex numbers, and a search in
MathlibExt finds nothing. The proof here is therefore *not* a port of the
v1 characteristic-function argument: `{0, 1}`-valued variables have
`E[X₀²] = E[X₀]`, so the rescaled variables `(Xᵢ − p)/√(p(1 − p))` have
mean `0` and second moment `1`, and the theorem follows directly from
Mathlib's central limit theorem. The interval form is the Portmanteau
theorem applied to `[a, b]`, whose boundary `{a, b}` has standard normal
mass `0`.

## Main results

* `ProbabilityTheory.deMoivreLaplace_tendstoInDistribution`: convergence
  in distribution of the standardized sums to the standard normal.
* `ProbabilityTheory.deMoivreLaplace_interval_probability`: the book's
  interval form, `P{a ≤ (Sₙ − np)/√(np(1 − p)) ≤ b} → (gaussianReal 0 1)[a, b]`.

## Proof outline

Standardize: `(Xᵢ − p)/√(p(1 − p))` is i.i.d. with mean `0` and second
moment `1` (using `X₀² = X₀` a.e.). Apply Mathlib's CLT, then rewrite
`(√n)⁻¹ ∑_{k<n} (Xₖ − p)/√(p(1 − p))` as `(Sₙ − np)/√(np(1 − p))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace ProbabilityTheory

/-- **Standardized partial sums.** For a sequence $X_0, X_1, \dots$ of real-valued functions on a
set $\Omega$, a real number $p$ and $n \in \mathbb{N}$, the standardized partial sum is the
function $\omega \mapsto (S_n(\omega) - np)/\sqrt{np(1-p)}$ on $\Omega$, where
$S_n = X_0 + \dots + X_{n-1}$.

The square root of a negative number is taken to be $0$ and division by $0$ gives $0$; in
particular the standardized partial sum is $0$ for $n = 0$. -/
noncomputable def deMoivreLaplaceStandardized {Ω : Type*} (X : ℕ → Ω → ℝ)
    (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((∑ k ∈ Finset.range n, X k ω) - ↑n * p) / Real.sqrt (↑n * p * (1 - p))

/-- **Bernoulli standardization map.** For a real number $p$, the standardization map sends
$x \in \mathbb{R}$ to $(x - p)/\sqrt{p(1-p)}$.

The square root of a negative number is taken to be $0$ and division by $0$ gives $0$, so for
$p \le 0$ or $p \ge 1$ the map is identically $0$. -/
noncomputable def standardizedBernoulli (p : ℝ) (x : ℝ) : ℝ :=
  (x - p) / Real.sqrt (p * (1 - p))

/-- **Almost surely $\{0, 1\}$-valued random variables are integrable.** Let $P$ be a probability
measure on $\Omega$ and let $f : \Omega \to \mathbb{R}$ be almost everywhere measurable with
$f(\omega) \in \{0, 1\}$ for $P$-almost every $\omega$. Then $f$ is integrable with respect to
$P$. -/
theorem integrable_of_ae_eq_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : AEMeasurable f P) (h : ∀ᵐ ω ∂P, f ω = 0 ∨ f ω = 1) :
    Integrable f P := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable ?_
  filter_upwards [h] with ω hω
  rcases hω with hω | hω <;> simp [hω]

/-- **Second moment of a $\{0, 1\}$-valued random variable.** Let $P$ be a probability measure on
$\Omega$ and let $f : \Omega \to \mathbb{R}$ satisfy $f(\omega) \in \{0, 1\}$ for $P$-almost every
$\omega$. Then $\int f^2 \, dP = \int f \, dP$. -/
theorem integral_sq_eq_integral_of_ae_eq_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (h : ∀ᵐ ω ∂P, f ω = 0 ∨ f ω = 1) :
    ∫ ω, (f ω) ^ 2 ∂P = ∫ ω, f ω ∂P := by
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rcases hω with hω | hω <;> simp [hω]

/-- **De Moivre–Laplace limit theorem, convergence in distribution.** Let $X_0, X_1, \dots$ be
independent, identically distributed real random variables on a probability space $(\Omega, P)$,
each almost surely equal to $0$ or $1$, with mean $p$ for some $0 < p < 1$. Write
$S_n = X_0 + \dots + X_{n-1}$. Then the standardized sums $(S_n - np)/\sqrt{np(1-p)}$ converge in
distribution to the standard normal distribution $\mathcal{N}(0, 1)$ as $n \to \infty$. -/
theorem deMoivreLaplace_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = p)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun n ω => deMoivreLaplaceStandardized X p n ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 1) := by
  have hσpos : 0 < Real.sqrt (p * (1 - p)) :=
    Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1))
  have hσsq : (Real.sqrt (p * (1 - p))) ^ 2 = p * (1 - p) :=
    Real.sq_sqrt (mul_nonneg hp0.le (sub_nonneg.mpr hp1.le))
  have hmeas0 : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hint0 : Integrable (X 0) P :=
    integrable_of_ae_eq_zero_or_one hmeas0 (h01 0)
  have hintSq0 : Integrable (fun ω => (X 0 ω) ^ 2) P :=
    hint0.congr (by
      filter_upwards [h01 0] with ω hω
      rcases hω with hω | hω <;> simp [hω])
  have hsq0 : ∫ ω, (X 0 ω) ^ 2 ∂P = p := by
    rw [integral_sq_eq_integral_of_ae_eq_zero_or_one (h01 0)]
    exact hmean 0
  -- Mean and second moment of the standardized variable.
  have hYmean : ∫ ω, standardizedBernoulli p (X 0 ω) ∂P = 0 := by
    simp only [standardizedBernoulli]
    rw [integral_div, integral_sub hint0 (integrable_const p), hmean 0, integral_const]
    simp
  have hYsq : ∫ ω, (standardizedBernoulli p (X 0 ω)) ^ 2 ∂P = 1 := by
    have hcentered : ∫ ω, (X 0 ω - p) ^ 2 ∂P = p * (1 - p) := by
      have hae : (fun ω => (X 0 ω - p) ^ 2)
          =ᵐ[P] fun ω => (1 - 2 * p) * X 0 ω + p ^ 2 := by
        filter_upwards [h01 0] with ω hω
        show (X 0 ω - p) ^ 2 = (1 - 2 * p) * X 0 ω + p ^ 2
        rcases hω with hω | hω <;> rw [hω] <;> ring
      rw [integral_congr_ae hae,
        integral_add (hint0.const_mul (1 - 2 * p)) (integrable_const (p ^ 2)),
        integral_const_mul, hmean 0]
      have hconst : ∫ _ω, (p ^ 2 : ℝ) ∂P = p ^ 2 := by simp
      rw [hconst]
      ring
    simp only [standardizedBernoulli, div_pow, integral_div, hcentered, hσsq]
    exact div_self (ne_of_gt (mul_pos hp0 (sub_pos.mpr hp1)))
  have hmeasStd : Measurable (standardizedBernoulli p) := by
    unfold standardizedBernoulli
    fun_prop
  have hindepY : iIndepFun (fun k ω => standardizedBernoulli p (X k ω)) P :=
    hindep.comp (fun _ => standardizedBernoulli p) (fun _ => hmeasStd)
  have hidentY : ∀ i, IdentDistrib
      (fun ω => standardizedBernoulli p (X i ω))
      (fun ω => standardizedBernoulli p (X 0 ω)) P P :=
    fun i => (hident i).comp hmeasStd
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum hY hYmean hYsq hindepY hidentY
  -- Rewrite the CLT form as the book's standardized sum.
  refine hCLT.congr (fun n => ?_) (Eventually.of_forall fun _ => rfl)
  filter_upwards with ω
  by_cases hn : n = 0
  · subst hn
    simp [deMoivreLaplaceStandardized]
  · have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsqrt : Real.sqrt (↑n * p * (1 - p))
        = Real.sqrt (n : ℝ) * Real.sqrt (p * (1 - p)) := by
      rw [show (↑n * p * (1 - p) : ℝ) = ↑n * (p * (1 - p)) by ring,
        Real.sqrt_mul (Nat.cast_nonneg n)]
    have hsum : ∑ k ∈ Finset.range n, standardizedBernoulli p (X k ω)
        = ((∑ k ∈ Finset.range n, X k ω) - ↑n * p) / Real.sqrt (p * (1 - p)) := by
      simp only [standardizedBernoulli, ← Finset.sum_div, Finset.sum_sub_distrib]
      congr 1
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    unfold deMoivreLaplaceStandardized
    rw [hsqrt]
    field_simp [(Real.sqrt_ne_zero'.mpr hnpos), hσpos.ne']

/-- **De Moivre–Laplace limit theorem, interval form.** Let $X_0, X_1, \dots$ be independent,
identically distributed real random variables on a probability space $(\Omega, P)$, each almost
surely equal to $0$ or $1$, with mean $p$ for some $0 < p < 1$. Write
$S_n = X_0 + \dots + X_{n-1}$. Then for all real numbers $a \le b$, the probability
$P\left(a \le (S_n - np)/\sqrt{np(1-p)} \le b\right)$ tends, as $n \to \infty$, to the mass that
the standard normal distribution $\mathcal{N}(0, 1)$ gives to the interval $[a, b]$. -/
theorem deMoivreLaplace_interval_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = p)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | a ≤ deMoivreLaplaceStandardized X p n ω
        ∧ deMoivreLaplaceStandardized X p n ω ≤ b}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc a b))) := by
  have hdist := deMoivreLaplace_tendstoInDistribution X hp0 hp1 h01 hmean hindep hident
  have hlim := by simpa [Measure.map_id] using hdist.tendsto
  have hnull : ((⟨gaussianReal 0 (1 : ℝ≥0), inferInstance⟩ : ProbabilityMeasure ℝ)
      : Measure ℝ) (frontier (Set.Icc a b)) = 0 := by
    have hns : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    show (gaussianReal 0 (1 : ℝ≥0)) (frontier (Set.Icc a b)) = 0
    rw [frontier_Icc hab]
    apply measure_mono_null _ (measure_union_null (measure_singleton a)
      (measure_singleton b))
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hnull
  have hport' : Tendsto
      (fun n => (P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Icc a b))
      atTop (𝓝 ((gaussianReal 0 1) (Set.Icc a b))) :=
    hport
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport'
  have hterm : ∀ n, P.real {ω | a ≤ deMoivreLaplaceStandardized X p n ω
        ∧ deMoivreLaplaceStandardized X p n ω ≤ b}
      = ((P.map (fun ω => deMoivreLaplaceStandardized X p n ω)) (Set.Icc a b)).toReal := by
    intro n
    have hmeas : AEMeasurable (fun ω => deMoivreLaplaceStandardized X p n ω) P :=
      hdist.forall_aemeasurable n
    have hpre : (fun ω => deMoivreLaplaceStandardized X p n ω) ⁻¹' Set.Icc a b
        = {ω | a ≤ deMoivreLaplaceStandardized X p n ω
          ∧ deMoivreLaplaceStandardized X p n ω ≤ b} := by
      ext ω
      simp [Set.mem_Icc]
    rw [← hpre, Measure.map_apply_of_aemeasurable hmeas measurableSet_Icc]
    rfl
  have hlimterm : (gaussianReal 0 1).real (Set.Icc a b)
      = ((gaussianReal 0 1) (Set.Icc a b)).toReal :=
    rfl
  simp_rw [hterm, hlimterm]
  exact hreal

end ProbabilityTheory
