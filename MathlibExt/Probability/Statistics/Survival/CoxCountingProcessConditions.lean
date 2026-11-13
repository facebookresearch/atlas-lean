/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood
public import MathlibExt.Probability.Martingale.ConditionalVarianceCLT
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cox: Andersen–Gill limit hypotheses from counting-process conditions, given the compensator limit

Andersen and Gill (1982) derive consistency and asymptotic normality of the Cox estimator from
two limit statements, which T145 (`CoxAsymptotics`, Theorems 3.2 and 3.3 for a scalar covariate)
takes as hypotheses:

* (score CLT, `hscore`) `Uₙ(β₀) / √n ⟶ Z` in distribution with `Z ~ N(0, v)`, where
  `Uₙ = coxScore`;
* (uniform information, `hinfo`) for every `η > 0`,
  `P(∃ b ∈ [β₀ - r, β₀ + r], η ≤ |Iₙ(b) / n - i(b)|) → 0`, where `Iₙ = coxInformation`.

Andersen and Gill obtain them from counting-process conditions through Rebolledo's martingale
central limit theorem under a Lindeberg condition and Lenglart's inequality. This file reduces
both to the convergence of the information compensator (hypothesis `hcomp`) by carrying out the
martingale part of that derivation, for a discrete time grid.

## Source receipt

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Section 3 (proofs of Theorems 3.2 and 3.3: the score
  `U(β₀, ·) = ∑ᵢ ∫ (Zᵢ - E(β₀, s)) dMᵢ(s)` is a martingale with predictable variation
  `∫ V(β₀, s) S⁽⁰⁾(β₀, s) λ₀(s) ds`; the observed information minus its compensator is a
  martingale controlled by Lenglart's inequality).
* E. Lenglart, *Relation de domination entre deux processus*, Ann. Inst. H. Poincaré 13 (1977),
  171–179 (domination of a martingale square by its predictable variation).
* Reused, not reproved: `coxScore`, `coxInformation`, `riskMean`, `riskVar`, `riskSet` from
  `CoxPartialLikelihood` (the T145 setup); the martingale CLT under the conditional-variance
  normalization and the conditional Lindeberg condition,
  `MathlibExt.Probability.Martingale.tendstoInDistribution_martingale_condVar`; the identity
  `Martingale.integral_predictableQuadraticVariation` (`E⟨M⟩ = E M²`); Mathlib's conditional
  expectation calculus and mean value inequality.
* Proved here: the pathwise grid bridge to `coxScore` / `coxInformation`, the martingale property
  and predictable variation of the Cox score under the Cox intensity, Lenglart's inequality for a
  martingale difference row (terminal form; the copy in `MartingaleTightness` is private), the
  predictable-variation bound for the information martingale, the Lipschitz bound for
  `b ↦ V(b)`, and the uniform-in-`b` limit.

## The model (`IsCoxCountingProcess`)

For each sample size `n` there are `n` subjects with observed grid times `tᵢ ∈ ℕ`, event
indicators `δᵢ` and covariates `zᵢ`, observed through a filtration `F n` indexed by grid steps.
Grid step `k` covers grid time `k + 1`: subject `i` is at risk when `k + 1 ≤ tᵢ` (`atRiskInd`) and
has its event when `tᵢ = k + 1` and `δᵢ` (`eventInd`). The conditions are predictable at-risk
indicators, adapted event indicators, covariates known at time `0`, `|zᵢ| ≤ B`, nonnegative
baseline hazard increments `Δα`, the **Cox intensity**
`E[ΔNᵢ(k + 1) | F_k] = Yᵢ(k + 1) exp (β₀ zᵢ) Δα(k + 1)` and **no ties** (almost surely at most one
event per step). The data enter T145's statements as `T = (tᵢ : ℝ)`, `δ`, `z`; the hypothesis
`hsupp` asks that every observed event lies on steps `1, …, K n`.

## Main results

* `sum_range_scoreIncr_eq_coxScore`, `sum_range_infoIncr_eq_coxInformation`: the grid sums of
  score and information increments are `coxScore` and `coxInformation` of the data.
* `IsCoxCountingProcess.condExp_scoreIncr`: the score increments are martingale differences.
* `IsCoxCountingProcess.condExp_scoreIncr_sq` (**information identity**): the predictable
  variation of the score is the information compensator at `β₀`, `infoCompensator`.
* `measure_le_abs_sum_le` (**Lenglart's inequality**, discrete terminal form):
  `P(|∑_{k<K} xₖ| ≥ ε) ≤ P(∑_{k<K} E[xₖ² | F_k] > η) + η / ε²`.
* `tendstoInDistribution_coxScore`, `tendstoInDistribution_coxScore_of_hasLaw`: if the
  information compensator at `β₀` tends to `v` in probability, then `Uₙ(β₀) / √n ⟶ N(0, v)`
  (T145's `hscore`).
* `tendsto_measure_exists_coxInformation`: if the information compensator converges uniformly in
  probability on `[β₀ - r, β₀ + r]` to `i`, so does `Iₙ / n` (T145's `hinfo`, verbatim).
* `andersenGill_hypotheses_of_tendsto_infoCompensator`: both T145 hypotheses from the
  conditions and the uniform information-compensator limit `hcomp`, with `i β₀ = v`.

## Proof

The score increment `∑ᵢ (zᵢ - z̄(β₀)) ΔNᵢ` has conditional mean
`Δα ∑ᵢ (zᵢ - z̄(β₀)) Yᵢ exp (β₀ zᵢ) = 0`; with no ties its square is `∑ᵢ (zᵢ - z̄)² ΔNᵢ`, whose
conditional mean is `Δα V(β₀) S⁽⁰⁾(β₀)`. Bounded covariates and no ties bound each increment by
`2B`, so after dividing by `√n` the conditional Lindeberg sums vanish for large `n`, and the
conditional-variance martingale CLT applies. For the information, `Iₙ(b) / n` minus the
compensator is `∑ₖ (V(b) / n)(ΔN̄ - Δα S⁽⁰⁾(β₀))`, a martingale whose predictable variation is at
most `(2 B⁴ / n²) Ā`, with `E Ā = E N̄ ≤ n`; Lenglart's inequality gives convergence to `0` in
probability at each `b`. Since `|dV / db| ≤ 6 B³`, the martingale is Lipschitz in `b` with
constant `6 B³ (1 + Ā / n)`; a finite net of the interval and Markov's inequality for `Ā / n`
give the uniform statement.

## What is weakened or deferred

* **Discrete time grid.** The model is a grid version of Andersen–Gill's continuous-time model,
  in the convention of `StochasticIntegral` (a fixed grid per sample size, here of length `K n`,
  with arbitrary `K n`). The continuous-time statement (stochastic integrals against
  `dMᵢ(t)` with a continuous intensity) is not formalized.
* **The compensator limit is a hypothesis.** Andersen–Gill's conditions A–D (uniform
  convergence of `S⁽ʲ⁾(b, t) / n` to deterministic `s⁽ʲ⁾`, `s⁽⁰⁾` bounded away from zero,
  `∫ λ₀ < ∞`) imply that the information compensator `(1/n) ∑ₖ Δα V(b) S⁽⁰⁾(β₀)` converges
  uniformly to `i(b) = ∫ v(b, t) s⁽⁰⁾(β₀, t) λ₀(t) dt`; this law-of-large-numbers step is the
  hypothesis `hcomp`, not derived. What is derived is everything martingale-theoretic: the
  score CLT and the passage from the compensator to the observed information.
* **No ties, single events.** Each subject has at most one event (survival data, not general
  recurrent-event counting processes), and the no-ties condition is assumed almost surely.
  With ties, the predictable variation of the Breslow score differs from the information
  compensator and T145's common variance `v` fails. On a grid, no ties almost surely is a strong
  restriction: it forces `Δα S⁽⁰⁾(β₀) ≤ 1` (`ae_compIncr_le_one`), and it rules out
  conditionally independent subjects that share positive hazard in the same step. The model
  therefore covers one-event-per-step setups (`Δα = O(1/n)` with `K n` of order `n`), not
  ordinary discrete-time survival data with independent subjects.
* **Bounded scalar covariates, fixed in time.** Time-dependent and vector covariates are not
  treated; boundedness replaces Andersen–Gill's moment and Lindeberg conditions (the conditional
  Lindeberg condition is proved, not assumed).
* **Lenglart's inequality** is proved in the discrete terminal-time form needed here, not for
  general stopping times or continuous time.
* T145's file `CoxAsymptotics.lean` is not imported (open PR). Its hypotheses are restated in the
  conclusions of `tendstoInDistribution_coxScore_of_hasLaw` and
  `tendsto_measure_exists_coxInformation` with `T n ω = fun l => (t n ω l : ℝ)` and `δ = d`.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections II.4.1 (Lenglart's inequality) and VII.2.2.
* E. Lenglart, *Relation de domination entre deux processus*, Ann. Inst. H. Poincaré 13 (1977),
  171–179.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxCountingProcessConditions

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

/-! ### Weighted risk-set sums -/

section Weighted

variable {n : ℕ}

/-- The weighted risk-set sum `S⁽ʲ⁾(b) = ∑ₗ Yₗ zₗʲ exp (b zₗ)` for at-risk weights `Y` and a
scalar covariate `z`. -/
noncomputable def wSum (Y z : Fin n → ℝ) (j : ℕ) (b : ℝ) : ℝ :=
  ∑ l, Y l * z l ^ j * exp (b * z l)

/-- The `exp (b z)`-weighted mean of the covariate over the risk set, `S⁽¹⁾(b) / S⁽⁰⁾(b)`. -/
noncomputable def wMean (Y z : Fin n → ℝ) (b : ℝ) : ℝ :=
  wSum Y z 1 b / wSum Y z 0 b

/-- The `exp (b z)`-weighted variance of the covariate over the risk set,
`S⁽²⁾(b) / S⁽⁰⁾(b) - (S⁽¹⁾(b) / S⁽⁰⁾(b))²`. -/
noncomputable def wVar (Y z : Fin n → ℝ) (b : ℝ) : ℝ :=
  wSum Y z 2 b / wSum Y z 0 b - wMean Y z b ^ 2

variable {Y z : Fin n → ℝ} {B : ℝ}

theorem wSum_zero_nonneg (hY : ∀ l, 0 ≤ Y l) (b : ℝ) : 0 ≤ wSum Y z 0 b :=
  sum_nonneg fun l _ => by
    rw [pow_zero, mul_one]
    exact mul_nonneg (hY l) (exp_pos _).le

theorem wSum_two_nonneg (hY : ∀ l, 0 ≤ Y l) (b : ℝ) : 0 ≤ wSum Y z 2 b :=
  sum_nonneg fun l _ => mul_nonneg (mul_nonneg (hY l) (sq_nonneg _)) (exp_pos _).le

/-- `|S⁽ʲ⁾(b)| ≤ Bʲ S⁽⁰⁾(b)` for nonnegative weights and `|z| ≤ B`. -/
theorem abs_wSum_le (hY : ∀ l, 0 ≤ Y l) (hz : ∀ l, |z l| ≤ B) (j : ℕ) (b : ℝ) :
    |wSum Y z j b| ≤ B ^ j * wSum Y z 0 b := by
  unfold wSum
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hY l), abs_of_pos (exp_pos _), abs_pow, pow_zero, mul_one]
  have hB : |z l| ^ j ≤ B ^ j := pow_le_pow_left₀ (abs_nonneg _) (hz l) j
  have hYe : 0 ≤ Y l * exp (b * z l) := mul_nonneg (hY l) (exp_pos _).le
  calc Y l * |z l| ^ j * exp (b * z l) = |z l| ^ j * (Y l * exp (b * z l)) := by ring
    _ ≤ B ^ j * (Y l * exp (b * z l)) := mul_le_mul_of_nonneg_right hB hYe

/-- A vanishing `S⁽⁰⁾` forces all nonnegative at-risk weights to vanish. -/
theorem eq_zero_of_wSum_zero_eq_zero (hY : ∀ l, 0 ≤ Y l) {b : ℝ} (h : wSum Y z 0 b = 0)
    (l : Fin n) : Y l = 0 := by
  have hterm : ∀ l ∈ (univ : Finset (Fin n)), 0 ≤ Y l * z l ^ 0 * exp (b * z l) := fun l _ => by
    rw [pow_zero, mul_one]
    exact mul_nonneg (hY l) (exp_pos _).le
  have := (sum_eq_zero_iff_of_nonneg hterm).1 h l (mem_univ l)
  rw [pow_zero, mul_one] at this
  exact (mul_eq_zero.1 this).resolve_right (exp_pos _).ne'

/-- If `S⁽⁰⁾` vanishes at one coefficient, every `S⁽ʲ⁾` vanishes at every coefficient. -/
theorem wSum_eq_zero_of_wSum_zero_eq_zero (hY : ∀ l, 0 ≤ Y l) {b : ℝ} (h : wSum Y z 0 b = 0)
    (j : ℕ) (b' : ℝ) : wSum Y z j b' = 0 := by
  unfold wSum
  exact sum_eq_zero fun l _ => by rw [eq_zero_of_wSum_zero_eq_zero hY h l]; ring

/-- `|S⁽ʲ⁾(b) / S⁽⁰⁾(b)| ≤ Bʲ`. -/
theorem abs_wSum_div_le (hY : ∀ l, 0 ≤ Y l) (hz : ∀ l, |z l| ≤ B) (hB : 0 ≤ B) (j : ℕ)
    (b : ℝ) : |wSum Y z j b / wSum Y z 0 b| ≤ B ^ j := by
  rcases (wSum_zero_nonneg hY b (z := z)).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact pow_nonneg hB j
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h]
    exact abs_wSum_le hY hz j b

theorem abs_wMean_le (hY : ∀ l, 0 ≤ Y l) (hz : ∀ l, |z l| ≤ B) (hB : 0 ≤ B) (b : ℝ) :
    |wMean Y z b| ≤ B := by
  simpa [wMean] using abs_wSum_div_le hY hz hB 1 b

theorem abs_wVar_le (hY : ∀ l, 0 ≤ Y l) (hz : ∀ l, |z l| ≤ B) (hB : 0 ≤ B) (b : ℝ) :
    |wVar Y z b| ≤ B ^ 2 := by
  have h2 := abs_le.1 (abs_wSum_div_le hY hz hB 2 b)
  have hnn : 0 ≤ wSum Y z 2 b / wSum Y z 0 b :=
    div_nonneg (wSum_two_nonneg hY b) (wSum_zero_nonneg hY b)
  have hm : wMean Y z b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_wMean_le hY hz hB b) 2
  unfold wVar
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (wMean Y z b)]

/-- The weighted mean centers the weighted covariate sum: `S⁽¹⁾ - z̄ S⁽⁰⁾ = 0`. -/
theorem wSum_one_sub_wMean_mul (hY : ∀ l, 0 ≤ Y l) (b : ℝ) :
    wSum Y z 1 b - wMean Y z b * wSum Y z 0 b = 0 := by
  rcases (wSum_zero_nonneg hY b (z := z)).eq_or_lt with h | h
  · rw [← h, mul_zero, sub_zero]
    exact wSum_eq_zero_of_wSum_zero_eq_zero hY h.symm 1 b
  · rw [wMean, div_mul_cancel₀ _ h.ne', sub_self]

/-- `∑ᵢ (zᵢ - z̄(b)) Yᵢ exp (b zᵢ) c = c (S⁽¹⁾ - z̄ S⁽⁰⁾)`. -/
theorem sum_sub_wMean_mul (Y z : Fin n → ℝ) (b c : ℝ) :
    ∑ i, (z i - wMean Y z b) * (Y i * exp (b * z i) * c) =
      c * (wSum Y z 1 b - wMean Y z b * wSum Y z 0 b) := by
  simp only [wSum, mul_sub, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **Information identity for the risk set.** `∑ᵢ (zᵢ - z̄(b))² Yᵢ exp (b zᵢ) c =
c V(b) S⁽⁰⁾(b)`. -/
theorem sum_sq_sub_wMean_mul (hY : ∀ l, 0 ≤ Y l) (b c : ℝ) :
    ∑ i, (z i - wMean Y z b) ^ 2 * (Y i * exp (b * z i) * c) =
      c * (wVar Y z b * wSum Y z 0 b) := by
  have hexp : ∑ i, (z i - wMean Y z b) ^ 2 * (Y i * exp (b * z i) * c) =
      c * (wSum Y z 2 b - 2 * wMean Y z b * wSum Y z 1 b + wMean Y z b ^ 2 * wSum Y z 0 b) := by
    simp only [wSum, mul_add, mul_sub, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hexp]
  rcases (wSum_zero_nonneg hY b (z := z)).eq_or_lt with h | h
  · rw [← h, wSum_eq_zero_of_wSum_zero_eq_zero hY h.symm 1,
      wSum_eq_zero_of_wSum_zero_eq_zero hY h.symm 2]
    ring
  · have h1 := wSum_one_sub_wMean_mul hY b (z := z)
    rw [wVar, sub_mul, div_mul_cancel₀ _ h.ne']
    linear_combination (-2 * wMean Y z b * c) * h1

/-- With `0/1` jumps of total at most one, `(∑ᵢ aᵢ xᵢ)² = ∑ᵢ aᵢ² xᵢ`. -/
theorem sq_sum_mul_eq_of_sum_le_one {ι : Type*} [Fintype ι] (a x : ι → ℝ)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hsum : ∑ i, x i ≤ 1) :
    (∑ i, a i * x i) ^ 2 = ∑ i, a i ^ 2 * x i := by
  classical
  have hnn : ∀ i, 0 ≤ x i := fun i => by rcases hx i with h | h <;> simp [h]
  have hpair : ∀ i j, i ≠ j → x i * x j = 0 := by
    intro i j hij
    have hle : x i + x j ≤ 1 := by
      have := sum_le_sum_of_subset_of_nonneg (subset_univ {i, j}) (fun k _ _ => hnn k)
      rw [sum_pair hij] at this
      linarith
    rcases hx i with h | h
    · simp [h]
    · rcases hx j with h' | h'
      · simp [h']
      · linarith
  rw [sq, sum_mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single i]
  · rcases hx i with h | h <;> simp [h, sq]
  · intro j _ hji
    rw [show a i * x i * (a j * x j) = a i * a j * (x i * x j) by ring, hpair i j (Ne.symm hji),
      mul_zero]
  · intro h
    exact absurd (mem_univ i) h

end Weighted

/-! ### Grid encoding of the Cox data and the pathwise bridge -/

section Grid

variable {n : ℕ}

/-- At-risk indicator of subject `l` at grid step `k`, i.e. at grid time `k + 1`:
`Yₗ(k + 1) = 1{k + 1 ≤ tₗ}`. -/
noncomputable def atRiskInd (t : Fin n → ℕ) (k : ℕ) (l : Fin n) : ℝ :=
  if k + 1 ≤ t l then 1 else 0

/-- Event indicator of subject `i` at grid step `k`: `ΔNᵢ(k + 1) = 1{tᵢ = k + 1, δᵢ}`. -/
noncomputable def eventInd (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) (i : Fin n) : ℝ :=
  if t i = k + 1 ∧ d i = true then 1 else 0

/-- Number of observed events at grid step `k`, `ΔN̄(k + 1) = ∑ᵢ ΔNᵢ(k + 1)`. -/
noncomputable def eventCount (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) : ℝ :=
  ∑ i, eventInd t d k i

/-- Increment of the Cox score at grid step `k`: `∑ᵢ (zᵢ - z̄(b, k + 1)) ΔNᵢ(k + 1)`. -/
noncomputable def scoreIncr (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ)
    (k : ℕ) : ℝ :=
  ∑ i, (z i - wMean (atRiskInd t k) z b) * eventInd t d k i

/-- Increment of the observed information at grid step `k`: `V(b, k + 1) ΔN̄(k + 1)`. -/
noncomputable def infoIncr (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ) (b : ℝ)
    (k : ℕ) : ℝ :=
  wVar (atRiskInd t k) z b * eventCount t d k

/-- The compensator of the observed information over the first `K` grid steps under the Cox
intensity with true coefficient `β₀` and baseline hazard increments `dα`:
`∑_{k < K} V(b, k + 1) S⁽⁰⁾(β₀, k + 1) Δα(k + 1)`. -/
noncomputable def infoCompensator (t : Fin n → ℕ) (z : Fin n → ℝ) (dα : ℕ → ℝ) (β₀ b : ℝ)
    (K : ℕ) : ℝ :=
  ∑ k ∈ range K, dα k * wVar (atRiskInd t k) z b * wSum (atRiskInd t k) z 0 β₀

/-- The compensator of the total counting process over the first `K` grid steps,
`Ā(K) = ∑_{k < K} S⁽⁰⁾(β₀, k + 1) Δα(k + 1)`. -/
noncomputable def totalCompensator (t : Fin n → ℕ) (z : Fin n → ℝ) (dα : ℕ → ℝ) (β₀ : ℝ)
    (K : ℕ) : ℝ :=
  ∑ k ∈ range K, dα k * wSum (atRiskInd t k) z 0 β₀

theorem atRiskInd_nonneg (t : Fin n → ℕ) (k : ℕ) (l : Fin n) : 0 ≤ atRiskInd t k l := by
  unfold atRiskInd; split_ifs <;> norm_num

theorem eventInd_eq_zero_or_one (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) (i : Fin n) :
    eventInd t d k i = 0 ∨ eventInd t d k i = 1 := by
  unfold eventInd; split_ifs <;> simp

theorem eventInd_nonneg (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) (i : Fin n) :
    0 ≤ eventInd t d k i := by
  rcases eventInd_eq_zero_or_one t d k i with h | h <;> simp [h]

theorem eventInd_le_one (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) (i : Fin n) :
    eventInd t d k i ≤ 1 := by
  rcases eventInd_eq_zero_or_one t d k i with h | h <;> simp [h]

theorem eventCount_nonneg (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) : 0 ≤ eventCount t d k :=
  sum_nonneg fun i _ => eventInd_nonneg t d k i

/-- Each subject has at most one event on the grid. -/
theorem sum_range_eventInd_le_one (t : Fin n → ℕ) (d : Fin n → Bool) (K : ℕ) (i : Fin n) :
    ∑ k ∈ range K, eventInd t d k i ≤ 1 := by
  calc ∑ k ∈ range K, eventInd t d k i ≤ ∑ k ∈ range K, if t i - 1 = k then (1 : ℝ) else 0 := by
        refine sum_le_sum fun k _ => ?_
        unfold eventInd
        by_cases h1 : t i = k + 1 ∧ d i = true
        · simp [h1]
        · simp only [h1, ↓reduceIte]
          split_ifs <;> norm_num
    _ ≤ 1 := by rw [sum_ite_eq]; split_ifs <;> norm_num

/-- The total number of events over the grid is at most the number of subjects. -/
theorem sum_range_eventCount_le (t : Fin n → ℕ) (d : Fin n → Bool) (K : ℕ) :
    ∑ k ∈ range K, eventCount t d k ≤ n := by
  unfold eventCount
  rw [sum_comm]
  calc ∑ i, ∑ k ∈ range K, eventInd t d k i ≤ ∑ _i : Fin n, (1 : ℝ) :=
        sum_le_sum fun i _ => sum_range_eventInd_le_one t d K i
    _ = n := by simp

/-- Reindexing a grid sum of event-weighted terms by subject: each observed event contributes
its term at its own grid step. -/
theorem sum_range_sum_mul_eventInd (t : Fin n → ℕ) (d : Fin n → Bool) (K : ℕ)
    (h : ∀ i, d i = true → 1 ≤ t i ∧ t i ≤ K) (g : ℕ → Fin n → ℝ) :
    ∑ k ∈ range K, ∑ i, g k i * eventInd t d k i = ∑ i with d i = true, g (t i - 1) i := by
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hd : d i = true
  · simp only [hd, ↓reduceIte]
    rw [sum_eq_single (t i - 1)]
    · have h1 := (h i hd).1
      have : t i = t i - 1 + 1 := by omega
      simp [eventInd, hd, ← this]
    · intro k _ hk
      have : ¬ (t i = k + 1 ∧ d i = true) := fun ⟨h1, _⟩ => hk (by omega)
      simp [eventInd, this]
    · intro hk
      exact absurd (mem_range.2 (by have := h i hd; omega)) hk
  · simp only [hd]
    exact sum_eq_zero fun k _ => by simp [eventInd, hd]

theorem wSum_atRiskInd (t : Fin n → ℕ) (z : Fin n → ℝ) (k j : ℕ) (b : ℝ) :
    wSum (atRiskInd t k) z j b = ∑ l with k + 1 ≤ t l, z l ^ j * exp (b * z l) := by
  rw [sum_filter]
  unfold wSum atRiskInd
  exact sum_congr rfl fun l _ => by split_ifs <;> ring

theorem riskSet_natCast (t : Fin n → ℕ) (i : Fin n) :
    riskSet (fun l => (t l : ℝ)) i = ({l | t i ≤ t l} : Finset (Fin n)) := by
  ext l
  simp [riskSet]

/-- On the grid, the weighted mean at the event step of subject `i` is Cox's risk-set mean. -/
theorem wMean_atRiskInd_eq_riskMean (t : Fin n → ℕ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (hi : 1 ≤ t i) : wMean (atRiskInd t (t i - 1)) z b = riskMean (fun l => (t l : ℝ)) z b i := by
  rw [wMean, riskMean, wSum_atRiskInd, wSum_atRiskInd, Nat.sub_add_cancel hi, riskSet_natCast]
  simp

/-- On the grid, the weighted variance at the event step of subject `i` is Cox's risk-set
variance. -/
theorem wVar_atRiskInd_eq_riskVar (t : Fin n → ℕ) (z : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (hi : 1 ≤ t i) : wVar (atRiskInd t (t i - 1)) z b = riskVar (fun l => (t l : ℝ)) z b i := by
  rw [wVar, riskVar, wMean_atRiskInd_eq_riskMean t z b i hi, wSum_atRiskInd, wSum_atRiskInd,
    Nat.sub_add_cancel hi, riskSet_natCast]
  simp

/-- **Pathwise bridge for the score.** If every observed event lies on the grid steps
`1, …, K`, the summed score increments are the Cox score `coxScore` of the data. -/
theorem sum_range_scoreIncr_eq_coxScore (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ)
    (b : ℝ) (K : ℕ) (h : ∀ i, d i = true → 1 ≤ t i ∧ t i ≤ K) :
    ∑ k ∈ range K, scoreIncr t d z b k = coxScore (fun l => (t l : ℝ)) d z b := by
  unfold scoreIncr coxScore
  rw [sum_range_sum_mul_eventInd t d K h (fun k i => z i - wMean (atRiskInd t k) z b)]
  refine sum_congr rfl fun i hi => ?_
  rw [wMean_atRiskInd_eq_riskMean t z b i (h i (mem_filter.1 hi).2).1]

/-- **Pathwise bridge for the information.** If every observed event lies on the grid steps
`1, …, K`, the summed information increments are the observed information `coxInformation`. -/
theorem sum_range_infoIncr_eq_coxInformation (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ)
    (b : ℝ) (K : ℕ) (h : ∀ i, d i = true → 1 ≤ t i ∧ t i ≤ K) :
    ∑ k ∈ range K, infoIncr t d z b k = coxInformation (fun l => (t l : ℝ)) d z b := by
  unfold infoIncr eventCount coxInformation
  simp_rw [mul_sum]
  rw [sum_range_sum_mul_eventInd t d K h (fun k _ => wVar (atRiskInd t k) z b)]
  refine sum_congr rfl fun i hi => ?_
  rw [wVar_atRiskInd_eq_riskVar t z b i (h i (mem_filter.1 hi).2).1]

/-- Under no ties the score increment is bounded by `2 B` times the number of events. -/
theorem abs_scoreIncr_le {B : ℝ} (t : Fin n → ℕ) (d : Fin n → Bool) {z : Fin n → ℝ}
    (hz : ∀ l, |z l| ≤ B) (hB : 0 ≤ B) (b : ℝ) (k : ℕ) :
    |scoreIncr t d z b k| ≤ 2 * B * eventCount t d k := by
  unfold scoreIncr eventCount
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (eventInd_nonneg t d k i)]
  have hm := abs_wMean_le (atRiskInd_nonneg t k) hz hB b
  have : |z i - wMean (atRiskInd t k) z b| ≤ 2 * B := by
    calc |z i - wMean (atRiskInd t k) z b| ≤ |z i| + |wMean (atRiskInd t k) z b| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hz i]
  exact mul_le_mul_of_nonneg_right this (eventInd_nonneg t d k i)

end Grid

/-! ### Lipschitz dependence of the weighted variance on the coefficient -/

section Lipschitz

variable {n : ℕ}

theorem hasDerivAt_wSum (Y z : Fin n → ℝ) (j : ℕ) (b : ℝ) :
    HasDerivAt (fun b => wSum Y z j b) (wSum Y z (j + 1) b) b := by
  unfold wSum
  refine HasDerivAt.fun_sum fun l _ => ?_
  have := ((hasDerivAt_mul_const (z l)).exp).const_mul (Y l * z l ^ j) (x := b)
  convert this using 1
  ring

/-- `b ↦ V(b)` is `6 B³`-Lipschitz for nonnegative weights and `|z| ≤ B`: its derivative is the
weighted third central moment. -/
theorem abs_wVar_sub_le {Y z : Fin n → ℝ} {B : ℝ} (hY : ∀ l, 0 ≤ Y l) (hz : ∀ l, |z l| ≤ B)
    (hB : 0 ≤ B) (b b' : ℝ) : |wVar Y z b - wVar Y z b'| ≤ 6 * B ^ 3 * |b - b'| := by
  by_cases h0 : ∀ l, Y l = 0
  · have hv : ∀ b, wVar Y z b = 0 := fun b => by simp [wVar, wMean, wSum, h0]
    rw [hv, hv, sub_zero, abs_zero]
    positivity
  push Not at h0
  obtain ⟨l₀, hl₀⟩ := h0
  have hYl : 0 < Y l₀ := lt_of_le_of_ne (hY l₀) (Ne.symm hl₀)
  have hpos : ∀ b, 0 < wSum Y z 0 b := fun b => by
    have hnn : ∀ l ∈ (univ : Finset (Fin n)), 0 ≤ Y l * z l ^ 0 * exp (b * z l) := fun l _ => by
      rw [pow_zero, mul_one]
      exact mul_nonneg (hY l) (exp_pos _).le
    calc (0 : ℝ) < Y l₀ * z l₀ ^ 0 * exp (b * z l₀) := by
          rw [pow_zero, mul_one]; exact mul_pos hYl (exp_pos _)
      _ ≤ wSum Y z 0 b := single_le_sum hnn (mem_univ l₀)
  have hd : ∀ x, HasDerivAt (fun b => wVar Y z b)
      (wSum Y z 3 x / wSum Y z 0 x - wSum Y z 2 x / wSum Y z 0 x * (wSum Y z 1 x / wSum Y z 0 x) -
        2 * (wSum Y z 1 x / wSum Y z 0 x) *
          (wSum Y z 2 x / wSum Y z 0 x - (wSum Y z 1 x / wSum Y z 0 x) ^ 2)) x := by
    intro x
    have h0 : HasDerivAt (fun b => wSum Y z 0 b) (wSum Y z 1 x) x := hasDerivAt_wSum Y z 0 x
    have h1 : HasDerivAt (fun b => wSum Y z 1 b) (wSum Y z 2 x) x := hasDerivAt_wSum Y z 1 x
    have h2 : HasDerivAt (fun b => wSum Y z 2 b) (wSum Y z 3 x) x := hasDerivAt_wSum Y z 2 x
    have hne := (hpos x).ne'
    have := (h2.div h0 hne).sub ((h1.div h0 hne).pow 2)
    convert this using 1
    all_goals first
      | (funext y; simp only [wVar, wMean, Pi.sub_apply, Pi.div_apply, Pi.pow_apply])
      | (simp only [Pi.div_apply]; norm_num; field_simp)
  have hbound : ∀ x, ‖wSum Y z 3 x / wSum Y z 0 x -
      wSum Y z 2 x / wSum Y z 0 x * (wSum Y z 1 x / wSum Y z 0 x) -
        2 * (wSum Y z 1 x / wSum Y z 0 x) *
          (wSum Y z 2 x / wSum Y z 0 x - (wSum Y z 1 x / wSum Y z 0 x) ^ 2)‖ ≤ 6 * B ^ 3 := by
    intro x
    have h1 := abs_wSum_div_le hY hz hB 1 x
    have h2 := abs_wSum_div_le hY hz hB 2 x
    have h3 := abs_wSum_div_le hY hz hB 3 x
    rw [Real.norm_eq_abs]
    generalize wSum Y z 1 x / wSum Y z 0 x = a1 at *
    generalize wSum Y z 2 x / wSum Y z 0 x = a2 at *
    generalize wSum Y z 3 x / wSum Y z 0 x = a3 at *
    rw [pow_one] at h1
    have e1 : |a2 * a1| ≤ B ^ 2 * B := by
      rw [abs_mul]; exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    have e2 : |a2 - a1 ^ 2| ≤ 2 * B ^ 2 := by
      calc |a2 - a1 ^ 2| ≤ |a2| + |a1 ^ 2| := abs_sub _ _
        _ ≤ B ^ 2 + B ^ 2 := by
          rw [abs_pow]; exact add_le_add h2 (pow_le_pow_left₀ (abs_nonneg _) h1 2)
        _ = 2 * B ^ 2 := by ring
    have e3 : |2 * a1 * (a2 - a1 ^ 2)| ≤ 2 * B * (2 * B ^ 2) := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 two_pos.le) e2 (abs_nonneg _) (by positivity)
    calc |a3 - a2 * a1 - 2 * a1 * (a2 - a1 ^ 2)|
        ≤ |a3 - a2 * a1| + |2 * a1 * (a2 - a1 ^ 2)| := abs_sub _ _
      _ ≤ |a3| + |a2 * a1| + |2 * a1 * (a2 - a1 ^ 2)| := by gcongr; exact abs_sub _ _
      _ ≤ B ^ 3 + B ^ 2 * B + 2 * B * (2 * B ^ 2) := by gcongr
      _ = 6 * B ^ 3 := by ring
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hbound x) (Set.mem_univ b') (Set.mem_univ b)
  simpa [Real.norm_eq_abs] using this

end Lipschitz

/-! ### Lenglart's inequality for a martingale difference row -/

section Lenglart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Predictable truncation keeps the summed conditional variances below `η`. -/
theorem sum_range_ite_le (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) {η : ℝ} (hη : 0 ≤ η) (K : ℕ) :
    ∑ k ∈ range K, (if ∑ j ∈ range (k + 1), c j ≤ η then c k else 0) ≤ η := by
  induction K with
  | zero => simpa using hη
  | succ K ih =>
    rw [sum_range_succ]
    by_cases hK : ∑ j ∈ range (K + 1), c j ≤ η
    · simp only [hK, ↓reduceIte]
      have hle : ∑ k ∈ range K, (if ∑ j ∈ range (k + 1), c j ≤ η then c k else 0) ≤
          ∑ k ∈ range K, c k := sum_le_sum fun k _ => by split_ifs <;> simp [hc k]
      rw [sum_range_succ] at hK
      linarith
    · simp only [hK, ↓reduceIte, add_zero]
      exact ih

/-- **Lenglart's inequality for a martingale difference row** (discrete form, terminal time).
For a square-integrable martingale difference sequence `x` (`x k` is `F (k + 1)`-measurable and
`E[x k | F k] = 0`) and `ε, η > 0`,
`P(|∑_{k < K} x k| ≥ ε) ≤ P(∑_{k < K} E[x k² | F k] > η) + η / ε²`.
The predictable variation dominates the square of the martingale (Lenglart 1977): truncating
the row predictably once the summed conditional variances exceed `η` gives a martingale with
second moment at most `η`, and the truncation is inactive where the conditional variances stay
below `η`. -/
theorem measure_le_abs_sum_le {F : Filtration ℕ m0} {x : ℕ → Ω → ℝ}
    (hx : ∀ k, StronglyMeasurable[F (k + 1)] (x k)) (hmds : ∀ k, P[x k | F k] =ᵐ[P] 0)
    (hL2 : ∀ k, MemLp (x k) 2 P) (K : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    P {ω | ε ≤ |∑ k ∈ range K, x k ω|} ≤
      P {ω | η < ∑ k ∈ range K, (P[fun ω => x k ω ^ 2 | F k]) ω} +
        ENNReal.ofReal (η / ε ^ 2) := by
  set c : ℕ → Ω → ℝ := fun k => P[fun ω => x k ω ^ 2 | F k] with hc
  set A : ℕ → Set Ω := fun k => {ω | ∑ j ∈ range (k + 1), c j ω ≤ η} with hA
  have hAm : ∀ k, MeasurableSet[F k] (A k) := by
    intro k
    have hg : Measurable[F k] (fun ω => ∑ j ∈ range (k + 1), c j ω) :=
      Finset.measurable_fun_sum _ fun j hj =>
        stronglyMeasurable_condExp.measurable.mono (F.mono (by simp at hj; omega)) le_rfl
    exact hg measurableSet_Iic
  have hAm0 : ∀ k, MeasurableSet (A k) := fun k => F.le k _ (hAm k)
  set y : ℕ → Ω → ℝ := fun k => (A k).indicator (x k) with hy
  set f : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ range k, y j ω with hf
  have hyL2 : ∀ k, MemLp (y k) 2 P := fun k => (hL2 k).indicator (hAm0 k).nullMeasurableSet
  have hyF : ∀ k, StronglyMeasurable[F (k + 1)] (y k) := fun k =>
    (hx k).indicator (F.mono (Nat.le_succ k) _ (hAm k))
  have hfL2 : ∀ k, MemLp (f k) 2 P := fun k => memLp_finsetSum _ fun j _ => hyL2 j
  have hmart : Martingale f F P := by
    refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_)
      (fun k => (hfL2 k).integrable one_le_two) (fun k => ?_)
    · exact Finset.stronglyMeasurable_fun_sum _ fun j hj =>
        (hyF j).mono (F.mono (by simp at hj; omega))
    · have hdiff : f (k + 1) - f k = y k := by
        funext ω
        simp [hf, sum_range_succ]
      rw [hdiff]
      filter_upwards [condExp_indicator ((hL2 k).integrable one_le_two) (hAm k), hmds k] with
        ω h1 h2
      rw [h1]
      simp [Set.indicator_apply, h2]
  have hcnn : ∀ᵐ ω ∂P, ∀ j, 0 ≤ c j ω :=
    ae_all_iff.2 fun j => condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (x j ω))
  have hpqv : ∀ᵐ ω ∂P, predictableQuadraticVariation P F f K ω ≤ η := by
    have hterm : ∀ᵐ ω ∂P, ∀ k, P[fun ω' => (f (k + 1) ω' - f k ω') ^ 2 | F k] ω =
        (A k).indicator (c k) ω := by
      rw [ae_all_iff]
      intro k
      have hfun : (fun ω' => (f (k + 1) ω' - f k ω') ^ 2) =
          (A k).indicator (fun ω' => x k ω' ^ 2) := by
        funext ω'
        simp only [hf, sum_range_succ, add_sub_cancel_left, hy]
        by_cases h : ω' ∈ A k <;> simp [h]
      rw [hfun]
      exact condExp_indicator (hL2 k).integrable_sq (hAm k)
    filter_upwards [hcnn, hterm] with ω hω hω'
    simp only [predictableQuadraticVariation]
    rw [sum_congr rfl fun k _ => hω' k]
    simp only [Set.indicator_apply, hA, Set.mem_ofPred_eq]
    exact sum_range_ite_le (fun j => c j ω) hω hη.le K
  have hEf : ∫ ω, f K ω ^ 2 ∂P ≤ η := by
    have h := Martingale.integral_predictableQuadraticVariation hmart hfL2 K
    have h0 : ∫ ω, f 0 ω ^ 2 ∂P = 0 := by simp [hf]
    rw [h0, sub_zero] at h
    rw [← h]
    have hint : Integrable (predictableQuadraticVariation P F f K) P := by
      unfold predictableQuadraticVariation
      exact integrable_finsetSum _ fun k _ => integrable_condExp
    calc ∫ ω, predictableQuadraticVariation P F f K ω ∂P ≤ ∫ _ω, η ∂P :=
          integral_mono_ae hint (integrable_const η) hpqv
      _ = η := by simp
  have hcheb : P {ω | ε ^ 2 ≤ f K ω ^ 2} ≤ ENNReal.ofReal (η / ε ^ 2) := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => sq_nonneg (f K ω)) (hfL2 K).integrable_sq (ε ^ 2)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h.trans hEf
  calc P {ω | ε ≤ |∑ k ∈ range K, x k ω|}
      ≤ P ({ω | η < ∑ k ∈ range K, c k ω} ∪ {ω | ε ^ 2 ≤ f K ω ^ 2}) := by
        refine measure_mono_ae ?_
        filter_upwards [hcnn] with ω hω hmem
        by_cases hbig : η < ∑ k ∈ range K, c k ω
        · exact Or.inl hbig
        · right
          push Not at hbig
          have heq : f K ω = ∑ k ∈ range K, x k ω := by
            simp only [hf, hy]
            refine sum_congr rfl fun k hk => Set.indicator_of_mem ?_ _
            change ∑ j ∈ range (k + 1), c j ω ≤ η
            exact le_trans (sum_le_sum_of_subset_of_nonneg
              (range_subset_range.2 (by simp at hk; omega)) fun j _ _ => hω j) hbig
          simp only [Set.mem_ofPred_eq] at hmem ⊢
          rw [heq, ← sq_abs (∑ k ∈ range K, x k ω)]
          exact pow_le_pow_left₀ hε.le hmem 2
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hcheb)

end Lenglart

/-! ### Measurability of risk-set functionals -/

section Measurability

variable {Ω : Type*} {n : ℕ}

theorem measurable_wSum {m : MeasurableSpace Ω} {Y z : Ω → Fin n → ℝ}
    (hY : ∀ l, Measurable fun ω => Y ω l) (hz : ∀ l, Measurable fun ω => z ω l) (j : ℕ)
    (b : ℝ) : Measurable fun ω => wSum (Y ω) (z ω) j b :=
  Finset.measurable_fun_sum _ fun l _ =>
    ((hY l).mul ((hz l).pow_const j)).mul ((hz l).const_mul b).exp

theorem measurable_wMean {m : MeasurableSpace Ω} {Y z : Ω → Fin n → ℝ}
    (hY : ∀ l, Measurable fun ω => Y ω l) (hz : ∀ l, Measurable fun ω => z ω l) (b : ℝ) :
    Measurable fun ω => wMean (Y ω) (z ω) b :=
  (measurable_wSum hY hz 1 b).div (measurable_wSum hY hz 0 b)

theorem measurable_wVar {m : MeasurableSpace Ω} {Y z : Ω → Fin n → ℝ}
    (hY : ∀ l, Measurable fun ω => Y ω l) (hz : ∀ l, Measurable fun ω => z ω l) (b : ℝ) :
    Measurable fun ω => wVar (Y ω) (z ω) b :=
  ((measurable_wSum hY hz 2 b).div (measurable_wSum hY hz 0 b)).sub
    ((measurable_wMean hY hz b).pow_const 2)

/-- A bounded measurable real function is integrable for a finite measure. -/
theorem integrable_of_abs_le {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- A bounded measurable real function is square integrable for a finite measure. -/
theorem memLp_two_of_abs_le {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

theorem wSum_zero_le {Y z : Fin n → ℝ} {B : ℝ} (hY1 : ∀ l, Y l ≤ 1)
    (hz : ∀ l, |z l| ≤ B) (b : ℝ) : wSum Y z 0 b ≤ n * exp (|b| * B) := by
  unfold wSum
  calc ∑ l, Y l * z l ^ 0 * exp (b * z l) ≤ ∑ _l : Fin n, exp (|b| * B) := by
        refine sum_le_sum fun l _ => ?_
        rw [pow_zero, mul_one]
        have he : exp (b * z l) ≤ exp (|b| * B) := by
          refine exp_le_exp.2 ((le_abs_self _).trans ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hz l) (abs_nonneg b)
        calc Y l * exp (b * z l) ≤ 1 * exp (b * z l) :=
              mul_le_mul_of_nonneg_right (hY1 l) (exp_pos _).le
          _ ≤ exp (|b| * B) := by rw [one_mul]; exact he
    _ = n * exp (|b| * B) := by simp

theorem atRiskInd_le_one (t : Fin n → ℕ) (k : ℕ) (l : Fin n) : atRiskInd t k l ≤ 1 := by
  unfold atRiskInd; split_ifs <;> norm_num

theorem eventCount_le (t : Fin n → ℕ) (d : Fin n → Bool) (k : ℕ) : eventCount t d k ≤ n := by
  unfold eventCount
  calc ∑ i, eventInd t d k i ≤ ∑ _i : Fin n, (1 : ℝ) :=
        sum_le_sum fun i _ => eventInd_le_one t d k i
    _ = n := by simp

end Measurability

/-! ### The discrete-time Cox counting-process model -/

section Model

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **Counting-process conditions for the Cox model on a time grid.** For each sample size `n`,
`n` subjects have observed grid times `t n ω i ∈ ℕ`, event indicators `d n ω i` and scalar
covariates `z n ω i`, observed through the filtration `F n`. Subject `i` is at risk at grid time
`k + 1` when `k + 1 ≤ tᵢ` (`atRiskInd`) and has its event there when `tᵢ = k + 1` and `δᵢ`
(`eventInd`). The conditions are:

* the at-risk indicators are predictable, the event indicators adapted, and the covariates known
  at time `0`;
* the covariates are bounded, `|zᵢ| ≤ B`;
* the baseline hazard increments `dα n k` are nonnegative;
* **the Cox intensity**: `E[ΔNᵢ(k + 1) | F_k] = Yᵢ(k + 1) exp (β₀ zᵢ) Δα(k + 1)`, the discrete
  form of Andersen–Gill's multiplicative intensity `Yᵢ(t) exp (β₀ zᵢ) λ₀(t)`;
* **no ties**: almost surely at most one event per grid step. On a grid this forces
  `Δα S⁽⁰⁾(β₀) ≤ 1` (`ae_compIncr_le_one`) and excludes conditionally independent subjects that
  share positive hazard in the same step, so the model covers one-event-per-step setups
  (`Δα = O(1/n)`, `K n` of order `n`), not ordinary discrete-time survival data with independent
  subjects. (In continuous time no ties holds when the event times have continuous laws; that
  case is not formalized here.) -/
structure IsCoxCountingProcess (P : Measure Ω) (F : ℕ → Filtration ℕ m0)
    (t : (n : ℕ) → Ω → Fin n → ℕ) (d : (n : ℕ) → Ω → Fin n → Bool)
    (z : (n : ℕ) → Ω → Fin n → ℝ) (dα : ℕ → ℕ → ℝ) (β₀ B : ℝ) : Prop where
  /-- At-risk indicators are predictable. -/
  atRisk_measurable : ∀ n k l, StronglyMeasurable[F n k] fun ω => atRiskInd (t n ω) k l
  /-- Event indicators are adapted. -/
  event_measurable : ∀ n k i, StronglyMeasurable[F n (k + 1)] fun ω => eventInd (t n ω) (d n ω) k i
  /-- Covariates are known at time `0`. -/
  covariate_measurable : ∀ n l, StronglyMeasurable[F n 0] fun ω => z n ω l
  /-- The covariate bound is nonnegative. -/
  bound_nonneg : 0 ≤ B
  /-- Covariates are bounded. -/
  covariate_bound : ∀ n ω l, |z n ω l| ≤ B
  /-- Baseline hazard increments are nonnegative. -/
  hazard_nonneg : ∀ n k, 0 ≤ dα n k
  /-- The Cox intensity. -/
  intensity : ∀ n k i, P[fun ω => eventInd (t n ω) (d n ω) k i | F n k] =ᵐ[P]
    fun ω => atRiskInd (t n ω) k i * exp (β₀ * z n ω i) * dα n k
  /-- No tied events. -/
  no_ties : ∀ n, ∀ᵐ ω ∂P, ∀ k, eventCount (t n ω) (d n ω) k ≤ 1

namespace IsCoxCountingProcess

variable {P : Measure Ω} {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

theorem measurable_atRisk (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (l : Fin n) :
    Measurable[F n k] fun ω => atRiskInd (t n ω) k l :=
  (h.atRisk_measurable n k l).measurable

theorem measurable_covariate (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (l : Fin n) :
    Measurable[F n k] fun ω => z n ω l :=
  (h.covariate_measurable n l).measurable.mono ((F n).mono (Nat.zero_le k)) le_rfl

theorem measurable_event (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (i : Fin n) :
    Measurable fun ω => eventInd (t n ω) (d n ω) k i :=
  (h.event_measurable n k i).measurable.mono ((F n).le _) le_rfl

theorem measurable_wMean' (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ) :
    Measurable[F n k] fun ω => wMean (atRiskInd (t n ω) k) (z n ω) b :=
  measurable_wMean (m := F n k) (fun l => h.measurable_atRisk n k l)
    (fun l => h.measurable_covariate n k l) b

theorem measurable_wVar' (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ) :
    Measurable[F n k] fun ω => wVar (atRiskInd (t n ω) k) (z n ω) b :=
  measurable_wVar (m := F n k) (fun l => h.measurable_atRisk n k l)
    (fun l => h.measurable_covariate n k l) b

theorem measurable_wSum' (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k j : ℕ) (b : ℝ) :
    Measurable[F n k] fun ω => wSum (atRiskInd (t n ω) k) (z n ω) j b :=
  measurable_wSum (m := F n k) (fun l => h.measurable_atRisk n k l)
    (fun l => h.measurable_covariate n k l) j b

/-- Conditional expectation of an event-weighted sum with predictable bounded weights: the
compensator replaces each `ΔNᵢ` by `Yᵢ exp (β₀ zᵢ) Δα`. -/
theorem condExp_sum_mul_eventInd [IsFiniteMeasure P] (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (n k : ℕ) {a : Fin n → Ω → ℝ} (ha : ∀ i, Measurable[F n k] (a i)) {C : ℝ}
    (haC : ∀ i ω, |a i ω| ≤ C) :
    P[fun ω => ∑ i, a i ω * eventInd (t n ω) (d n ω) k i | F n k] =ᵐ[P]
      fun ω => ∑ i, a i ω * (atRiskInd (t n ω) k i * exp (β₀ * z n ω i) * dα n k) := by
  have heI : ∀ i, Integrable (fun ω => eventInd (t n ω) (d n ω) k i) P := fun i =>
    integrable_of_abs_le (h.measurable_event n k i) 1 fun ω => by
      rw [abs_of_nonneg (eventInd_nonneg _ _ _ _)]; exact eventInd_le_one _ _ _ _
  have hprodI : ∀ i, Integrable (a i * fun ω => eventInd (t n ω) (d n ω) k i) P := fun i =>
    integrable_of_abs_le (((ha i).mono ((F n).le k) le_rfl).mul (h.measurable_event n k i)) C
      fun ω => by
        rw [Pi.mul_apply, abs_mul, abs_of_nonneg (eventInd_nonneg _ _ _ _)]
        calc |a i ω| * eventInd (t n ω) (d n ω) k i ≤ |a i ω| * 1 :=
              mul_le_mul_of_nonneg_left (eventInd_le_one _ _ _ _) (abs_nonneg _)
          _ ≤ C := by rw [mul_one]; exact haC i ω
  have hsum : (fun ω => ∑ i, a i ω * eventInd (t n ω) (d n ω) k i) =
      ∑ i, (a i * fun ω => eventInd (t n ω) (d n ω) k i) := by
    funext ω
    simp [Finset.sum_apply]
  rw [hsum]
  have hall : ∀ᵐ ω ∂P, ∀ i, P[a i * fun ω => eventInd (t n ω) (d n ω) k i | F n k] ω =
      a i ω * (atRiskInd (t n ω) k i * exp (β₀ * z n ω i) * dα n k) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (ha i).stronglyMeasurable (hprodI i)
      (heI i), h.intensity n k i] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  filter_upwards [condExp_finsetSum (fun i _ => hprodI i) (F n k), hall] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact sum_congr rfl fun i _ => h2 i

theorem abs_sub_wMean_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ)
    (ω : Ω) (i : Fin n) : |z n ω i - wMean (atRiskInd (t n ω) k) (z n ω) b| ≤ 2 * B := by
  have hm := abs_wMean_le (atRiskInd_nonneg (t n ω) k) (h.covariate_bound n ω) h.bound_nonneg b
  calc |z n ω i - wMean (atRiskInd (t n ω) k) (z n ω) b|
      ≤ |z n ω i| + |wMean (atRiskInd (t n ω) k) (z n ω) b| := abs_sub _ _
    _ ≤ 2 * B := by linarith [h.covariate_bound n ω i]

theorem measurable_scoreIncr (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ) :
    Measurable[F n (k + 1)] fun ω => scoreIncr (t n ω) (d n ω) (z n ω) b k :=
  Finset.measurable_fun_sum _ fun i _ =>
    ((h.measurable_covariate n k i).sub (h.measurable_wMean' n k b)).mono
      ((F n).mono (Nat.le_succ k)) le_rfl |>.mul (h.event_measurable n k i).measurable

theorem abs_scoreIncr_le_n (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ)
    (ω : Ω) : |scoreIncr (t n ω) (d n ω) (z n ω) b k| ≤ 2 * B * n :=
  (abs_scoreIncr_le (t n ω) (d n ω) (h.covariate_bound n ω) h.bound_nonneg b k).trans
    (mul_le_mul_of_nonneg_left (eventCount_le _ _ _) (by linarith [h.bound_nonneg]))

/-- **The Cox score is a martingale.** Under the Cox intensity, the score increment at `β₀` has
conditional mean zero: `∑ᵢ (zᵢ - z̄(β₀)) Yᵢ exp (β₀ zᵢ) = 0`. -/
theorem condExp_scoreIncr [IsFiniteMeasure P] (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (n k : ℕ) : P[fun ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k | F n k] =ᵐ[P] 0 := by
  have hc := h.condExp_sum_mul_eventInd n k
    (a := fun i ω => z n ω i - wMean (atRiskInd (t n ω) k) (z n ω) β₀)
    (fun i => (h.measurable_covariate n k i).sub (h.measurable_wMean' n k β₀))
    (fun i ω => h.abs_sub_wMean_le n k β₀ ω i)
  filter_upwards [hc] with ω hω
  simp only [scoreIncr] at hω ⊢
  rw [hω, sum_sub_wMean_mul, wSum_one_sub_wMean_mul (atRiskInd_nonneg _ _), mul_zero,
    Pi.zero_apply]

/-- **Predictable variation of the Cox score** (the Andersen–Gill information identity):
`E[(ΔU(β₀))² | F_k] = Δα V(β₀) S⁽⁰⁾(β₀)`, the increment of the information compensator. -/
theorem condExp_scoreIncr_sq [IsFiniteMeasure P] (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (n k : ℕ) : P[fun ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k ^ 2 | F n k] =ᵐ[P]
      fun ω => dα n k * (wVar (atRiskInd (t n ω) k) (z n ω) β₀ *
        wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) := by
  have hae : (fun ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k ^ 2) =ᵐ[P]
      fun ω => ∑ i, (z n ω i - wMean (atRiskInd (t n ω) k) (z n ω) β₀) ^ 2 *
        eventInd (t n ω) (d n ω) k i := by
    filter_upwards [h.no_ties n] with ω hω
    exact sq_sum_mul_eq_of_sum_le_one _ _ (eventInd_eq_zero_or_one _ _ k) (hω k)
  have hc := h.condExp_sum_mul_eventInd n k
    (a := fun i ω => (z n ω i - wMean (atRiskInd (t n ω) k) (z n ω) β₀) ^ 2)
    (fun i => ((h.measurable_covariate n k i).sub (h.measurable_wMean' n k β₀)).pow_const 2)
    (C := (2 * B) ^ 2) (fun i ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_sub_wMean_le n k β₀ ω i) 2)
  filter_upwards [condExp_congr_ae hae, hc] with ω h1 h2
  rw [h1, h2, sum_sq_sub_wMean_mul (atRiskInd_nonneg _ _)]

end IsCoxCountingProcess

end Model

/-! ### The score limit: martingale CLT under the conditional Lindeberg condition -/

section Score

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

omit [IsProbabilityMeasure P] in
/-- A sequence of functions that is eventually almost surely zero tends to zero in measure. -/
theorem tendstoInMeasure_zero_of_eventually_ae {f : ℕ → Ω → ℝ}
    (hf : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, f n ω = 0) : TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hf] with n hn
  symm
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hn] with ω hω
  simp [hω, not_le.2 hε]

/-- **Score CLT from the counting-process conditions.** Under `IsCoxCountingProcess`, if the
information compensator at `β₀`, `(1/n) ∑_{k < K n} Δα V(β₀) S⁽⁰⁾(β₀)`, converges in probability
to `v`, then the normalized summed score increments converge in distribution to `N(0, v)`.
The score increments form a martingale difference array (`condExp_scoreIncr`) whose predictable
variation is the information compensator (`condExp_scoreIncr_sq`); bounded covariates and no ties
bound each increment by `2 B / √n`, so the conditional Lindeberg condition holds, and the
martingale CLT `tendstoInDistribution_martingale_condVar` applies. -/
theorem tendstoInDistribution_sum_scoreIncr (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) {v : NNReal}
    (hcomp : TendstoInMeasure P
      (fun n ω => infoCompensator (t n ω) (z n ω) (dα n) β₀ β₀ (K n) / n) atTop
      (fun _ => (v : ℝ))) :
    TendstoInDistribution
      (fun (n : ℕ) ω => ∑ k ∈ range (K n), scoreIncr (t n ω) (d n ω) (z n ω) β₀ k / √(n : ℝ))
      atTop id (fun _ => P) (gaussianReal 0 v) := by
  set X : ℕ → ℕ → Ω → ℝ := fun n k ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k / √(n : ℝ)
    with hXdef
  have hXm : ∀ n k, Measurable[F n (k + 1)] (X n k) := fun n k =>
    (h.measurable_scoreIncr n k β₀).div_const _
  have hXL2 : ∀ n k, MemLp (X n k) 2 P := fun n k =>
    memLp_two_of_abs_le ((hXm n k).mono ((F n).le _) le_rfl) (2 * B * n / √(n : ℝ)) fun ω => by
      simp only [hXdef, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_div_of_nonneg_right (h.abs_scoreIncr_le_n n k β₀ ω) (Real.sqrt_nonneg _)
  have hXcond : ∀ n k, P[X n k | F n k] =ᵐ[P] 0 := by
    intro n k
    have hfun : X n k = (√(n : ℝ))⁻¹ • fun ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k := by
      funext ω
      simp [hXdef, div_eq_inv_mul]
    rw [hfun]
    filter_upwards [condExp_smul (μ := P) (√(n : ℝ))⁻¹
      (fun ω => scoreIncr (t n ω) (d n ω) (z n ω) β₀ k) (F n k), h.condExp_scoreIncr n k] with
      ω h1 h2
    rw [h1, Pi.smul_apply, h2]
    simp
  have hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) P := by
    intro n
    refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_)
      (fun k => memLp_finsetSum _ (fun j _ => hXL2 n j) |>.integrable one_le_two) (fun k => ?_)
    · exact Finset.stronglyMeasurable_fun_sum _ fun j hj =>
        ((hXm n j).mono ((F n).mono (by simp at hj; omega)) le_rfl).stronglyMeasurable
    · have hdiff : ((fun ω => ∑ j ∈ range (k + 1), X n j ω) - fun ω => ∑ j ∈ range k, X n j ω) =
          X n k := by
        funext ω
        simp [sum_range_succ]
      rw [hdiff]
      exact hXcond n k
  have hpqv : TendstoInMeasure P (fun n => predictableQuadraticVariation P (F n)
      (fun k ω => ∑ j ∈ range k, X n j ω) (K n)) atTop (fun _ => (v : ℝ)) := by
    refine hcomp.congr (fun n => ?_) (ae_of_all _ fun _ => rfl)
    have hk : ∀ᵐ ω ∂P, ∀ k, P[fun ω' => (∑ j ∈ range (k + 1), X n j ω' -
        ∑ j ∈ range k, X n j ω') ^ 2 | F n k] ω =
          (n : ℝ)⁻¹ * (dα n k * (wVar (atRiskInd (t n ω) k) (z n ω) β₀ *
            wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀)) := by
      rw [ae_all_iff]
      intro k
      have hfun : (fun ω' => (∑ j ∈ range (k + 1), X n j ω' - ∑ j ∈ range k, X n j ω') ^ 2) =
          (n : ℝ)⁻¹ • fun ω' => scoreIncr (t n ω') (d n ω') (z n ω') β₀ k ^ 2 := by
        funext ω'
        simp only [sum_range_succ, add_sub_cancel_left, hXdef, Pi.smul_apply, smul_eq_mul]
        rw [div_pow, sq_sqrt (Nat.cast_nonneg n), div_eq_inv_mul]
      rw [hfun]
      filter_upwards [condExp_smul (μ := P) (n : ℝ)⁻¹
        (fun ω' => scoreIncr (t n ω') (d n ω') (z n ω') β₀ k ^ 2) (F n k),
        h.condExp_scoreIncr_sq n k] with ω h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    filter_upwards [hk] with ω hω
    simp only [predictableQuadraticVariation]
    rw [sum_congr rfl fun k _ => hω k, ← mul_sum, infoCompensator, div_eq_inv_mul]
    congr 1
    exact sum_congr rfl fun k _ => by ring
  have hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure P (fun n ω => ∑ k ∈ range (K n),
      (P[{ω' | ε < |X n k ω'|}.indicator (fun ω' => X n k ω' ^ 2) | F n k]) ω) atTop
      (fun _ => 0) := by
    intro ε hε
    refine tendstoInMeasure_zero_of_eventually_ae ?_
    have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqrt.eventually_gt_atTop (2 * B / ε)] with n hn
    have hpos : 0 < √(n : ℝ) := lt_of_le_of_lt (div_nonneg (by linarith [h.bound_nonneg])
      hε.le) hn
    have hsmall : ∀ᵐ ω ∂P, ∀ k, ¬ ε < |X n k ω| := by
      filter_upwards [h.no_ties n] with ω hω k
      rw [not_lt]
      have h1 := abs_scoreIncr_le (t n ω) (d n ω) (h.covariate_bound n ω) h.bound_nonneg β₀ k
      have h2 : |scoreIncr (t n ω) (d n ω) (z n ω) β₀ k| ≤ 2 * B :=
        h1.trans (by nlinarith [hω k, h.bound_nonneg])
      simp only [hXdef, abs_div, abs_of_pos hpos]
      rw [div_le_iff₀ hpos]
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    have hzero : ∀ᵐ ω ∂P, ∀ k, (P[{ω' | ε < |X n k ω'|}.indicator (fun ω' => X n k ω' ^ 2) |
        F n k]) ω = 0 := by
      rw [ae_all_iff]
      intro k
      have hae : {ω' | ε < |X n k ω'|}.indicator (fun ω' => X n k ω' ^ 2) =ᵐ[P] 0 := by
        filter_upwards [hsmall] with ω hω
        simp [hω k]
      filter_upwards [condExp_congr_ae hae] with ω hω
      rw [hω, condExp_zero, Pi.zero_apply]
    filter_upwards [hzero] with ω hω
    exact sum_eq_zero fun k _ => hω k
  exact MathlibExt.Probability.Martingale.tendstoInDistribution_martingale_condVar X F K hmart
    hXL2 v hpqv hcondL

/-- **The score hypothesis of Andersen–Gill (T145) from counting-process conditions and the
convergence of the information compensator at `β₀`.** If every
observed event lies on the grid steps `1, …, K n` and the information compensator at `β₀`
converges in probability to `v`, then the normalized Cox score `Uₙ(β₀) / √n` of the data
converges in distribution to `N(0, v)`. -/
theorem tendstoInDistribution_coxScore (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n) {v : NNReal}
    (hcomp : TendstoInMeasure P
      (fun n ω => infoCompensator (t n ω) (z n ω) (dα n) β₀ β₀ (K n) / n) atTop
      (fun _ => (v : ℝ))) :
    TendstoInDistribution
      (fun (n : ℕ) ω => coxScore (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) β₀ / √(n : ℝ))
      atTop id (fun _ => P) (gaussianReal 0 v) := by
  have heq : (fun (n : ℕ) ω => coxScore (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) β₀ / √(n : ℝ)) =
      fun (n : ℕ) ω => ∑ k ∈ range (K n), scoreIncr (t n ω) (d n ω) (z n ω) β₀ k / √(n : ℝ) := by
    funext n ω
    rw [← sum_div, sum_range_scoreIncr_eq_coxScore _ _ _ _ _ (hsupp n ω)]
  rw [heq]
  exact tendstoInDistribution_sum_scoreIncr h K hcomp

/-- The score hypothesis in exactly the form of T145's `hscore`: the limit is any random variable
`Z` on any probability space with law `N(0, v)`. -/
theorem tendstoInDistribution_coxScore_of_hasLaw (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n) {v : NNReal}
    (hcomp : TendstoInMeasure P
      (fun n ω => infoCompensator (t n ω) (z n ω) (dα n) β₀ β₀ (K n) / n) atTop
      (fun _ => (v : ℝ)))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => coxScore (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) β₀ / √(n : ℝ))
      atTop Z (fun _ => P) P' := by
  have h0 := tendstoInDistribution_coxScore h K hsupp hcomp
  refine ⟨h0.forall_aemeasurable, hZ.aemeasurable, ?_⟩
  have hlaw : (⟨P'.map Z, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨(gaussianReal 0 v).map id, inferInstance⟩ :=
    Subtype.ext (by simp only [hZ.map_eq, Measure.map_id])
  rw [hlaw]
  exact h0.tendsto

end Score

/-! ### The information limit: Lenglart's inequality and a Lipschitz net -/

section Information

variable {n : ℕ}

/-- The information martingale increment at coefficient `b`, normalized by `n`:
`(V(b, k + 1) / n) (ΔN̄(k + 1) - Δα S⁽⁰⁾(β₀, k + 1))`. Its sum over the grid is the observed
information minus its compensator, divided by `n` (`sum_range_infoMartIncr`). -/
noncomputable def infoMartIncr (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ) (dα : ℕ → ℝ)
    (β₀ b : ℝ) (k : ℕ) : ℝ :=
  wVar (atRiskInd t k) z b / n * (eventCount t d k - dα k * wSum (atRiskInd t k) z 0 β₀)

theorem sum_range_infoMartIncr (t : Fin n → ℕ) (d : Fin n → Bool) (z : Fin n → ℝ) (dα : ℕ → ℝ)
    (β₀ b : ℝ) (K : ℕ) :
    ∑ k ∈ range K, infoMartIncr t d z dα β₀ b k =
      (∑ k ∈ range K, infoIncr t d z b k - infoCompensator t z dα β₀ b K) / n := by
  unfold infoMartIncr infoIncr infoCompensator
  rw [← sum_sub_distrib, sum_div]
  exact sum_congr rfl fun k _ => by ring

end Information

namespace IsCoxCountingProcess

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

omit [IsProbabilityMeasure P] in
theorem measurable_eventCount (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    Measurable[F n (k + 1)] fun ω => eventCount (t n ω) (d n ω) k :=
  Finset.measurable_fun_sum _ fun i _ => (h.event_measurable n k i).measurable

omit [IsProbabilityMeasure P] in
theorem measurable_compIncr (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    Measurable[F n k] fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ :=
  (h.measurable_wSum' n k 0 β₀).const_mul _

omit [IsProbabilityMeasure P] in
theorem compIncr_nonneg (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (ω : Ω) :
    0 ≤ dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ :=
  mul_nonneg (h.hazard_nonneg n k) (wSum_zero_nonneg (atRiskInd_nonneg _ _) β₀)

omit [IsProbabilityMeasure P] in
theorem compIncr_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (ω : Ω) :
    dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ ≤ dα n k * (n * exp (|β₀| * B)) :=
  mul_le_mul_of_nonneg_left (wSum_zero_le (atRiskInd_le_one _ _) (h.covariate_bound n ω) β₀)
    (h.hazard_nonneg n k)

theorem integrable_eventCount (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    Integrable (fun ω => eventCount (t n ω) (d n ω) k) P :=
  integrable_of_abs_le ((h.measurable_eventCount n k).mono ((F n).le _) le_rfl) n fun ω => by
    rw [abs_of_nonneg (eventCount_nonneg _ _ _)]; exact eventCount_le _ _ _

theorem integrable_compIncr (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    Integrable (fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) P :=
  integrable_of_abs_le ((h.measurable_compIncr n k).mono ((F n).le _) le_rfl)
    (dα n k * (n * exp (|β₀| * B))) fun ω => by
      rw [abs_of_nonneg (h.compIncr_nonneg n k ω)]; exact h.compIncr_le n k ω

/-- The compensator of the total counting process: `E[ΔN̄(k + 1) | F_k] = Δα S⁽⁰⁾(β₀, k + 1)`. -/
theorem condExp_eventCount (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    P[fun ω => eventCount (t n ω) (d n ω) k | F n k] =ᵐ[P]
      fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ := by
  have hfun : (fun ω => eventCount (t n ω) (d n ω) k) =
      fun ω => ∑ i, (1 : ℝ) * eventInd (t n ω) (d n ω) k i := by
    funext ω
    simp [eventCount]
  rw [hfun]
  filter_upwards [h.condExp_sum_mul_eventInd n k (a := fun _ _ => 1) (fun _ => measurable_const)
    (C := 1) (fun _ _ => by simp)] with ω hω
  rw [hω, wSum, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- **The information martingale has conditional mean zero.** For a predictable bounded `g`,
`E[g (ΔN̄ - Δα S⁽⁰⁾(β₀)) | F_k] = 0`. -/
theorem condExp_mul_eventCount_sub (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ)
    {g : Ω → ℝ} (hg : Measurable[F n k] g) {C : ℝ} (hC : 0 ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    P[fun ω => g ω * (eventCount (t n ω) (d n ω) k -
      dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) | F n k] =ᵐ[P] 0 := by
  have hg0 : Measurable g := hg.mono ((F n).le k) le_rfl
  have hI1 : Integrable (g * fun ω => eventCount (t n ω) (d n ω) k) P :=
    integrable_of_abs_le (hg0.mul ((h.measurable_eventCount n k).mono ((F n).le _) le_rfl))
      (C * n) fun ω => by
        rw [Pi.mul_apply, abs_mul, abs_of_nonneg (eventCount_nonneg _ _ _)]
        exact mul_le_mul (hgC ω) (eventCount_le _ _ _) (eventCount_nonneg _ _ _) hC
  have hI2 : Integrable (g * fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) P :=
    integrable_of_abs_le (hg0.mul ((h.measurable_compIncr n k).mono ((F n).le _) le_rfl))
      (C * (dα n k * (n * exp (|β₀| * B)))) fun ω => by
        rw [Pi.mul_apply, abs_mul, abs_of_nonneg (h.compIncr_nonneg n k ω)]
        exact mul_le_mul (hgC ω) (h.compIncr_le n k ω) (h.compIncr_nonneg n k ω) hC
  have hfun : (fun ω => g ω * (eventCount (t n ω) (d n ω) k -
      dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀)) =
      (g * fun ω => eventCount (t n ω) (d n ω) k) -
        g * fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ := by
    funext ω
    simp [mul_sub]
  rw [hfun]
  have h2 : P[g * fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ | F n k] =
      g * fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ :=
    condExp_of_stronglyMeasurable ((F n).le k)
      (hg.mul (h.measurable_compIncr n k)).stronglyMeasurable
      hI2
  filter_upwards [condExp_sub hI1 hI2 (F n k), condExp_mul_of_stronglyMeasurable_left
    hg.stronglyMeasurable hI1 (h.integrable_eventCount n k), h.condExp_eventCount n k] with
    ω e1 e2 e3
  rw [e1, Pi.sub_apply, e2, h2, Pi.mul_apply, e3, Pi.mul_apply, sub_self, Pi.zero_apply]

omit [IsProbabilityMeasure P] in
theorem measurable_infoMartIncr (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ) :
    Measurable[F n (k + 1)] fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k :=
  (((h.measurable_wVar' n k b).div_const _).mono ((F n).mono (Nat.le_succ k)) le_rfl).mul
    ((h.measurable_eventCount n k).sub
      ((h.measurable_compIncr n k).mono ((F n).mono (Nat.le_succ k)) le_rfl))

omit [IsProbabilityMeasure P] in
theorem abs_infoMartIncr_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ)
    (ω : Ω) : |infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k| ≤
      B ^ 2 / n * (n + dα n k * (n * exp (|β₀| * B))) := by
  unfold infoMartIncr
  rw [abs_mul, abs_div, Nat.abs_cast]
  refine mul_le_mul (div_le_div_of_nonneg_right
    (abs_wVar_le (atRiskInd_nonneg _ _) (h.covariate_bound n ω) h.bound_nonneg b)
    (Nat.cast_nonneg n)) ?_ (abs_nonneg _) (by positivity)
  calc |eventCount (t n ω) (d n ω) k - dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀|
      ≤ |eventCount (t n ω) (d n ω) k| + |dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀| :=
        abs_sub _ _
    _ ≤ n + dα n k * (n * exp (|β₀| * B)) := by
        rw [abs_of_nonneg (eventCount_nonneg _ _ _), abs_of_nonneg (h.compIncr_nonneg n k ω)]
        exact add_le_add (eventCount_le _ _ _) (h.compIncr_le n k ω)

theorem condExp_infoMartIncr (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) (b : ℝ) :
    P[fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k | F n k] =ᵐ[P] 0 :=
  h.condExp_mul_eventCount_sub n k (g := fun ω => wVar (atRiskInd (t n ω) k) (z n ω) b / n)
    ((h.measurable_wVar' n k b).div_const _) (C := B ^ 2 / n) (by positivity) fun ω => by
      rw [abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right
        (abs_wVar_le (atRiskInd_nonneg _ _) (h.covariate_bound n ω) h.bound_nonneg b)
        (Nat.cast_nonneg n)

/-- Under no ties the compensator increment is at most one almost surely. -/
theorem ae_compIncr_le_one (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ) :
    ∀ᵐ ω ∂P, dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ ≤ 1 := by
  have hmono : P[fun ω => eventCount (t n ω) (d n ω) k | F n k] ≤ᵐ[P]
      P[fun _ => (1 : ℝ) | F n k] := by
    refine condExp_mono (h.integrable_eventCount n k) (integrable_const 1) ?_
    filter_upwards [h.no_ties n] with ω hω
    exact hω k
  filter_upwards [hmono, h.condExp_eventCount n k] with ω h1 h2
  rw [h2, condExp_const ((F n).le k)] at h1
  exact h1

/-- **Predictable variation of the information martingale.** Under no ties,
`E[(ΔM_b)² | F_k] ≤ (2 B⁴ / n²) Δα S⁽⁰⁾(β₀)`. -/
theorem condExp_infoMartIncr_sq_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n k : ℕ)
    (b : ℝ) : P[fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2 | F n k] ≤ᵐ[P]
      fun ω => 2 * B ^ 4 / (n : ℝ) ^ 2 * (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) := by
  set κ : ℝ := (B ^ 2 / n) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := sq_nonneg _
  have hNI := h.integrable_eventCount n k
  have hA0 : Measurable fun ω => dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ :=
    (h.measurable_compIncr n k).mono ((F n).le _) le_rfl
  have hA2I : Integrable (fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2) P :=
    integrable_of_abs_le (hA0.pow_const 2) ((dα n k * (n * exp (|β₀| * B))) ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (by
        rw [abs_of_nonneg (h.compIncr_nonneg n k ω)]; exact h.compIncr_le n k ω) 2
  have hζI : Integrable (fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2) P :=
    integrable_of_abs_le (((h.measurable_infoMartIncr n k b).mono ((F n).le _) le_rfl).pow_const 2)
      ((B ^ 2 / n * (n + dα n k * (n * exp (|β₀| * B)))) ^ 2) fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_infoMartIncr_le n k b ω) 2
  have hle : (fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2) ≤ᵐ[P]
      κ • ((fun ω => eventCount (t n ω) (d n ω) k) +
        fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2) := by
    filter_upwards [h.no_ties n] with ω hω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, infoMartIncr]
    set N := eventCount (t n ω) (d n ω) k
    set A := dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀
    set V := wVar (atRiskInd (t n ω) k) (z n ω) b
    have hN0 : 0 ≤ N := eventCount_nonneg _ _ _
    have hN1 : N ≤ 1 := hω k
    have hA : 0 ≤ A := h.compIncr_nonneg n k ω
    have hV : (V / n) ^ 2 ≤ κ := by
      rw [hκ, ← sq_abs (V / n)]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_div, Nat.abs_cast]
      exact div_le_div_of_nonneg_right
        (abs_wVar_le (atRiskInd_nonneg _ _) (h.covariate_bound n ω) h.bound_nonneg b)
        (Nat.cast_nonneg n)
    have hD : (N - A) ^ 2 ≤ N + A ^ 2 := by nlinarith
    rw [mul_pow]
    exact mul_le_mul hV hD (sq_nonneg _) hκ0
  have hRI : Integrable (κ • ((fun ω => eventCount (t n ω) (d n ω) k) +
      fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2)) P :=
    (hNI.add hA2I).smul κ
  have hA2 : P[fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2 | F n k] =
      fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2 :=
    condExp_of_stronglyMeasurable ((F n).le k)
      ((h.measurable_compIncr n k).pow_const 2).stronglyMeasurable
      hA2I
  filter_upwards [condExp_mono (m := F n k) hζI hRI hle, condExp_smul (μ := P) κ
    ((fun ω => eventCount (t n ω) (d n ω) k) +
      fun ω => (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) ^ 2) (F n k),
    condExp_add hNI hA2I (F n k), h.condExp_eventCount n k, h.ae_compIncr_le_one n k] with
    ω e1 e2 e3 e4 e5
  rw [e2, Pi.smul_apply, e3, Pi.add_apply, e4, hA2, smul_eq_mul] at e1
  refine e1.trans ?_
  have hA := h.compIncr_nonneg n k ω
  set A := dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀
  have hκeq : κ = B ^ 4 / (n : ℝ) ^ 2 := by rw [hκ, div_pow, ← pow_mul]
  rw [hκeq]
  have hB4 : 0 ≤ B ^ 4 / (n : ℝ) ^ 2 := by positivity
  calc B ^ 4 / (n : ℝ) ^ 2 * (A + A ^ 2) ≤ B ^ 4 / (n : ℝ) ^ 2 * (A + A) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hB4
    _ = 2 * B ^ 4 / (n : ℝ) ^ 2 * A := by ring

omit [IsProbabilityMeasure P] in
theorem totalCompensator_nonneg (h : IsCoxCountingProcess P F t d z dα β₀ B) (n K : ℕ) (ω : Ω) :
    0 ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ K :=
  sum_nonneg fun k _ => h.compIncr_nonneg n k ω

/-- `E[Ā(K)] = E[N̄(K)] ≤ n`: the compensator has the mean of the counting process, and each
subject has at most one event. -/
theorem integral_totalCompensator_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n K : ℕ) :
    ∫ ω, totalCompensator (t n ω) (z n ω) (dα n) β₀ K ∂P ≤ n := by
  unfold totalCompensator
  rw [integral_finsetSum _ fun k _ => h.integrable_compIncr n k]
  have hk : ∀ k, ∫ ω, dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ ∂P =
      ∫ ω, eventCount (t n ω) (d n ω) k ∂P := by
    intro k
    rw [← integral_condExp ((F n).le k) (f := fun ω => eventCount (t n ω) (d n ω) k)]
    exact integral_congr_ae (h.condExp_eventCount n k).symm
  rw [sum_congr rfl fun k _ => hk k, ← integral_finsetSum _ fun k _ => h.integrable_eventCount n k]
  calc ∫ ω, ∑ k ∈ range K, eventCount (t n ω) (d n ω) k ∂P ≤ ∫ _ω, (n : ℝ) ∂P :=
        integral_mono (integrable_finsetSum _ fun k _ => h.integrable_eventCount n k)
          (integrable_const _) fun ω => sum_range_eventCount_le _ _ _
    _ = n := by simp

/-- Markov's inequality for the total compensator: `P(Ā(K) ≥ s) ≤ n / s`. -/
theorem measure_le_totalCompensator_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n K : ℕ)
    {s : ℝ} (hs : 0 < s) :
    P {ω | s ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ K} ≤ ENNReal.ofReal (n / s) := by
  have hI : Integrable (fun ω => totalCompensator (t n ω) (z n ω) (dα n) β₀ K) P :=
    integrable_finsetSum _ fun k _ => h.integrable_compIncr n k
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => h.totalCompensator_nonneg n K ω) hI s
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hs, mul_comm]
  exact hm.trans (h.integral_totalCompensator_le n K)

/-- **Lenglart bound for the information martingale at a fixed coefficient.** -/
theorem measure_le_abs_sum_infoMartIncr_le (h : IsCoxCountingProcess P F t d z dα β₀ B) {n : ℕ}
    (hn : 0 < n) (K : ℕ) (b : ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    P {ω | ε ≤ |∑ k ∈ range K, infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k|} ≤
      ENNReal.ofReal ((2 * B ^ 4 + 1) / (η * n)) + ENNReal.ofReal (η / ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := measure_le_abs_sum_le (P := P) (F := F n)
    (x := fun k ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k)
    (fun k => (h.measurable_infoMartIncr n k b).stronglyMeasurable)
    (fun k => h.condExp_infoMartIncr n k b)
    (fun k => memLp_two_of_abs_le ((h.measurable_infoMartIncr n k b).mono ((F n).le _) le_rfl) _
      (h.abs_infoMartIncr_le n k b)) K hε hη
  refine hL.trans (add_le_add ?_ le_rfl)
  set C : ℝ := 2 * B ^ 4 + 1 with hC
  have hCpos : 0 < C := by positivity
  have hsub : {ω | η < ∑ k ∈ range K,
      (P[fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2 | F n k]) ω} ≤ᵐ[P]
      {ω | η * n ^ 2 / C ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ K} := by
    have hall : ∀ᵐ ω ∂P, ∀ k,
        (P[fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2 | F n k]) ω ≤
          2 * B ^ 4 / (n : ℝ) ^ 2 * (dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) :=
      ae_all_iff.2 fun k => h.condExp_infoMartIncr_sq_le n k b
    filter_upwards [hall] with ω hω hmem
    change η < ∑ k ∈ range K,
      (P[fun ω => infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k ^ 2 | F n k]) ω at hmem
    have hsum := sum_le_sum fun k (_ : k ∈ range K) => hω k
    rw [← mul_sum] at hsum
    have hA := h.totalCompensator_nonneg n K ω
    unfold totalCompensator
    rw [div_le_iff₀ hCpos]
    have h1 : η < 2 * B ^ 4 / (n : ℝ) ^ 2 *
        ∑ k ∈ range K, dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ := hmem.trans_le hsum
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at h1
    unfold totalCompensator at hA
    nlinarith
  calc _ ≤ P {ω | η * n ^ 2 / C ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ K} :=
        measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (n / (η * n ^ 2 / C)) :=
        h.measure_le_totalCompensator_le n K (by positivity)
    _ = ENNReal.ofReal (C / (η * n)) := by
        congr 1
        field_simp

/-- **Pointwise convergence of the information martingale** (Lenglart): for each coefficient
`b`, `(I_n(b) - compensator) / n → 0` in probability. -/
theorem tendsto_measure_le_abs_sum_infoMartIncr (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ε ≤
      |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨κ₀, -, hκ₀pos, hκ₀lt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hκ
  have hκ₀ : 0 < κ₀ := ENNReal.ofReal_pos.1 hκ₀pos
  set η : ℝ := κ₀ * ε ^ 2 / 2 with hηdef
  have hη : 0 < η := by positivity
  have hlim : Tendsto (fun n : ℕ => (2 * B ^ 4 + 1) / (η * n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hη)
  filter_upwards [hlim.eventually (Iic_mem_nhds (half_pos hκ₀)), eventually_gt_atTop 0] with
    n hn hn0
  calc _ ≤ ENNReal.ofReal ((2 * B ^ 4 + 1) / (η * n)) + ENNReal.ofReal (η / ε ^ 2) :=
        h.measure_le_abs_sum_infoMartIncr_le hn0 (K n) b hε hη
    _ ≤ ENNReal.ofReal (κ₀ / 2) + ENNReal.ofReal (κ₀ / 2) := by
        refine add_le_add (ENNReal.ofReal_le_ofReal hn) (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        rw [hηdef]
        field_simp
    _ = ENNReal.ofReal κ₀ := by
        rw [← ENNReal.ofReal_add (half_pos hκ₀).le (half_pos hκ₀).le, add_halves]
    _ ≤ κ := hκ₀lt.le

omit [IsProbabilityMeasure P] in
/-- **Lipschitz dependence of the information martingale on the coefficient.** -/
theorem abs_sum_infoMartIncr_sub_le (h : IsCoxCountingProcess P F t d z dα β₀ B) {n : ℕ}
    (hn : 0 < n) (K : ℕ) (b b' : ℝ) (ω : Ω) :
    |∑ k ∈ range K, infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k -
      ∑ k ∈ range K, infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b' k| ≤
      6 * B ^ 3 * |b - b'| * (1 + totalCompensator (t n ω) (z n ω) (dα n) β₀ K / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℝ := 6 * B ^ 3 * |b - b'| with hLdef
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h.bound_nonneg 3))
    (abs_nonneg _)
  have hterm : ∀ k, |infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k -
      infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b' k| ≤
        L / n * (eventCount (t n ω) (d n ω) k +
          dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) := by
    intro k
    unfold infoMartIncr
    rw [← sub_mul, ← sub_div, abs_mul, abs_div, Nat.abs_cast]
    have hV := abs_wVar_sub_le (atRiskInd_nonneg (t n ω) k) (h.covariate_bound n ω)
      h.bound_nonneg b b'
    have hD : |eventCount (t n ω) (d n ω) k - dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀| ≤
        eventCount (t n ω) (d n ω) k + dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ := by
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_of_nonneg (eventCount_nonneg _ _ _), abs_of_nonneg (h.compIncr_nonneg n k ω)]
    exact mul_le_mul (div_le_div_of_nonneg_right hV hn'.le) hD (abs_nonneg _)
      (div_nonneg hL hn'.le)
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ k ∈ range K, |infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k -
        infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b' k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range K, L / n * (eventCount (t n ω) (d n ω) k +
        dα n k * wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀) := sum_le_sum fun k _ => hterm k
    _ = L / n * (∑ k ∈ range K, eventCount (t n ω) (d n ω) k +
        totalCompensator (t n ω) (z n ω) (dα n) β₀ K) := by
        rw [← mul_sum, sum_add_distrib, totalCompensator]
    _ ≤ L / n * (n + totalCompensator (t n ω) (z n ω) (dα n) β₀ K) :=
        mul_le_mul_of_nonneg_left (add_le_add_left (sum_range_eventCount_le _ _ _) _)
          (div_nonneg hL hn'.le)
    _ = L * (1 + totalCompensator (t n ω) (z n ω) (dα n) β₀ K / n) := by
        field_simp

/-- **Uniform convergence of the information martingale on a neighborhood.** For every
`η > 0`, `P(∃ b ∈ [β₀ - r, β₀ + r], |I_n(b) - compensator| / n ≥ η) → 0`. Lenglart's inequality
gives the convergence at each point of a finite net of mesh `h`; the Lipschitz bound
`abs_sum_infoMartIncr_sub_le` and Markov's inequality for `Ā / n` control the oscillation
between net points. -/
theorem tendsto_measure_exists_abs_sum_infoMartIncr (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (r : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r), η ≤
      |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨κ₀, -, hκ₀pos, hκ₀lt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hκ
  have hκ₀ : 0 < κ₀ := ENNReal.ofReal_pos.1 hκ₀pos
  set M : ℝ := 2 / κ₀ with hMdef
  have hM : 0 < M := by positivity
  set L : ℝ := 6 * B ^ 3 with hLdef
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (pow_nonneg h.bound_nonneg 3)
  set hs : ℝ := η / (2 * (L + 1) * (1 + M)) with hsdef
  have hs0 : 0 < hs := div_pos hη (by positivity)
  have hLs : L * hs * (1 + M) ≤ η / 2 := by
    rw [hsdef]
    have h1 : L * (η / (2 * (L + 1) * (1 + M))) * (1 + M) = η / 2 * (L / (L + 1)) := by
      field_simp
    rw [h1]
    have h2 : L / (L + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    nlinarith
  set J : ℕ := ⌈2 * r / hs⌉₊ with hJ
  set grid : ℕ → ℝ := fun j => β₀ - r + j * hs with hgrid
  have hnet : Tendsto (fun n : ℕ => ∑ j ∈ range (J + 1), P {ω | η / 2 ≤
      |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ (grid j) k|}) atTop
      (𝓝 0) := by
    have := tendsto_finsetSum (range (J + 1)) fun j _ =>
      h.tendsto_measure_le_abs_sum_infoMartIncr K (grid j) (half_pos hη)
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hnet) (ENNReal.ofReal (κ₀ / 2))
    (ENNReal.ofReal_pos.2 (half_pos hκ₀)), eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hMarkov : P {ω | M ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n} ≤
      ENNReal.ofReal (κ₀ / 2) := by
    calc _ ≤ P {ω | M * n ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n)} :=
          measure_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω ⊢
            rwa [le_div_iff₀ hn'] at hω
      _ ≤ ENNReal.ofReal (n / (M * n)) := h.measure_le_totalCompensator_le n (K n) (by positivity)
      _ = ENNReal.ofReal (κ₀ / 2) := by
          congr 1
          rw [hMdef]
          field_simp
  calc _ ≤ P ({ω | M ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n} ∪
        ⋃ j ∈ range (J + 1), {ω | η / 2 ≤
          |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ (grid j) k|}) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨b, hb, hbη⟩ := hω
        by_cases hA : M ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n
        · exact Or.inl hA
        right
        push Not at hA
        set x : ℝ := (b - (β₀ - r)) / hs with hx
        have hx0 : 0 ≤ x := div_nonneg (by linarith [hb.1]) hs0.le
        set j : ℕ := ⌊x⌋₊ with hj
        have hj1 : (j : ℝ) * hs ≤ b - (β₀ - r) := (le_div_iff₀ hs0).1 (Nat.floor_le hx0)
        have hj2 : b - (β₀ - r) < ((j : ℝ) + 1) * hs := (div_lt_iff₀ hs0).1 (Nat.lt_floor_add_one x)
        have hjJ : j ≤ J := (Nat.floor_le_floor (div_le_div_of_nonneg_right
          (by linarith [hb.2]) hs0.le)).trans (Nat.floor_le_ceil _)
        refine Set.mem_biUnion (mem_range.2 (Nat.lt_succ_of_le hjJ)) ?_
        simp only [Set.mem_ofPred_eq]
        have hdist : |b - grid j| ≤ hs := by
          rw [hgrid, abs_le]
          constructor <;> nlinarith
        have hlip := h.abs_sum_infoMartIncr_sub_le hn0 (K n) b (grid j) ω
        have hbound : 6 * B ^ 3 * |b - grid j| *
            (1 + totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n) ≤ η / 2 := by
          have hA0 : 0 ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n :=
            div_nonneg (h.totalCompensator_nonneg n (K n) ω) hn'.le
          calc 6 * B ^ 3 * |b - grid j| *
              (1 + totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n)
              ≤ L * hs * (1 + M) := by
                rw [← hLdef]
                exact mul_le_mul (mul_le_mul_of_nonneg_left hdist hL) (by linarith)
                  (by positivity) (mul_nonneg hL hs0.le)
            _ ≤ η / 2 := hLs
        have := abs_sub_abs_le_abs_sub
          (∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k)
          (∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ (grid j) k)
        linarith
    _ ≤ P {ω | M ≤ totalCompensator (t n ω) (z n ω) (dα n) β₀ (K n) / n} +
        ∑ j ∈ range (J + 1), P {ω | η / 2 ≤
          |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ (grid j) k|} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (κ₀ / 2) + ENNReal.ofReal (κ₀ / 2) := add_le_add hMarkov hn
    _ = ENNReal.ofReal κ₀ := by
        rw [← ENNReal.ofReal_add (half_pos hκ₀).le (half_pos hκ₀).le, add_halves]
    _ ≤ κ := hκ₀lt.le

end IsCoxCountingProcess

/-! ### The two Andersen–Gill limit hypotheses (T145) -/

section AndersenGill

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

/-- **The uniform-information hypothesis of Andersen–Gill (T145) from counting-process conditions
and the uniform information-compensator limit.** Under `IsCoxCountingProcess`, with every observed
event on the grid steps `1, …, K n`, if the information compensator converges uniformly in
probability on `[β₀ - r, β₀ + r]` to `i`, then so does the observed information `Iₙ(b) / n`
(`coxInformation`): the difference is the information martingale, which vanishes uniformly by
`tendsto_measure_exists_abs_sum_infoMartIncr` (Lenglart's inequality on a Lipschitz net). The
conclusion is T145's hypothesis `hinfo` verbatim. -/
theorem tendsto_measure_exists_coxInformation (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    {i : ℝ → ℝ} {r : ℝ}
    (hcomp : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b|}) atTop (𝓝 0)) :
    ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) b / n - i b|}) atTop (𝓝 0) := by
  intro η hη
  have hAB := (h.tendsto_measure_exists_abs_sum_infoMartIncr K r (half_pos hη)).add
    (hcomp (η / 2) (half_pos hη))
  rw [add_zero] at hAB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAB (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  obtain ⟨b, hb, hbη⟩ := hω
  have hsplit : coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) b / n - i b =
      ∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k +
        (infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b) := by
    rw [sum_range_infoMartIncr, sum_range_infoIncr_eq_coxInformation _ _ _ _ _ (hsupp n ω)]
    ring
  rw [hsplit] at hbη
  have htri := abs_add_le (∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k)
    (infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b)
  by_cases h1 : η / 2 ≤ |∑ k ∈ range (K n), infoMartIncr (t n ω) (d n ω) (z n ω) (dα n) β₀ b k|
  · exact Or.inl ⟨b, hb, h1⟩
  · exact Or.inr ⟨b, hb, by linarith⟩

omit [IsProbabilityMeasure P] in
/-- Uniform convergence of the information compensator near `β₀` to `i` with `i β₀ = v`
gives convergence in probability of the compensator at `β₀` to `v`. -/
theorem tendstoInMeasure_infoCompensator_of_uniform (K : ℕ → ℕ) {i : ℝ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) {v : NNReal} (hiv : i β₀ = v)
    (hcomp : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b|}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => infoCompensator (t n ω) (z n ω) (dα n) β₀ β₀ (K n) / n) atTop
      (fun _ => (v : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hcomp ε hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  refine ⟨β₀, ⟨by linarith, by linarith⟩, ?_⟩
  have : ε ≤ dist (infoCompensator (t n ω) (z n ω) (dα n) β₀ β₀ (K n) / n) (v : ℝ) := hω
  rwa [Real.dist_eq, ← hiv] at this

/-- **Both Andersen–Gill limit hypotheses (T145) from counting-process conditions and the
uniform information-compensator limit.** Under the
discrete-time Cox counting-process conditions `IsCoxCountingProcess` (Cox intensity, bounded
covariates, no ties), with every observed event on the grid steps `1, …, K n`, assume the
information compensator `(1/n) ∑_{k < K n} Δα V(b) S⁽⁰⁾(β₀)` converges uniformly in probability on
`[β₀ - r, β₀ + r]` (`r ≥ 0`) to a function `i` with `i β₀ = v`. Then, for any `Z ~ N(0, v)`:

* (score CLT, T145's `hscore`) `Uₙ(β₀) / √n ⟶ Z` in distribution, and
* (uniform information, T145's `hinfo`) `P(∃ b ∈ [β₀ - r, β₀ + r], |Iₙ(b) / n - i(b)| ≥ η) → 0`
  for every `η > 0`.

The score is a martingale under the Cox intensity whose predictable variation is the
information compensator at `β₀` (the information identity); the martingale CLT under the
conditional Lindeberg condition gives the first statement. The observed information minus its
compensator is a martingale whose predictable variation is `O(Ā / n²)`; Lenglart's inequality
and a Lipschitz net give the second. -/
theorem andersenGill_hypotheses_of_tendsto_infoCompensator
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (K : ℕ → ℕ) (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    {i : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) {v : NNReal} (hiv : i β₀ = v)
    (hcomp : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b|}) atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => coxScore (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) β₀ / √(n : ℝ))
      atTop Z (fun _ => P) P' ∧
    ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) b / n - i b|}) atTop (𝓝 0) :=
  ⟨tendstoInDistribution_coxScore_of_hasLaw h K hsupp
      (tendstoInMeasure_infoCompensator_of_uniform K hr hiv hcomp) hZ,
    tendsto_measure_exists_coxInformation h K hsupp hcomp⟩

end AndersenGill

end MathlibExt.Probability.Statistics.CoxCountingProcessConditions
