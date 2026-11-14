/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGray
public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics

/-!
# Fine–Gray regression: consistency and asymptotic normality

The Fine–Gray estimator of the subdistribution-hazard coefficient maximizes the
inverse-probability-of-censoring weighted partial likelihood `fgWeightedPartialLikelihood` of
`FineGray` (Fine and Gray 1999, Section 3). For a scalar covariate `z` and the weights
`w_l(X_i) = fgWeight X ε c G l i` (`1` while `l` is under observation, `G(X_i) / G(X_l)` after a
competing event of `l`, `0` otherwise), write

* `S_k(b, i) = ∑_l w_l(X_i) z_l^k exp (b z_l)` (`fgWeightedSum`),
* `z̄(b, i) = S_1 / S_0` and `V(b, i) = S_2 / S_0 - z̄²` (`fgMean`, `fgVar`),
* `ℓ(b) = ∑_{i : εᵢ = c} (b zᵢ - log S_0(b, i))` (`fgLogPartialLikelihood₁`),
* `U(b) = ∑_{i : εᵢ = c} (zᵢ - z̄(b, i))` (the **Fine–Gray score**, `fgScore`),
* `I(b) = ∑_{i : εᵢ = c} V(b, i)` (the **Fine–Gray observed information**, `fgInformation`).

For a nonnegative censoring survival `G`, `ℓ` is the logarithm of the weighted partial
likelihood (`log_fgWeightedPartialLikelihood`), `U = ℓ'` and `I = -U' ≥ 0`
(`isConcaveScore_fg`).

## The Fine–Gray regularity conditions

For each `n` the data `(Xᵢ, εᵢ, zᵢ)_{i < n}` and the weight function `G n` (in practice the
Kaplan–Meier estimate of the censoring survival) are random. `FineGrayConditions` collects:

* `weight_nonneg`: `G n ω t ≥ 0`;
* `score`: `Uₙ(β₀) / √n ⟶ Z` in distribution;
* `info_unif`: on `[β₀ - r, β₀ + r]` (`r > 0`), `sup_b |Iₙ(b) / n - i(b)| → 0` in probability,
  stated without measurability as `P {ω | ∃ b ∈ [β₀ - r, β₀ + r], η ≤ |Iₙ(b) / n - i(b)|} → 0`;
* `info_continuousAt`, `info_eq`, `info_ne_zero`: `i` is continuous at `β₀` and `i(β₀) = v ≠ 0`.

Unlike Cox regression, the score limit is **not** assumed to have variance `v`: the weighted
score is not a martingale, and estimating `G` adds a term to its variance. In Fine and Gray's
notation the score has limit `N(0, Σ)` and the information limit is `Ω`, and the estimator has
the sandwich variance `Ω⁻¹ Σ Ω⁻¹`; here `Σ = σ²` and `Ω = v`.

## Main results

* `tendsto_measure_not_exists_isMaxOn_fg`: with probability tending to one the weighted log
  partial likelihood has a maximizer.
* `tendstoInMeasure_fgMPLE` (**consistency**): `βhat n → β₀` in probability.
* `tendstoInDistribution_fgMPLE`: `√n (βhat n - β₀) ⟶ Z / v` for any score limit `Z`.
* `tendstoInDistribution_fgMPLE_gaussian` (**asymptotic normality**): if `Z ~ N(0, σ²)` then
  `√n (βhat n - β₀) ⟶ Z / v ~ N(0, σ² / v²)`.
* `tendstoInMeasure_fgInformation_fgMPLE`: `Iₙ(βhat n) / n → v` in probability.
* `fgScore_eq_coxScore_of_noCompeting`, `fgInformation_eq_coxInformation_of_noCompeting`,
  `fgLogPartialLikelihood₁_eq_of_noCompeting`: without competing events the Fine–Gray score,
  information and criterion are Cox's, for every `G`.

The asymptotics are instances of the abstract results for a concave criterion
(`IsConcaveScore`: `ℓ' = U`, `U' = -I`, `I ≥ 0`) in `ConcaveScore`, which carries the
Andersen–Gill argument with the score variance decoupled from the information limit;
`CoxAsymptotics` is built on the same results (`isConcaveScore_cox`).

## Scope

Scalar covariate only. The two limit hypotheses `score` and `info_unif` are assumptions; their
derivation from the Fine–Gray conditions (the i.i.d. representation of the weighted score
including the `ψ` terms from the Kaplan–Meier estimate of `G`, the functional delta method for
`Ĝ`, uniform laws for `S_k / n`) is not formalized, nor is a consistent estimator of the
sandwich variance `σ² / v²`. A model-based Wald interval with `1 / I(βhat)` is not asymptotically
valid here and is not stated.

## Source receipt

* J. P. Fine and R. J. Gray, *A proportional hazards model for the subdistribution of a
  competing risk*, J. Amer. Statist. Assoc. 94 (1999), 496–509, Section 3 (weighted score and
  information; consistency and asymptotic normality with variance `Ω⁻¹ Σ Ω⁻¹`).
* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3 (the argument).
* Reused, not reproved: `fgWeight`, `fgWeightedPartialLikelihood`, `causeIndicator` from
  `FineGray`; `riskSet`, `coxScore`, `coxInformation`, `logPartialLikelihood₁` from
  `CoxPartialLikelihood`; `IsConcaveScore`, `tendstoInMeasure_argmax`,
  `tendstoInDistribution_argmax`, `tendstoInMeasure_info_argmax` from `ConcaveScore`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGrayAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptotics
open MathlibExt.Probability.Statistics.ConcaveScore

/-! ### Gaussian limit with a decoupled score variance -/

section GaussianLimit

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {Z : Ω' → ℝ}

/-- Dividing a centered Gaussian of variance `σ²` by `v ≠ 0` gives variance `σ² / v²`. -/
theorem hasLaw_div_gaussianReal_sq {σ2 v : NNReal}
    (hZ : HasLaw Z (gaussianReal 0 σ2) P') :
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 (σ2 / v ^ 2)) P' := by
  have h : HasLaw (fun x : ℝ => x / (v : ℝ)) (gaussianReal 0 (σ2 / v ^ 2)) (gaussianReal 0 σ2) := by
    have := hasLaw_map (P := gaussianReal 0 σ2) (X := fun x : ℝ => x / (v : ℝ)) (by fun_prop)
    rwa [gaussianReal_map_div_const, zero_div,
      show σ2 / NNReal.mk ((v : ℝ) ^ 2) (sq_nonneg _) = σ2 / v ^ 2 by
        ext; simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_pow]] at this
  exact h.comp hZ

end GaussianLimit

/-! ### The weighted Fine–Gray score and information -/

section FineGrayScore

variable {ι : Type*} [DecidableEq ι] {n : ℕ}
  (X : Fin n → ℝ) (ε : Fin n → Option ι) (c : ι) (G : ℝ → ℝ) (z : Fin n → ℝ)

/-- The weighted sum `S_k(b, i) = ∑_l w_l(X_i) z_l^k exp (b z_l)` with the Fine–Gray weights
`w_l(X_i) = fgWeight X ε c G l i`. -/
noncomputable def fgWeightedSum (k : ℕ) (b : ℝ) (i : Fin n) : ℝ :=
  ∑ l, fgWeight X ε c G l i * (z l ^ k * exp (b * z l))

/-- The weighted covariate mean `z̄(b, i) = S_1(b, i) / S_0(b, i)`. -/
noncomputable def fgMean (b : ℝ) (i : Fin n) : ℝ :=
  fgWeightedSum X ε c G z 1 b i / fgWeightedSum X ε c G z 0 b i

/-- The weighted covariate variance `V(b, i) = S_2(b, i) / S_0(b, i) - z̄(b, i)²`. -/
noncomputable def fgVar (b : ℝ) (i : Fin n) : ℝ :=
  fgWeightedSum X ε c G z 2 b i / fgWeightedSum X ε c G z 0 b i - fgMean X ε c G z b i ^ 2

/-- The **Fine–Gray score** for a scalar covariate, `U(b) = ∑_{i : εᵢ = c} (zᵢ - z̄(b, i))`. -/
noncomputable def fgScore (b : ℝ) : ℝ :=
  ∑ i with ε i = some c, (z i - fgMean X ε c G z b i)

/-- The **Fine–Gray observed information** for a scalar covariate,
`I(b) = ∑_{i : εᵢ = c} V(b, i)`. -/
noncomputable def fgInformation (b : ℝ) : ℝ :=
  ∑ i with ε i = some c, fgVar X ε c G z b i

/-- The weighted Fine–Gray log partial likelihood of a scalar covariate,
`ℓ(b) = ∑_{i : εᵢ = c} (b zᵢ - log S_0(b, i))`. -/
noncomputable def fgLogPartialLikelihood₁ (b : ℝ) : ℝ :=
  ∑ i with ε i = some c, (b * z i - log (fgWeightedSum X ε c G z 0 b i))

/-- A subject has weight `1` at its own observed time. -/
theorem fgWeight_self (i : Fin n) : fgWeight X ε c G i i = 1 := by
  simp [fgWeight]

/-- The Fine–Gray weights are nonnegative when `G` is. -/
theorem fgWeight_nonneg {G : ℝ → ℝ} (hG : ∀ t, 0 ≤ G t) (l i : Fin n) :
    0 ≤ fgWeight X ε c G l i := by
  unfold fgWeight
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (hG _) (hG _)
  · exact le_rfl

variable {G}

/-- `S_0(b, i) ≥ exp (b zᵢ) > 0` for a nonnegative `G`. -/
theorem fgWeightedSum_zero_pos (hG : ∀ t, 0 ≤ G t) (b : ℝ) (i : Fin n) :
    0 < fgWeightedSum X ε c G z 0 b i := by
  refine lt_of_lt_of_le (exp_pos (b * z i)) ?_
  have h := single_le_sum (f := fun l => fgWeight X ε c G l i * (z l ^ 0 * exp (b * z l)))
    (fun l _ => mul_nonneg (fgWeight_nonneg X ε c hG l i) (by positivity)) (mem_univ i)
  simpa [fgWeightedSum, fgWeight_self] using h

/-- `d/db S_k(b, i) = S_{k+1}(b, i)`. -/
theorem hasDerivAt_fgWeightedSum (k : ℕ) (b : ℝ) (i : Fin n) :
    HasDerivAt (fun b => fgWeightedSum X ε c G z k b i) (fgWeightedSum X ε c G z (k + 1) b i)
      b := by
  unfold fgWeightedSum
  refine HasDerivAt.fun_sum fun l _ => ?_
  convert (((hasDerivAt_mul_const (z l)).exp).const_mul (z l ^ k)).const_mul
    (fgWeight X ε c G l i) using 1
  ring

/-- The weighted variance is nonnegative. -/
theorem fgVar_nonneg (hG : ∀ t, 0 ≤ G t) (b : ℝ) (i : Fin n) : 0 ≤ fgVar X ε c G z b i := by
  have hW := fgWeightedSum_zero_pos X ε c z hG b i
  set m := fgMean X ε c G z b i with hm
  have key : fgVar X ε c G z b i =
      (∑ l, fgWeight X ε c G l i * exp (b * z l) * (z l - m) ^ 2) /
        fgWeightedSum X ε c G z 0 b i := by
    have hexp : ∑ l, fgWeight X ε c G l i * exp (b * z l) * (z l - m) ^ 2 =
        fgWeightedSum X ε c G z 2 b i - 2 * m * fgWeightedSum X ε c G z 1 b i +
          m ^ 2 * fgWeightedSum X ε c G z 0 b i := by
      simp only [fgWeightedSum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun l _ => by ring
    rw [hexp, fgVar, hm, fgMean]
    field_simp
    ring
  rw [key]
  exact div_nonneg (sum_nonneg fun l _ => mul_nonneg
    (mul_nonneg (fgWeight_nonneg X ε c hG l i) (exp_pos _).le) (sq_nonneg _)) hW.le

/-- The Fine–Gray information is nonnegative. -/
theorem fgInformation_nonneg (hG : ∀ t, 0 ≤ G t) (b : ℝ) : 0 ≤ fgInformation X ε c G z b :=
  sum_nonneg fun i _ => fgVar_nonneg X ε c z hG b i

/-- The derivative of the weighted log partial likelihood is the Fine–Gray score. -/
theorem hasDerivAt_fgLogPartialLikelihood₁ (hG : ∀ t, 0 ≤ G t) (b : ℝ) :
    HasDerivAt (fgLogPartialLikelihood₁ X ε c G z) (fgScore X ε c G z b) b := by
  unfold fgLogPartialLikelihood₁ fgScore
  refine HasDerivAt.fun_sum fun i _ => ?_
  convert (hasDerivAt_mul_const (z i)).fun_sub ((hasDerivAt_fgWeightedSum X ε c z 0 b i).log
    (fgWeightedSum_zero_pos X ε c z hG b i).ne') using 1
  simp [fgMean]

/-- The derivative of the Fine–Gray score is minus the Fine–Gray information. -/
theorem hasDerivAt_fgScore (hG : ∀ t, 0 ≤ G t) (b : ℝ) :
    HasDerivAt (fgScore X ε c G z) (-fgInformation X ε c G z b) b := by
  unfold fgScore fgInformation
  rw [← sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hpos := fgWeightedSum_zero_pos X ε c z hG b i
  convert (hasDerivAt_const b (z i)).fun_sub ((hasDerivAt_fgWeightedSum X ε c z 1 b i).fun_div
    (hasDerivAt_fgWeightedSum X ε c z 0 b i) hpos.ne') using 1
  · rfl
  · unfold fgVar fgMean
    field_simp
    ring

/-- **The weighted Fine–Gray criterion is concave with score `fgScore` and information
`fgInformation`** for a nonnegative censoring survival `G`. -/
theorem isConcaveScore_fg (hG : ∀ t, 0 ≤ G t) :
    IsConcaveScore (fgLogPartialLikelihood₁ X ε c G z) (fgScore X ε c G z)
      (fgInformation X ε c G z) :=
  ⟨hasDerivAt_fgLogPartialLikelihood₁ X ε c z hG, hasDerivAt_fgScore X ε c z hG,
    fgInformation_nonneg X ε c z hG⟩

/-- `fgLogPartialLikelihood₁` is the logarithm of T146's weighted partial likelihood
`fgWeightedPartialLikelihood` with the scalar covariate `z` and coefficient `b`. -/
theorem log_fgWeightedPartialLikelihood (hG : ∀ t, 0 ≤ G t) (b : ℝ) :
    log (fgWeightedPartialLikelihood X ε c G (fun l _ => z l) (fun _ : Fin 1 => b)) =
      fgLogPartialLikelihood₁ X ε c G z b := by
  have hS : ∀ i, ∑ l, fgWeight X ε c G l i *
      exp ((fun _ : Fin 1 => b) ⬝ᵥ (fun _ : Fin 1 => z l)) = fgWeightedSum X ε c G z 0 b i :=
    fun i => by simp [fgWeightedSum, dotProduct]
  rw [fgWeightedPartialLikelihood, log_prod fun i _ => ?_, fgLogPartialLikelihood₁]
  · refine sum_congr rfl fun i _ => ?_
    rw [hS, log_div (exp_pos _).ne' (fgWeightedSum_zero_pos X ε c z hG b i).ne', log_exp]
    simp [dotProduct]
  · rw [hS]
    exact div_ne_zero (exp_pos _).ne' (fgWeightedSum_zero_pos X ε c z hG b i).ne'

/-! #### No competing events: the Cox case -/

private lemma filter_causeIndicator' :
    univ.filter (fun i : Fin n => causeIndicator ε c i = true) =
      univ.filter (fun i => ε i = some c) := by
  ext i
  simp [causeIndicator]

/-- Without competing events the weighted sums are Cox's risk-set sums, for every `G`. -/
theorem fgWeightedSum_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c) (k : ℕ) (b : ℝ)
    (i : Fin n) :
    fgWeightedSum X ε c G z k b i = ∑ l ∈ riskSet X i, z l ^ k * exp (b * z l) := by
  rw [fgWeightedSum, riskSet, sum_filter]
  refine sum_congr rfl fun l _ => ?_
  have hc : ¬ (ε l ≠ none ∧ ε l ≠ some c) := fun h => (hε l).elim h.1 h.2
  unfold fgWeight
  split_ifs <;> simp

/-- **No competing events**: the Fine–Gray score is the Cox score with the cause-`c` failures as
events, for every censoring survival `G`. -/
theorem fgScore_eq_coxScore_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c) (b : ℝ) :
    fgScore X ε c G z b = coxScore X (causeIndicator ε c) z b := by
  rw [fgScore, coxScore, filter_causeIndicator']
  refine sum_congr rfl fun i _ => ?_
  simp [fgMean, riskMean, fgWeightedSum_of_noCompeting X ε c z hε]

/-- **No competing events**: the Fine–Gray information is the Cox information. -/
theorem fgInformation_eq_coxInformation_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c)
    (b : ℝ) : fgInformation X ε c G z b = coxInformation X (causeIndicator ε c) z b := by
  rw [fgInformation, coxInformation, filter_causeIndicator']
  refine sum_congr rfl fun i _ => ?_
  simp [fgVar, fgMean, riskVar, riskMean, fgWeightedSum_of_noCompeting X ε c z hε]

/-- **No competing events**: the weighted Fine–Gray criterion is Cox's log partial likelihood, so
the Fine–Gray estimator is the Cox estimator. -/
theorem fgLogPartialLikelihood₁_eq_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c) :
    fgLogPartialLikelihood₁ X ε c G z = logPartialLikelihood₁ X (causeIndicator ε c) z := by
  funext b
  rw [fgLogPartialLikelihood₁, logPartialLikelihood₁, logPartialLikelihood,
    filter_causeIndicator']
  refine sum_congr rfl fun i _ => ?_
  simp [fgWeightedSum_of_noCompeting X ε c z hε, dotProduct]

end FineGrayScore

/-! ### Consistency and asymptotic normality of the Fine–Gray estimator -/

section FineGrayAsymptotics

variable {Ω Ω' ι : Type*} [DecidableEq ι] {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **The Fine–Gray regularity conditions** (scalar covariate) for the data
`(X n ω, ε n ω, z n ω)`, cause of interest `c`, weight functions `G n ω` (e.g. the Kaplan–Meier
estimate of the censoring survival), true coefficient `β₀`, score limit `Z` and information
limit `i` with `i(β₀) = v`. See the module docstring. -/
structure FineGrayConditions (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (X : (n : ℕ) → Ω → Fin n → ℝ)
    (ε : (n : ℕ) → Ω → Fin n → Option ι) (c : ι) (G : ℕ → Ω → ℝ → ℝ)
    (z : (n : ℕ) → Ω → Fin n → ℝ) (β₀ r : ℝ) (i : ℝ → ℝ) (v : NNReal) (Z : Ω' → ℝ) : Prop where
  /-- The censoring-survival weights are nonnegative. -/
  weight_nonneg : ∀ n ω t, 0 ≤ G n ω t
  /-- The normalized score at the true coefficient converges in distribution. -/
  score : TendstoInDistribution
    (fun (n : ℕ) ω ↦ fgScore (X n ω) (ε n ω) c (G n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z
    (fun _ ↦ P) P'
  /-- The neighbourhood radius is positive. -/
  radius_pos : 0 < r
  /-- The normalized information converges uniformly in probability on `[β₀ - r, β₀ + r]`. -/
  info_unif : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
    η ≤ |fgInformation (X n ω) (ε n ω) c (G n ω) (z n ω) b / n - i b|}) atTop (𝓝 0)
  /-- The information limit is continuous at `β₀`. -/
  info_continuousAt : ContinuousAt i β₀
  /-- The information limit at `β₀` is `v`. -/
  info_eq : i β₀ = v
  /-- The information limit at `β₀` is nonzero. -/
  info_ne_zero : v ≠ 0

variable {X : (n : ℕ) → Ω → Fin n → ℝ} {ε : (n : ℕ) → Ω → Fin n → Option ι} {c : ι}
  {G : ℕ → Ω → ℝ → ℝ} {z : (n : ℕ) → Ω → Fin n → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {v : NNReal}
  {Z : Ω' → ℝ} {βhat : ℕ → Ω → ℝ}

/-- **Existence of the Fine–Gray estimator with probability tending to one.** -/
theorem tendsto_measure_not_exists_isMaxOn_fg
    (h : FineGrayConditions P P' X ε c G z β₀ r i v Z) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b,
      IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b}) atTop
      (𝓝 0) :=
  tendsto_measure_not_exists_isMaxOn
    (fun n ω => isConcaveScore_fg (X n ω) (ε n ω) c (z n ω) (h.weight_nonneg n ω))
    h.info_ne_zero h.score h.info_continuousAt h.info_eq h.info_unif h.radius_pos

/-- **Consistency of the Fine–Gray estimator** (Fine and Gray 1999, Section 3, scalar
covariate). Let `βhat n` maximize the weighted Fine–Gray log partial likelihood whenever a
maximizer exists. Under `FineGrayConditions`, `βhat n → β₀` in probability. Only
`Uₙ(β₀) / n → 0` in probability is used from the score hypothesis. -/
theorem tendstoInMeasure_fgMPLE (h : FineGrayConditions P P' X ε c G z β₀ r i v Z)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω)) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) :=
  tendstoInMeasure_argmax
    (fun n ω => isConcaveScore_fg (X n ω) (ε n ω) c (z n ω) (h.weight_nonneg n ω))
    h.info_ne_zero hβhat h.score h.info_continuousAt h.info_eq h.info_unif h.radius_pos

/-- **The Fine–Gray estimator is asymptotically `Z / v`**: under `FineGrayConditions` and
measurability of the estimator, `√n (βhat n - β₀) ⟶ Z / v` in distribution. -/
theorem tendstoInDistribution_fgMPLE (h : FineGrayConditions P P' X ε c G z β₀ r i v Z)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' :=
  tendstoInDistribution_argmax
    (fun n ω => isConcaveScore_fg (X n ω) (ε n ω) c (z n ω) (h.weight_nonneg n ω))
    h.info_ne_zero hβhat hβhat_meas h.score h.info_continuousAt h.info_eq h.info_unif
    h.radius_pos

/-- **Asymptotic normality of the Fine–Gray estimator** (Fine and Gray 1999, Section 3, scalar
covariate). Under `FineGrayConditions` with a Gaussian score limit `Z ~ N(0, σ²)` and a
measurable estimator, `√n (βhat n - β₀) ⟶ Z / v` and `Z / v ~ N(0, σ² / v²)`: the sandwich
variance `Ω⁻¹ Σ Ω⁻¹` with `Σ = σ²` and `Ω = v`. -/
theorem tendstoInDistribution_fgMPLE_gaussian {σ2 : NNReal}
    (h : FineGrayConditions P P' X ε c G z β₀ r i v Z) (hZ : HasLaw Z (gaussianReal 0 σ2) P')
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 (σ2 / v ^ 2)) P' :=
  ⟨tendstoInDistribution_fgMPLE h hβhat hβhat_meas,
    hasLaw_div_gaussianReal_sq hZ⟩

/-- **Consistency of the normalized Fine–Gray information at the estimator**:
`Iₙ(βhat n) / n → v` in probability (the bread `Ω` of the sandwich variance). -/
theorem tendstoInMeasure_fgInformation_fgMPLE (h : FineGrayConditions P P' X ε c G z β₀ r i v Z)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω)) :
    TendstoInMeasure P
      (fun n ω => fgInformation (X n ω) (ε n ω) c (G n ω) (z n ω) (βhat n ω) / n) atTop
      (fun _ => (v : ℝ)) :=
  tendstoInMeasure_info_argmax
    (fun n ω => isConcaveScore_fg (X n ω) (ε n ω) c (z n ω) (h.weight_nonneg n ω))
    h.info_ne_zero hβhat h.score h.info_continuousAt h.info_eq h.info_unif h.radius_pos

end FineGrayAsymptotics

/-! ### Old names

The concave-criterion API moved to `ConcaveScore` and `isConcaveScore_cox` to `CoxAsymptotics`.
These re-exports keep the old names in this namespace resolving to the moved declarations, as
`CoxAsymptotics` does for `tendstoInMeasure_div_sqrt`. They are exports rather than deprecated
aliases because an alias of the structure would break field notation on hypotheses stated with
the old name. -/

export MathlibExt.Probability.Statistics.ConcaveScore (IsConcaveScore
  tendsto_measure_not_score_eq_zero_and_abs_sub_lt tendsto_measure_not_exists_isMaxOn
  tendstoInMeasure_argmax tendstoInDistribution_argmax tendstoInMeasure_info_argmax)
export MathlibExt.Probability.Statistics.CoxAsymptotics (isConcaveScore_cox)

namespace IsConcaveScore

export MathlibExt.Probability.Statistics.ConcaveScore.IsConcaveScore (mk hasDerivAt_crit
  hasDerivAt_score info_nonneg continuous_score antitone_score exists_score_sub_eq
  score_eq_zero_of_isMaxOn isMaxOn_of_score_eq_zero score_eq_zero_and_abs_sub_lt
  score_eq_zero_and_abs_sub_lt_of_div abs_sqrt_mul_sub_sub_le)

end IsConcaveScore

end MathlibExt.Probability.Statistics.FineGrayAsymptotics
