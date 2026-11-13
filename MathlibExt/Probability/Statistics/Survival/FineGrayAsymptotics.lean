/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGray
public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics
import MathlibExt.Probability.BoundedInProbability
import MathlibExt.Probability.Statistics.Slutsky
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

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

The asymptotics are proved once for an abstract concave criterion (`IsConcaveScore`: `ℓ' = U`,
`U' = -I`, `I ≥ 0`) in the `ConcaveScore` section and then instantiated. The argument is the
Andersen–Gill one of `CoxAsymptotics` (which treats the Cox score directly), with the score
variance decoupled from the information limit; `isConcaveScore_cox` shows the scalar Cox score is
also an instance.

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
  `CoxPartialLikelihood`; `tendstoInMeasure_div_sqrt` from `CoxAsymptotics`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGrayAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptotics

/-! ### Abstract concave criteria -/

/-- `ℓ` is a concave criterion with score `U` and observed information `I`: `ℓ' = U`, `U' = -I`
and `I ≥ 0`. -/
structure IsConcaveScore (ℓ U I : ℝ → ℝ) : Prop where
  hasDerivAt_crit : ∀ b, HasDerivAt ℓ (U b) b
  hasDerivAt_score : ∀ b, HasDerivAt U (-I b) b
  info_nonneg : ∀ b, 0 ≤ I b

namespace IsConcaveScore

variable {ℓ U I : ℝ → ℝ} (h : IsConcaveScore ℓ U I)
include h

/-- The score is continuous. -/
theorem continuous_score : Continuous U :=
  continuous_iff_continuousAt.2 fun b => (h.hasDerivAt_score b).continuousAt

/-- The score is antitone. -/
theorem antitone_score : Antitone U :=
  antitone_of_deriv_nonpos (fun b => (h.hasDerivAt_score b).differentiableAt) fun b => by
    rw [(h.hasDerivAt_score b).deriv]
    exact neg_nonpos.2 (h.info_nonneg b)

/-- Mean value form of the score increment: `U(b) - U(a) = -I(c) (b - a)` for some `c` between
`a` and `b`. -/
theorem exists_score_sub_eq (a b : ℝ) :
    ∃ c ∈ Set.uIcc a b, U b - U a = -I c * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope U (fun c => -I c) hab
      h.continuous_score.continuousOn fun c _ => h.hasDerivAt_score c
    refine ⟨c, Set.uIcc_of_le hab.le ▸ Set.Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']; field_simp [(sub_pos.2 hab).ne']
  · exact ⟨a, Set.left_mem_uIcc, by ring⟩
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope U (fun c => -I c) hab
      h.continuous_score.continuousOn fun c _ => h.hasDerivAt_score c
    refine ⟨c, Set.uIcc_of_ge hab.le ▸ Set.Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']; field_simp [(sub_pos.2 hab).ne']; ring

/-- A maximizer of the criterion is a root of the score. -/
theorem score_eq_zero_of_isMaxOn {b : ℝ} (hb : IsMaxOn ℓ Set.univ b) : U b = 0 :=
  (hb.isLocalMax Filter.univ_mem).hasDerivAt_eq_zero (h.hasDerivAt_crit b)

/-- A root of the score maximizes the criterion (concavity). -/
theorem isMaxOn_of_score_eq_zero {b : ℝ} (hb : U b = 0) : IsMaxOn ℓ Set.univ b := by
  have hcont : Continuous ℓ :=
    continuous_iff_continuousAt.2 fun c => (h.hasDerivAt_crit c).continuousAt
  intro c _
  rcases le_total c b with hcb | hbc
  · have hmono : MonotoneOn ℓ (Set.Iic b) :=
      monotoneOn_of_deriv_nonneg (convex_Iic b) hcont.continuousOn
        (fun x _ => (h.hasDerivAt_crit x).differentiableAt.differentiableWithinAt) fun x hx => by
          rw [interior_Iic] at hx
          rw [(h.hasDerivAt_crit x).deriv, ← hb]
          exact h.antitone_score (le_of_lt hx)
    exact hmono hcb le_rfl hcb
  · have hanti : AntitoneOn ℓ (Set.Ici b) :=
      antitoneOn_of_deriv_nonpos (convex_Ici b) hcont.continuousOn
        (fun x _ => (h.hasDerivAt_crit x).differentiableAt.differentiableWithinAt) fun x hx => by
          rw [interior_Ici] at hx
          rw [(h.hasDerivAt_crit x).deriv, ← hb]
          exact h.antitone_score (le_of_lt hx)
    exact hanti le_rfl hbc hbc

/-- **Deterministic core of consistency.** If the information exceeds `m` on
`[β₀ - ε, β₀ + ε]` and `|U(β₀)| < ε m`, then the criterion has a maximizer, and any `bh` that is
a maximizer whenever one exists is a root of the score within `ε` of `β₀`. -/
theorem score_eq_zero_and_abs_sub_lt {β₀ ε m bh : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < I b) (hU : |U β₀| < ε * m)
    (hbh : (∃ b, IsMaxOn ℓ Set.univ b) → IsMaxOn ℓ Set.univ bh) :
    U bh = 0 ∧ |bh - β₀| < ε := by
  obtain ⟨c, hc, hc'⟩ := h.exists_score_sub_eq β₀ (β₀ + ε)
  obtain ⟨d, hd, hd'⟩ := h.exists_score_sub_eq β₀ (β₀ - ε)
  rw [Set.uIcc_of_le (by linarith)] at hc
  rw [Set.uIcc_of_ge (by linarith)] at hd
  have h1 := hI c ⟨by linarith [hc.1], hc.2⟩
  have h2 := hI d ⟨hd.1, by linarith [hd.2]⟩
  rw [abs_lt] at hU
  have hplus : U (β₀ + ε) < 0 := by nlinarith
  have hminus : 0 < U (β₀ - ε) := by nlinarith
  obtain ⟨b, -, hb⟩ := intermediate_value_Icc' (show β₀ - ε ≤ β₀ + ε by linarith)
    h.continuous_score.continuousOn ⟨hplus.le, hminus.le⟩
  have hroot := h.score_eq_zero_of_isMaxOn (hbh ⟨b, h.isMaxOn_of_score_eq_zero hb⟩)
  refine ⟨hroot, abs_sub_lt_iff.2 ⟨?_, ?_⟩⟩
  · by_contra hc
    have := h.antitone_score (show β₀ + ε ≤ bh by linarith)
    linarith
  · by_contra hc
    have := h.antitone_score (show bh ≤ β₀ - ε by linarith)
    linarith

/-- Normalized form of `score_eq_zero_and_abs_sub_lt`: if `|I(b) / n - i(b)| < v / 4` and
`|i(b) - v| < v / 4` on `[β₀ - ε, β₀ + ε]` and `|U(β₀) / n| < ε v / 4`, then `bh` is a root of the
score within `ε` of `β₀`. -/
theorem score_eq_zero_and_abs_sub_lt_of_div {n : ℕ} {i : ℝ → ℝ} {β₀ v ε bh : ℝ} (hn : 0 < n)
    (hv : 0 < v) (hε : 0 < ε) (hiv : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |i b - v| < v / 4)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |I b / n - i b| < v / 4)
    (hU : |U β₀ / n| < ε * v / 4)
    (hbh : (∃ b, IsMaxOn ℓ Set.univ b) → IsMaxOn ℓ Set.univ bh) :
    U bh = 0 ∧ |bh - β₀| < ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine h.score_eq_zero_and_abs_sub_lt (m := n * v / 2) hε (fun b hb => ?_) ?_ hbh
  · have h1 := abs_lt.1 (hI b hb)
    have h2 := abs_lt.1 (hiv b hb)
    have h3 : v / 2 < I b / n := by linarith
    rw [lt_div_iff₀ hn'] at h3
    linarith
  · rw [abs_div, abs_of_pos hn', div_lt_iff₀ hn'] at hU
    nlinarith [mul_pos (mul_pos hε hn') hv]

/-- **Deterministic core of asymptotic normality.** If `bh` is a root of the score within `ε` of
`β₀` and `I(b) / n` is within `η ≤ v / 2` of `v` on `[β₀ - ε, β₀ + ε]`, then `√n (bh - β₀)`
differs from `(U(β₀) / √n) / v` by at most `|U(β₀) / √n| · 2 η / v²`. -/
theorem abs_sqrt_mul_sub_sub_le {n : ℕ} {β₀ ε v η bh : ℝ} (hn : 0 < n) (hv : 0 < v)
    (hη : η ≤ v / 2) (hroot : U bh = 0) (hb : |bh - β₀| ≤ ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |I b / n - v| < η) :
    |√(n : ℝ) * (bh - β₀) - U β₀ / √(n : ℝ) / v| ≤ |U β₀ / √(n : ℝ)| * (2 * η / v ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
  obtain ⟨c, hc, hc'⟩ := h.exists_score_sub_eq β₀ bh
  have hcI : c ∈ Set.Icc (β₀ - ε) (β₀ + ε) := by
    rw [abs_le] at hb
    exact Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hc
  have hJ := abs_lt.1 (hI c hcI)
  set J := I c / n with hJdef
  have hJpos : v / 2 < J := by linarith
  have hJ0 : 0 < J := by linarith
  have hIc : I c = n * J := by rw [hJdef]; field_simp
  set S := U β₀ / √(n : ℝ) with hSdef
  have hU : U β₀ = √(n : ℝ) * S := by rw [hSdef]; field_simp
  have hY : √(n : ℝ) * (bh - β₀) = S / J := by
    rw [hroot, hU, hIc] at hc'
    have h1 : √(n : ℝ) * S = √(n : ℝ) * (√(n : ℝ) * J * (bh - β₀)) := by
      linear_combination -hc' - J * (bh - β₀) * hss
    rw [mul_left_cancel₀ hsq.ne' h1]
    field_simp
  rw [hY, show S / J - S / v = S * ((v - J) / (J * v)) by field_simp, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg S)
  rw [abs_div, abs_of_pos (mul_pos hJ0 hv), div_le_div_iff₀ (mul_pos hJ0 hv) (by positivity)]
  have hvJ : |v - J| ≤ η := by rw [abs_sub_comm]; exact (abs_lt.2 hJ).le
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) hvJ
  nlinarith [mul_le_mul_of_nonneg_left hJpos.le hη0]

end IsConcaveScore

/-- The scalar Cox log partial likelihood is a concave criterion with the Cox score and
information, so the results below also cover `CoxAsymptotics`' setting. -/
theorem isConcaveScore_cox {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) :
    IsConcaveScore (logPartialLikelihood₁ T δ z) (coxScore T δ z) (coxInformation T δ z) :=
  ⟨hasDerivAt_logPartialLikelihood T δ z, hasDerivAt_coxScore T δ z, coxInformation_nonneg T δ z⟩

/-! ### Asymptotics of the maximizer of a random concave criterion -/

section ConcaveScore

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℓ U I : ℕ → Ω → ℝ → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

omit [IsProbabilityMeasure P'] in
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

/-- **With probability tending to one the maximizer is a root of the score near `β₀`**, for a
random concave criterion with score limit at `β₀` and normalized information converging
uniformly in probability near `β₀` to a function `i` continuous at `β₀` with `i β₀ = v > 0`. -/
theorem tendsto_measure_not_score_eq_zero_and_abs_sub_lt
    (hC : ∀ n ω, IsConcaveScore (ℓ n ω) (U n ω) (I n ω)) (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (ℓ n ω) Set.univ b) → IsMaxOn (ℓ n ω) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution (fun (n : ℕ) ω ↦ U n ω β₀ / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |I n ω b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ (U n ω (βhat n ω) = 0 ∧ |βhat n ω - β₀| < ε)}) atTop
      (𝓝 0) := by
  have hv' : (0 : ℝ) < v := by positivity
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.continuousAt_iff.1 hi (v / 4) (by positivity)
  set ε' := min ε (min (r₀ / 2) r) with hε'
  have hε'0 : 0 < ε' := lt_min hε (lt_min (by positivity) hr)
  have hA := (tendstoInMeasure_iff_norm.1 (tendstoInMeasure_div_sqrt hscore))
    (ε' * v / 4) (by positivity)
  have hB := hinfo (v / 4) (by positivity)
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAB
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  rw [Set.mem_union]
  by_contra hbad
  rw [not_or] at hbad
  obtain ⟨hU, hI⟩ := hbad
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hU' : |U n ω β₀ / n| < ε' * v / 4 := by
    have h : ¬ (ε' * v / 4 ≤ ‖U n ω β₀ / √(n : ℝ) / √(n : ℝ) - (0 : Ω → ℝ) ω‖) := hU
    rwa [not_le, Pi.zero_apply, sub_zero, Real.norm_eq_abs, div_div,
      Real.mul_self_sqrt hn'.le] at h
  have hI' : ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r), |I n ω b / n - i b| < v / 4 :=
    fun b hb => lt_of_not_ge fun h => hI ⟨b, hb, h⟩
  have h1 : ε' ≤ r₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : ε' ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  have hgood := (hC n ω).score_eq_zero_and_abs_sub_lt_of_div (i := i) (ε := ε') hn hv' hε'0
    (fun b hb => by
      have h := hr₀' (x := b) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb.1, hb.2])
      rwa [hiv, Real.dist_eq] at h)
    (fun b hb => hI' b ⟨by linarith [hb.1], by linarith [hb.2]⟩) hU' (hβhat n ω)
  exact hω ⟨hgood.1, lt_of_lt_of_le hgood.2 (min_le_left _ _)⟩

/-- **Existence of a maximizer with probability tending to one.** -/
theorem tendsto_measure_not_exists_isMaxOn
    (hC : ∀ n ω, IsConcaveScore (ℓ n ω) (U n ω) (I n ω)) (hv : v ≠ 0)
    (hscore : TendstoInDistribution (fun (n : ℕ) ω ↦ U n ω β₀ / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |I n ω b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b, IsMaxOn (ℓ n ω) Set.univ b}) atTop (𝓝 0) := by
  classical
  let βsel : ℕ → Ω → ℝ := fun n ω =>
    if h : ∃ b, IsMaxOn (ℓ n ω) Set.univ b then h.choose else 0
  have hsel : ∀ n ω, (∃ b, IsMaxOn (ℓ n ω) Set.univ b) → IsMaxOn (ℓ n ω) Set.univ (βsel n ω) :=
    fun n ω h => by simp only [βsel, h, ↓reduceDIte]; exact h.choose_spec
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_not_score_eq_zero_and_abs_sub_lt (βhat := βsel) hC hv hsel hscore hi hiv
      hinfo hr one_pos) (fun _ => zero_le) fun n => measure_mono fun ω hω hgood => hω
      ⟨βsel n ω, (hC n ω).isMaxOn_of_score_eq_zero hgood.1⟩

/-- **Consistency of the maximizer of a random concave criterion.** -/
theorem tendstoInMeasure_argmax
    (hC : ∀ n ω, IsConcaveScore (ℓ n ω) (U n ω) (I n ω)) (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (ℓ n ω) Set.univ b) → IsMaxOn (ℓ n ω) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution (fun (n : ℕ) ω ↦ U n ω β₀ / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |I n ω b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_not_score_eq_zero_and_abs_sub_lt hC hv hβhat hscore hi hiv hinfo hr hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω hgood => ?_
  have h : ε ≤ dist (βhat n ω) β₀ := hω
  rw [Real.dist_eq] at h
  exact absurd hgood.2 (not_lt.2 h)

/-- **The maximizer is asymptotically `Z / v`**: `√n (βhat n - β₀) ⟶ Z / v`, where `Z` is the
limit of `Uₙ(β₀) / √n` and `v = i(β₀)`. -/
theorem tendstoInDistribution_argmax
    (hC : ∀ n ω, IsConcaveScore (ℓ n ω) (U n ω) (I n ω)) (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (ℓ n ω) Set.univ b) → IsMaxOn (ℓ n ω) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution (fun (n : ℕ) ω ↦ U n ω β₀ / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |I n ω b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' := by
  have hv' : (0 : ℝ) < v := by positivity
  set S : ℕ → Ω → ℝ := fun n ω => U n ω β₀ / √(n : ℝ) with hSdef
  have hX := hscore.continuous_comp (g := fun x : ℝ => x / (v : ℝ)) (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_
    (fun n => ((hβhat_meas n).sub_const β₀).const_mul _)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨K, hK⟩ :=
    exists_forall_measure_lt_norm_le_of_tendstoInDistribution hscore (ENNReal.half_pos hκ.ne')
  obtain ⟨M, hM, hMn⟩ : ∃ M : ℝ, 0 < M ∧ ∀ n, P {ω | M ≤ |S n ω|} ≤ κ / 2 := by
    refine ⟨max K 0 + 1, by linarith [le_max_right K 0], fun n => le_trans ?_ (hK n)⟩
    refine measure_mono fun ω (hω : max K 0 + 1 ≤ |S n ω|) => ?_
    change K < |S n ω|
    linarith [le_max_left K 0]
  set η := min ((v : ℝ) / 4) (ε * (v : ℝ) ^ 2 / (4 * M)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨r₁', hr₁', hr₁''⟩ := Metric.continuousAt_iff.1 hi (η / 2) (by positivity)
  set r₁ := min (r₁' / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hr
  have hG := tendsto_measure_not_score_eq_zero_and_abs_sub_lt hC hv hβhat hscore hi hiv hinfo hr
    hr₁
  have hB := hinfo (η / 2) (by positivity)
  have hGB := hG.add hB
  rw [add_zero] at hGB
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hGB) (κ / 2) (ENNReal.half_pos hκ.ne'),
    eventually_gt_atTop 0] with n hn' hn0
  let A : Set Ω := {ω | M ≤ |U n ω β₀ / √(n : ℝ)|}
  let B : Set Ω := {ω | ¬ (U n ω (βhat n ω) = 0 ∧ |βhat n ω - β₀| < r₁)}
  let C : Set Ω := {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r), η / 2 ≤ |I n ω b / n - i b|}
  have hA : P A ≤ κ / 2 := hMn n
  have hBC : P B + P C ≤ κ / 2 := hn'
  refine le_trans (measure_mono (t := A ∪ (B ∪ C)) ?_) (le_trans
    ((measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _))
    (le_trans (add_le_add hA hBC) (ENNReal.add_halves κ).le))
  intro ω hω
  rw [Set.mem_union, Set.mem_union]
  by_contra hbad
  simp only [not_or] at hbad
  obtain ⟨hS, hroot, hI⟩ := hbad
  have hS' : |S n ω| < M := lt_of_not_ge hS
  have hroot' : U n ω (βhat n ω) = 0 ∧ |βhat n ω - β₀| < r₁ := not_not.1 hroot
  have hI' : ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r), |I n ω b / n - i b| < η / 2 :=
    fun b hb => lt_of_not_ge fun h => hI ⟨b, hb, h⟩
  have h1 : r₁ ≤ r₁' / 2 := min_le_left _ _
  have h2 : r₁ ≤ r := min_le_right _ _
  have hbound := (hC n ω).abs_sqrt_mul_sub_sub_le (ε := r₁) (η := η) hn0 hv'
    (by linarith [min_le_left ((v : ℝ) / 4) (ε * (v : ℝ) ^ 2 / (4 * M))]) hroot'.1
    hroot'.2.le fun b hb => by
      have hib := hr₁'' (x := b) (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb.1, hb.2])
      rw [hiv, Real.dist_eq] at hib
      have hIb := hI' b ⟨by linarith [hb.1], by linarith [hb.2]⟩
      calc |I n ω b / n - v| ≤ |I n ω b / n - i b| + |i b - v| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := add_lt_add hIb hib
        _ = η := add_halves η
  have hηM : M * (2 * η / (v : ℝ) ^ 2) ≤ ε / 2 := by
    have : η ≤ ε * (v : ℝ) ^ 2 / (4 * M) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hlt : ‖(fun ω ↦ √(n : ℝ) * (βhat n ω - β₀)) ω - ((fun x ↦ x / (v : ℝ)) ∘ S n) ω‖ < ε := by
    rw [Real.norm_eq_abs, Function.comp_apply]
    calc _ ≤ |S n ω| * (2 * η / (v : ℝ) ^ 2) := hbound
      _ ≤ M * (2 * η / (v : ℝ) ^ 2) := by gcongr
      _ < ε := by linarith
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
  exact (not_le.2 hlt) hω

/-- **Consistency of the normalized information at the maximizer**: `Iₙ(βhat n) / n → v`. -/
theorem tendstoInMeasure_info_argmax
    (hC : ∀ n ω, IsConcaveScore (ℓ n ω) (U n ω) (I n ω)) (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (ℓ n ω) Set.univ b) → IsMaxOn (ℓ n ω) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution (fun (n : ℕ) ω ↦ U n ω β₀ / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |I n ω b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P (fun n ω => I n ω (βhat n ω) / n) atTop (fun _ => (v : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨r₁', hr₁', hr₁''⟩ := Metric.continuousAt_iff.1 hi (ε / 2) (by positivity)
  set r₁ := min (r₁' / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hr
  have hG := tendsto_measure_not_score_eq_zero_and_abs_sub_lt hC hv hβhat hscore hi hiv hinfo hr
    hr₁
  have hB := hinfo (ε / 2) (by positivity)
  have hGB := hG.add hB
  rw [add_zero] at hGB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGB (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  rw [Set.mem_union]
  by_contra hbad
  rw [not_or] at hbad
  obtain ⟨hroot, hI⟩ := hbad
  have hroot' : U n ω (βhat n ω) = 0 ∧ |βhat n ω - β₀| < r₁ := not_not.1 hroot
  have h1 : r₁ ≤ r₁' / 2 := min_le_left _ _
  have h2 : r₁ ≤ r := min_le_right _ _
  have hb := abs_lt.1 hroot'.2
  have hIb : |I n ω (βhat n ω) / n - i (βhat n ω)| < ε / 2 :=
    lt_of_not_ge fun h => hI ⟨βhat n ω, ⟨by linarith, by linarith⟩, h⟩
  have hib := hr₁'' (x := βhat n ω) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [hiv, Real.dist_eq] at hib
  have hω' : ε ≤ dist (I n ω (βhat n ω) / n) (v : ℝ) := hω
  rw [Real.dist_eq] at hω'
  have := abs_sub_le (I n ω (βhat n ω) / n) (i (βhat n ω)) v
  linarith

end ConcaveScore

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
  rw [fgScore, coxScore, filter_causeIndicator]
  refine sum_congr rfl fun i _ => ?_
  simp [fgMean, riskMean, fgWeightedSum_of_noCompeting X ε c z hε]

/-- **No competing events**: the Fine–Gray information is the Cox information. -/
theorem fgInformation_eq_coxInformation_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c)
    (b : ℝ) : fgInformation X ε c G z b = coxInformation X (causeIndicator ε c) z b := by
  rw [fgInformation, coxInformation, filter_causeIndicator]
  refine sum_congr rfl fun i _ => ?_
  simp [fgVar, fgMean, riskVar, riskMean, fgWeightedSum_of_noCompeting X ε c z hε]

/-- **No competing events**: the weighted Fine–Gray criterion is Cox's log partial likelihood, so
the Fine–Gray estimator is the Cox estimator. -/
theorem fgLogPartialLikelihood₁_eq_of_noCompeting (hε : ∀ l, ε l = none ∨ ε l = some c) :
    fgLogPartialLikelihood₁ X ε c G z = logPartialLikelihood₁ X (causeIndicator ε c) z := by
  funext b
  rw [fgLogPartialLikelihood₁, logPartialLikelihood₁, logPartialLikelihood,
    filter_causeIndicator]
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

end MathlibExt.Probability.Statistics.FineGrayAsymptotics
