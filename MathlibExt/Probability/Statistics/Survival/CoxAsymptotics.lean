/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ProcessInference
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.IntermediateValue

/-!
# Cox regression: consistency and asymptotic normality (Andersen–Gill)

For each sample size `n`, the data `(Tᵢ, δᵢ, zᵢ)_{i < n}` (observed times, event indicators and a
scalar covariate) are random, `ω ↦ (T n ω, δ n ω, z n ω)` on a probability space `(Ω, P)`. Write
`ℓₙ` for the log partial likelihood `logPartialLikelihood₁`, `Uₙ = coxScore` for its derivative
and `Iₙ = coxInformation` for the observed information `-ℓₙ''` (see `CoxPartialLikelihood`). The
Cox estimator `βhat n` is a maximizer of `ℓₙ` whenever one exists (it need not exist: with
monotone likelihood there is none).

Andersen and Gill (1982) derive the asymptotics of `βhat n` from two limit statements about the
counting-process data, which they obtain from their conditions A–D by Rebolledo's martingale
central limit theorem (under a Lindeberg condition) and Lenglart's inequality. **These two limit
statements are the hypotheses here**; their derivation from conditions A–D is not formalized:

* (score CLT) `Uₙ(β₀) / √n ⟶ Z` in distribution, with `Z ~ N(0, v)`;
* (uniform information) on a neighbourhood `[β₀ - r, β₀ + r]`,
  `sup_b |Iₙ(b) / n - i(b)| → 0` in probability, for a function `i` continuous at `β₀` with
  `i(β₀) = v > 0`. The supremum is stated without measurability assumptions, as
  `P {ω | ∃ b ∈ [β₀ - r, β₀ + r], η ≤ |Iₙ(b) / n - i(b)|} → 0` for every `η > 0`.

That the score variance and the information limit are the same `v` is the Andersen–Gill
information identity: `Uₙ(β₀)` is a martingale whose predictable variation is `Iₙ(β₀)`.

## Main results

* `tendsto_measure_not_exists_isMaxOn`: with probability tending to one, `ℓₙ` has a maximizer.
* `tendstoInMeasure_coxMPLE` (**consistency**, Andersen–Gill Theorem 3.2): `βhat n → β₀` in
  probability. Only `Uₙ(β₀) / n → 0` in probability is used from the score hypothesis.
* `tendstoInDistribution_coxMPLE_gaussian` (**asymptotic normality**, Andersen–Gill Theorem
  3.3): `√n (βhat n - β₀) ⟶ Z / v` and `Z / v ~ N(0, v⁻¹)`: the asymptotic variance is the
  inverse of the limiting information. `tendstoInDistribution_coxMPLE` is the limit statement
  for an arbitrary score limit `Z`.
* `tendstoInMeasure_coxInformation_coxMPLE`: `Iₙ(βhat n) / n → v` in probability.
* `tendsto_coverage_cox_waldInterval_coxMPLE`: the Wald interval `βhat n ± c / √(Iₙ(βhat n))`
  has asymptotic coverage equal to the standard-normal mass of `[-c, c]`; this discharges the
  limit hypotheses of `ProcessInference.tendsto_coverage_cox_waldInterval`.

The deterministic core: `riskVar_nonneg` and `antitone_coxScore` (concavity),
`isMaxOn_of_coxScore_eq_zero` and `coxScore_eq_zero_of_isMaxOn` (maximizers are the roots of the
score), `coxScore_eq_zero_and_abs_sub_lt` (a lower bound on the information near `β₀` and a small
score at `β₀` locate every maximizer near `β₀`), and `abs_sqrt_mul_sub_sub_le` (the one-step
mean-value expansion `√n (βhat - β₀) ≈ (Uₙ(β₀) / √n) / v`). The probabilistic helpers are
`exists_eventually_measure_le_abs_lt` (convergence in distribution implies tightness) and
`tendstoInMeasure_div_sqrt`.

## Scope

Only a **scalar covariate** (`p = 1`) is treated. The vector case of Andersen–Gill (`β ∈ ℝᵖ`,
limit `N(0, Σ⁻¹)` with the information matrix `Σ`) needs the Jacobian of the score vector
`coxGradient` and a matrix-valued mean value argument, and is not covered. The derivation of the
two limit hypotheses from the counting-process conditions (Rebolledo's martingale CLT, Lenglart's
inequality, the uniform law for `S⁽ᵏ⁾ / n`) is not formalized.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3.
* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

/-! ### Deterministic facts about the scalar Cox score -/

section Deterministic

variable {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ)

/-- The weighted risk-set variance is nonnegative. -/
theorem riskVar_nonneg (b : ℝ) (i : Fin n) : 0 ≤ riskVar T z b i := by
  have hW : 0 < ∑ l ∈ riskSet T i, exp (b * z l) :=
    sum_pos (fun _ _ => exp_pos _) (riskSet_nonempty T i)
  have hexp : ∑ l ∈ riskSet T i, exp (b * z l) * (z l - riskMean T z b i) ^ 2 =
      ∑ l ∈ riskSet T i, z l ^ 2 * exp (b * z l) -
        2 * riskMean T z b i * ∑ l ∈ riskSet T i, z l * exp (b * z l) +
          riskMean T z b i ^ 2 * ∑ l ∈ riskSet T i, exp (b * z l) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  have key : riskVar T z b i = (∑ l ∈ riskSet T i, exp (b * z l) * (z l - riskMean T z b i) ^ 2) /
      ∑ l ∈ riskSet T i, exp (b * z l) := by
    rw [hexp]
    simp only [riskVar, riskMean]
    generalize ∑ l ∈ riskSet T i, z l ^ 2 * exp (b * z l) = A at *
    generalize ∑ l ∈ riskSet T i, z l * exp (b * z l) = B at *
    generalize ∑ l ∈ riskSet T i, exp (b * z l) = W at *
    field_simp
    ring
  rw [key]
  exact div_nonneg (sum_nonneg fun l _ => by positivity) hW.le

/-- The observed information is nonnegative. -/
theorem coxInformation_nonneg (b : ℝ) : 0 ≤ coxInformation T δ z b :=
  sum_nonneg fun i _ => riskVar_nonneg T z b i

/-- The scalar Cox score is antitone (the log partial likelihood is concave). -/
theorem antitone_coxScore : Antitone (coxScore T δ z) :=
  antitone_of_deriv_nonpos (fun b => (hasDerivAt_coxScore T δ z b).differentiableAt)
    fun b => by
      rw [(hasDerivAt_coxScore T δ z b).deriv]
      exact neg_nonpos.2 (coxInformation_nonneg T δ z b)

/-- The scalar Cox score is continuous. -/
theorem continuous_coxScore : Continuous (coxScore T δ z) :=
  continuous_iff_continuousAt.2 fun b => (hasDerivAt_coxScore T δ z b).continuousAt

/-- Mean value form of the score increment: `U(b) - U(a) = -I(c) (b - a)` for some `c` between
`a` and `b`. -/
theorem exists_coxScore_sub_eq (a b : ℝ) :
    ∃ c ∈ Set.uIcc a b,
      coxScore T δ z b - coxScore T δ z a = -coxInformation T δ z c * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (coxScore T δ z)
      (fun c => -coxInformation T δ z c) hab (continuous_coxScore T δ z).continuousOn
      fun c _ => hasDerivAt_coxScore T δ z c
    refine ⟨c, Set.uIcc_of_le hab.le ▸ Set.Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']; field_simp [(sub_pos.2 hab).ne']
  · exact ⟨a, Set.left_mem_uIcc, by ring⟩
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (coxScore T δ z)
      (fun c => -coxInformation T δ z c) hab (continuous_coxScore T δ z).continuousOn
      fun c _ => hasDerivAt_coxScore T δ z c
    refine ⟨c, Set.uIcc_of_ge hab.le ▸ Set.Ioo_subset_Icc_self hc, ?_⟩
    rw [hc']; field_simp [(sub_pos.2 hab).ne']; ring

/-- A maximizer of the scalar log partial likelihood is a root of the Cox score. -/
theorem coxScore_eq_zero_of_isMaxOn {b : ℝ} (h : IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) :
    coxScore T δ z b = 0 :=
  (h.isLocalMax Filter.univ_mem).hasDerivAt_eq_zero (hasDerivAt_logPartialLikelihood T δ z b)

/-- A root of the Cox score maximizes the scalar log partial likelihood (concavity). -/
theorem isMaxOn_of_coxScore_eq_zero {b : ℝ} (h : coxScore T δ z b = 0) :
    IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b := by
  have hd : ∀ c, HasDerivAt (logPartialLikelihood₁ T δ z) (coxScore T δ z c) c :=
    hasDerivAt_logPartialLikelihood T δ z
  have hcont : Continuous (logPartialLikelihood₁ T δ z) :=
    continuous_iff_continuousAt.2 fun c => (hd c).continuousAt
  intro c _
  rcases le_total c b with hcb | hbc
  · have hmono : MonotoneOn (logPartialLikelihood₁ T δ z) (Set.Iic b) :=
      monotoneOn_of_deriv_nonneg (convex_Iic b) hcont.continuousOn
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => by
          rw [interior_Iic] at hx
          rw [(hd x).deriv, ← h]
          exact antitone_coxScore T δ z (le_of_lt hx)
    exact hmono hcb le_rfl hcb
  · have hanti : AntitoneOn (logPartialLikelihood₁ T δ z) (Set.Ici b) :=
      antitoneOn_of_deriv_nonpos (convex_Ici b) hcont.continuousOn
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => by
          rw [interior_Ici] at hx
          rw [(hd x).deriv, ← h]
          exact antitone_coxScore T δ z (le_of_lt hx)
    exact hanti le_rfl hbc hbc

/-- Signs of the score at `β₀ ± ε` from a lower bound `m` on the information near `β₀`: if
`|U(β₀)| < ε m` then `U(β₀ + ε) < 0 < U(β₀ - ε)`. -/
theorem coxScore_add_neg_and_sub_pos {β₀ ε m : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < coxInformation T δ z b)
    (hU : |coxScore T δ z β₀| < ε * m) :
    coxScore T δ z (β₀ + ε) < 0 ∧ 0 < coxScore T δ z (β₀ - ε) := by
  obtain ⟨c, hc, hc'⟩ := exists_coxScore_sub_eq T δ z β₀ (β₀ + ε)
  obtain ⟨d, hd, hd'⟩ := exists_coxScore_sub_eq T δ z β₀ (β₀ - ε)
  rw [Set.uIcc_of_le (by linarith)] at hc
  rw [Set.uIcc_of_ge (by linarith)] at hd
  have h1 := hI c ⟨by linarith [hc.1], hc.2⟩
  have h2 := hI d ⟨hd.1, by linarith [hd.2]⟩
  rw [abs_lt] at hU
  constructor <;> nlinarith

/-- **Deterministic core of consistency.** If the information is bounded below by `m` on
`[β₀ - ε, β₀ + ε]` and `|U(β₀)| < ε m`, then the log partial likelihood has a maximizer, and any
`bh` that is a maximizer whenever one exists is a root of the score within `ε` of `β₀`. -/
theorem coxScore_eq_zero_and_abs_sub_lt {β₀ ε m bh : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < coxInformation T δ z b)
    (hU : |coxScore T δ z β₀| < ε * m)
    (hbh : (∃ b, IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ bh) :
    coxScore T δ z bh = 0 ∧ |bh - β₀| < ε := by
  obtain ⟨hplus, hminus⟩ := coxScore_add_neg_and_sub_pos T δ z hε hI hU
  obtain ⟨b, -, hb⟩ := intermediate_value_Icc' (show β₀ - ε ≤ β₀ + ε by linarith)
    (continuous_coxScore T δ z).continuousOn ⟨hplus.le, hminus.le⟩
  have hroot := coxScore_eq_zero_of_isMaxOn T δ z (hbh ⟨b, isMaxOn_of_coxScore_eq_zero T δ z hb⟩)
  refine ⟨hroot, abs_sub_lt_iff.2 ⟨?_, ?_⟩⟩
  · by_contra h
    have := antitone_coxScore T δ z (show β₀ + ε ≤ bh by linarith)
    linarith
  · by_contra h
    have := antitone_coxScore T δ z (show bh ≤ β₀ - ε by linarith)
    linarith

/-- The normalized form of `coxScore_eq_zero_and_abs_sub_lt` used in the asymptotics: if
`|I(b) / n - i(b)| < v / 4` and `|i(b) - v| < v / 4` on `[β₀ - ε, β₀ + ε]` and
`|U(β₀) / n| < ε v / 4`, then `bh` is a root of the score within `ε` of `β₀`. -/
theorem coxScore_eq_zero_and_abs_sub_lt_of_div {i : ℝ → ℝ} {β₀ v ε bh : ℝ} (hn : 0 < n)
    (hv : 0 < v) (hε : 0 < ε) (hiv : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |i b - v| < v / 4)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |coxInformation T δ z b / n - i b| < v / 4)
    (hU : |coxScore T δ z β₀ / n| < ε * v / 4)
    (hbh : (∃ b, IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ bh) :
    coxScore T δ z bh = 0 ∧ |bh - β₀| < ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine coxScore_eq_zero_and_abs_sub_lt T δ z (m := n * v / 2) hε (fun b hb => ?_) ?_ hbh
  · have h1 := abs_lt.1 (hI b hb)
    have h2 := abs_lt.1 (hiv b hb)
    have h3 : v / 2 < coxInformation T δ z b / n := by linarith
    rw [lt_div_iff₀ hn'] at h3
    linarith
  · rw [abs_div, abs_of_pos hn', div_lt_iff₀ hn'] at hU
    nlinarith [mul_pos (mul_pos hε hn') hv]

/-- **Deterministic core of asymptotic normality.** If `bh` is a root of the score within `ε` of
`β₀` and the normalized information `I(b) / n` is within `η ≤ v / 2` of `v` on
`[β₀ - ε, β₀ + ε]`, then `√n (bh - β₀)` differs from `(U(β₀) / √n) / v` by at most
`|U(β₀) / √n| · 2 η / v²`. -/
theorem abs_sqrt_mul_sub_sub_le {β₀ ε v η bh : ℝ} (hn : 0 < n) (hv : 0 < v) (hη : η ≤ v / 2)
    (hroot : coxScore T δ z bh = 0) (hb : |bh - β₀| ≤ ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |coxInformation T δ z b / n - v| < η) :
    |√(n : ℝ) * (bh - β₀) - coxScore T δ z β₀ / √(n : ℝ) / v| ≤
      |coxScore T δ z β₀ / √(n : ℝ)| * (2 * η / v ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
  obtain ⟨c, hc, hc'⟩ := exists_coxScore_sub_eq T δ z β₀ bh
  have hcI : c ∈ Set.Icc (β₀ - ε) (β₀ + ε) := by
    rw [abs_le] at hb
    exact Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hc
  have hJ := abs_lt.1 (hI c hcI)
  set J := coxInformation T δ z c / n with hJdef
  have hJpos : v / 2 < J := by linarith
  have hJ0 : 0 < J := by linarith
  have hIc : coxInformation T δ z c = n * J := by rw [hJdef]; field_simp
  set S := coxScore T δ z β₀ / √(n : ℝ) with hSdef
  have hU : coxScore T δ z β₀ = √(n : ℝ) * S := by rw [hSdef]; field_simp
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

end Deterministic

/-! ### Tightness consequences of convergence in distribution -/

section Probability

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Convergence in distribution implies tightness.** If `X n` converges in distribution, then
for every `ε > 0` there is `M > 0` with `P (M ≤ |X n|) < ε` for all large `n`. -/
theorem exists_eventually_measure_le_abs_lt {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {ε : ENNReal} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, P {ω | M ≤ |X n ω|} < ε := by
  set F : ℕ → Set ℝ := fun k => {x | (k : ℝ) + 1 ≤ |x|} with hF
  have hFc : ∀ k, IsClosed (F k) := fun k => isClosed_le (by fun_prop) (by fun_prop)
  have hanti : Antitone F := fun k l hkl x (hx : (l : ℝ) + 1 ≤ |x|) =>
    show (k : ℝ) + 1 ≤ |x| from le_trans (by gcongr) hx
  have hempty : (⋂ k, F k) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    exact ⟨k, fun (hx : (k : ℝ) + 1 ≤ |x|) => by linarith⟩
  have hlim := tendsto_measure_iInter_atTop (μ := P'.map Z)
    (fun k => (hFc k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨(k : ℝ) + 1, by positivity, ?_⟩
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto (hFc k)
  simp only [ProbabilityMeasure.coe_mk] at hport
  filter_upwards [eventually_lt_of_limsup_lt (hport.trans_lt hk)] with n hn
  rwa [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) (hFc k).measurableSet] at hn

/-- If `X n` converges in distribution, then `X n / √n` converges to `0` in probability. -/
theorem tendstoInMeasure_div_sqrt {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') :
    TendstoInMeasure P (fun n ω => X n ω / √(n : ℝ)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hMn⟩ := exists_eventually_measure_le_abs_lt h hη
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hMn, hsqrt.eventually_gt_atTop (M / ε)] with n hn hn'
  refine le_trans (measure_mono fun ω (hω : ε ≤ ‖X n ω / √(n : ℝ) - 0‖) => ?_) hn.le
  have hpos : 0 < √(n : ℝ) := lt_trans (by positivity) hn'
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hpos, le_div_iff₀ hpos] at hω
  rw [div_lt_iff₀ hε] at hn'
  change M ≤ |X n ω|
  nlinarith

omit [IsProbabilityMeasure P] in
/-- **Continuous mapping for convergence in probability to a constant.** If `f n → c` in
probability and `g` is continuous at `c`, then `g ∘ f n → g c` in probability. -/
theorem tendstoInMeasure_comp_continuousAt_const {f : ℕ → Ω → ℝ} {c : ℝ} {g : ℝ → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => c)) (hg : ContinuousAt g c) :
    TendstoInMeasure P (fun n ω => g (f n ω)) atTop (fun _ => g c) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf η hη)
    (fun _ => zero_le) fun n => measure_mono fun ω (hω : ε ≤ dist (g (f n ω)) (g c)) => ?_
  change η ≤ dist (f n ω) c
  by_contra h
  exact absurd (hη' (lt_of_not_ge h)) (not_lt.2 hω)

omit [IsProbabilityMeasure P'] in
/-- Dividing a centered Gaussian of variance `v ≠ 0` by `v` gives variance `v⁻¹`. -/
theorem hasLaw_div_gaussianReal {Z : Ω' → ℝ} {v : NNReal} (hv : v ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 v) P') :
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' := by
  have h : HasLaw (fun x : ℝ => x / (v : ℝ)) (gaussianReal 0 v⁻¹) (gaussianReal 0 v) := by
    have := hasLaw_map (P := gaussianReal 0 v) (X := fun x : ℝ => x / (v : ℝ)) (by fun_prop)
    rwa [gaussianReal_map_div_const, zero_div,
      show v / NNReal.mk ((v : ℝ) ^ 2) (sq_nonneg _) = v⁻¹ by
        ext; simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_inv]
        have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
        field_simp] at this
  exact h.comp hZ

end Probability

/-! ### The Andersen–Gill theorems for a scalar covariate -/

section AndersenGill

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
  {z : (n : ℕ) → Ω → Fin n → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

/-- **With probability tending to one the Cox estimator is a root of the score near `β₀`.**
Under the Andersen–Gill hypotheses (score limit at `β₀`, uniform convergence in probability of
`I_n(b) / n` to a function `i` continuous at `β₀` with `i β₀ = v > 0`), for every `ε > 0` the
probability that `βhat n` fails to be a root of the score within `ε` of `β₀` tends to zero. -/
theorem tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ (coxScore (T n ω) (δ n ω) (z n ω) (βhat n ω) = 0 ∧
      |βhat n ω - β₀| < ε)}) atTop (𝓝 0) := by
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
  have hU' : |coxScore (T n ω) (δ n ω) (z n ω) β₀ / n| < ε' * v / 4 := by
    have h : ¬ (ε' * v / 4 ≤ ‖coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ) / √(n : ℝ) -
        (0 : Ω → ℝ) ω‖) := hU
    rwa [not_le, Pi.zero_apply, sub_zero, Real.norm_eq_abs, div_div,
      Real.mul_self_sqrt hn'.le] at h
  have hI' : ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b| < v / 4 :=
    fun b hb => lt_of_not_ge fun h => hI ⟨b, hb, h⟩
  have h1 : ε' ≤ r₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : ε' ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  have hgood := coxScore_eq_zero_and_abs_sub_lt_of_div (T n ω) (δ n ω) (z n ω) (i := i)
    (ε := ε') hn hv' hε'0
    (fun b hb => by
      have h := hr₀' (x := b) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb.1, hb.2])
      rwa [hiv, Real.dist_eq] at h)
    (fun b hb => hI' b ⟨by linarith [hb.1], by linarith [hb.2]⟩) hU' (hβhat n ω)
  exact hω ⟨hgood.1, lt_of_lt_of_le hgood.2 (min_le_left _ _)⟩

/-- **Existence of the Cox estimator with probability tending to one** (Andersen–Gill): under the
hypotheses of `tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt`, the probability that the
scalar log partial likelihood has no maximizer tends to zero. -/
theorem tendsto_measure_not_exists_isMaxOn (hv : v ≠ 0)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b,
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b}) atTop (𝓝 0) := by
  classical
  -- Any maximizer-selection works; take one that is a maximizer whenever one exists.
  let βsel : ℕ → Ω → ℝ := fun n ω =>
    if h : ∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b
    then h.choose else 0
  have hsel : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βsel n ω) :=
    fun n ω h => by simp only [βsel, h, ↓reduceDIte]; exact h.choose_spec
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt (βhat := βsel) hv hsel hscore hi hiv
      hinfo hr one_pos) (fun _ => zero_le) fun n => measure_mono fun ω hω hgood => hω
      ⟨βsel n ω, isMaxOn_of_coxScore_eq_zero _ _ _ hgood.1⟩

/-- **Consistency of the Cox estimator** (Andersen–Gill 1982, Theorem 3.2, scalar covariate).
Let `βhat n` be a maximizer of the log partial likelihood of the first `n` subjects whenever one
exists. Assume

* the normalized score at the true coefficient converges in distribution,
  `U_n(β₀) / √n ⟶ Z` (the Andersen–Gill martingale central limit theorem under the Lindeberg
  condition; only `U_n(β₀) / n → 0` in probability is used here), and
* the normalized information converges uniformly in probability on a neighbourhood
  `[β₀ - r, β₀ + r]`, `sup_b |I_n(b) / n - i(b)| → 0`, to a function `i` continuous at `β₀`
  with `i(β₀) = v > 0`.

Then `βhat n → β₀` in probability. -/
theorem tendstoInMeasure_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt hv hβhat hscore hi hiv hinfo hr hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω hgood => ?_
  have h : ε ≤ dist (βhat n ω) β₀ := hω
  rw [Real.dist_eq] at h
  exact absurd hgood.2 (not_lt.2 h)

/-- **The Cox estimator is asymptotically `Z / v`.** Under the hypotheses of
`tendstoInMeasure_coxMPLE` and measurability of the estimator, `√n (βhat n - β₀) ⟶ Z / v` in
distribution, where `Z` is the limit of `Uₙ(β₀) / √n` and `v = i(β₀)` the limiting information.
No Gaussianity is used; see `tendstoInDistribution_coxMPLE_gaussian` for the normal limit. -/
theorem tendstoInDistribution_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' := by
  have hv' : (0 : ℝ) < v := by positivity
  set S : ℕ → Ω → ℝ := fun n ω => coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ) with hSdef
  have hX := hscore.continuous_comp (g := fun x : ℝ => x / (v : ℝ)) (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_
    (fun n => ((hβhat_meas n).sub_const β₀).const_mul _)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨M, hM, hMn⟩ := exists_eventually_measure_le_abs_lt hscore (ENNReal.half_pos hκ.ne')
  set η := min ((v : ℝ) / 4) (ε * (v : ℝ) ^ 2 / (4 * M)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨r₁', hr₁', hr₁''⟩ := Metric.continuousAt_iff.1 hi (η / 2) (by positivity)
  set r₁ := min (r₁' / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hr
  have hG := tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt hv hβhat hscore hi hiv hinfo hr
    hr₁
  have hB := hinfo (η / 2) (by positivity)
  have hGB := hG.add hB
  rw [add_zero] at hGB
  filter_upwards [hMn, (ENNReal.tendsto_nhds_zero.1 hGB) (κ / 2) (ENNReal.half_pos hκ.ne'),
    eventually_gt_atTop 0] with n hn hn' hn0
  let A : Set Ω := {ω | M ≤ |coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)|}
  let B : Set Ω := {ω | ¬ (coxScore (T n ω) (δ n ω) (z n ω) (βhat n ω) = 0 ∧
    |βhat n ω - β₀| < r₁)}
  let C : Set Ω := {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
    η / 2 ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}
  have hA : P A ≤ κ / 2 := hn.le
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
  have hroot' : coxScore (T n ω) (δ n ω) (z n ω) (βhat n ω) = 0 ∧ |βhat n ω - β₀| < r₁ :=
    not_not.1 hroot
  have hI' : ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b| < η / 2 :=
    fun b hb => lt_of_not_ge fun h => hI ⟨b, hb, h⟩
  have h1 : r₁ ≤ r₁' / 2 := min_le_left _ _
  have h2 : r₁ ≤ r := min_le_right _ _
  have hbound := abs_sqrt_mul_sub_sub_le (T n ω) (δ n ω) (z n ω) (ε := r₁) (η := η) hn0 hv'
    (by linarith [min_le_left ((v : ℝ) / 4) (ε * (v : ℝ) ^ 2 / (4 * M))]) hroot'.1
    hroot'.2.le fun b hb => by
      have hib := hr₁'' (x := b) (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb.1, hb.2])
      rw [hiv, Real.dist_eq] at hib
      have hIb := hI' b ⟨by linarith [hb.1], by linarith [hb.2]⟩
      calc |coxInformation (T n ω) (δ n ω) (z n ω) b / n - v|
          ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b| + |i b - v| :=
            abs_sub_le _ _ _
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

/-- **Asymptotic normality of the Cox estimator** (Andersen–Gill 1982, Theorem 3.3, scalar
covariate). Let `βhat n` be a measurable maximizer of the log partial likelihood whenever one
exists. If `Uₙ(β₀) / √n ⟶ Z ~ N(0, v)` and `Iₙ(b) / n → i(b)` uniformly in probability near `β₀`
with `i` continuous at `β₀` and `i(β₀) = v ≠ 0`, then `√n (βhat n - β₀) ⟶ Z / v` in distribution
and `Z / v ~ N(0, v⁻¹)`: the asymptotic variance is the inverse of the information. -/
theorem tendstoInDistribution_coxMPLE_gaussian (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' :=
  ⟨tendstoInDistribution_coxMPLE hv hβhat hβhat_meas hscore hi hiv hinfo hr,
    hasLaw_div_gaussianReal hv hZ⟩

/-- **Consistency of the normalized observed information at the estimator.** Under the
hypotheses of `tendstoInMeasure_coxMPLE`, `Iₙ(βhat n) / n → v` in probability. -/
theorem tendstoInMeasure_coxInformation_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P (fun n ω => coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n) atTop
      (fun _ => (v : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨r₁', hr₁', hr₁''⟩ := Metric.continuousAt_iff.1 hi (ε / 2) (by positivity)
  set r₁ := min (r₁' / 2) r with hr₁def
  have hr₁ : 0 < r₁ := lt_min (by positivity) hr
  have hG := tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt hv hβhat hscore hi hiv hinfo hr
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
  have hroot' : coxScore (T n ω) (δ n ω) (z n ω) (βhat n ω) = 0 ∧ |βhat n ω - β₀| < r₁ :=
    not_not.1 hroot
  have h1 : r₁ ≤ r₁' / 2 := min_le_left _ _
  have h2 : r₁ ≤ r := min_le_right _ _
  have hb := abs_lt.1 hroot'.2
  have hIb : |coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n - i (βhat n ω)| < ε / 2 :=
    lt_of_not_ge fun h => hI ⟨βhat n ω, ⟨by linarith, by linarith⟩, h⟩
  have hib := hr₁'' (x := βhat n ω) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [hiv, Real.dist_eq] at hib
  have hω' : ε ≤ dist (coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n) (v : ℝ) := hω
  rw [Real.dist_eq] at hω'
  have := abs_sub_le (coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n) (i (βhat n ω)) v
  linarith

/-- **Coverage of the Cox Wald interval under the Andersen–Gill conditions.** Under the hypotheses
of `tendstoInDistribution_coxMPLE`, the Wald interval `βhat n ± c / √(I_n(βhat n))` covers the
true coefficient `β₀` with probability tending to the standard-normal mass of `[-c, c]`. This
discharges the two limit hypotheses of `ProcessInference.tendsto_coverage_cox_waldInterval`
(the estimator limit and the consistency of the model-based standard deviation). -/
theorem tendsto_coverage_cox_waldInterval_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r)
    (hsd_meas : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ √(n / coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω))) P) (c : ℝ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | β₀ ∈ ProcessInference.waldInterval (βhat n ω)
        (1 / √(coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω))) c}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-c) c))) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hAN := tendstoInDistribution_coxMPLE hv hβhat hβhat_meas hscore hi hiv hinfo hr
  have hsd := tendstoInMeasure_comp_continuousAt_const (g := fun x => √(x⁻¹))
    (tendstoInMeasure_coxInformation_coxMPLE hv hβhat hscore hi hiv hinfo hr)
    ((continuousAt_inv₀ hv').sqrt)
  refine ProcessInference.tendsto_coverage_cox_waldInterval (inv_ne_zero hv) c hAN
    (hasLaw_div_gaussianReal hv hZ) ?_ hsd_meas
  convert hsd using 3 with n ω
  · rw [inv_div]
  · simp

end AndersenGill

end MathlibExt.Probability.Statistics.CoxAsymptotics
