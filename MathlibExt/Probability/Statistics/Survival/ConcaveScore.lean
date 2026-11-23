/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import MathlibExt.Probability.BoundedInProbability
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Maximizers of random concave criteria: consistency and asymptotic normality

A criterion `ℓ : ℝ → ℝ` is a **concave score** criterion with score `U` and observed information
`I` (`IsConcaveScore ℓ U I`) when `ℓ' = U`, `U' = -I` and `I ≥ 0`. The scalar Cox log partial
likelihood (`CoxAsymptotics.isConcaveScore_cox`) and the weighted Fine–Gray criterion
(`FineGrayAsymptotics.isConcaveScore_fg`) are instances.

For random criteria `ℓₙ(ω)` with scores `Uₙ(ω)` and informations `Iₙ(ω)` this file proves the
Andersen–Gill argument once, from two limit hypotheses:

* (score limit) `Uₙ(β₀) / √n ⟶ Z` in distribution;
* (uniform information) on a neighbourhood `[β₀ - r, β₀ + r]`, `sup_b |Iₙ(b) / n - i(b)| → 0` in
  probability, for a function `i` continuous at `β₀` with `i(β₀) = v > 0`. The supremum is
  stated without measurability assumptions, as
  `P {ω | ∃ b ∈ [β₀ - r, β₀ + r], η ≤ |Iₙ(b) / n - i(b)|} → 0` for every `η > 0`.

The variance of `Z` is not tied to `v`: for Cox the two agree, for Fine–Gray they do not.

## Main results

* Deterministic (`IsConcaveScore` namespace): the score is continuous and antitone
  (`continuous_score`, `antitone_score`); roots of the score are exactly the maximizers
  (`isMaxOn_of_score_eq_zero`, `score_eq_zero_of_isMaxOn`); a lower bound on the information
  near `β₀` and a small score at `β₀` locate every maximizer near `β₀`
  (`score_eq_zero_and_abs_sub_lt`); the one-step mean-value expansion
  `√n (βhat - β₀) ≈ (U(β₀) / √n) / v` (`abs_sqrt_mul_sub_sub_le`).
* `tendstoInMeasure_div_sqrt`: if `Xₙ` converges in distribution, then `Xₙ / √n → 0` in
  probability.
* `tendsto_measure_not_exists_isMaxOn`: with probability tending to one `ℓₙ` has a maximizer.
* `tendstoInMeasure_argmax` (**consistency**): `βhat n → β₀` in probability.
* `tendstoInDistribution_argmax`: `√n (βhat n - β₀) ⟶ Z / v` in distribution, for a measurable
  maximizer selection.
* `tendstoInMeasure_info_argmax`: `Iₙ(βhat n) / n → v` in probability.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3 (the argument).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.ConcaveScore

open MeasureTheory ProbabilityTheory Filter Topology Real

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

/-- Signs of the score at `β₀ ± ε` from a lower bound `m` on the information near `β₀`: if
`|U(β₀)| < ε m` then `U(β₀ + ε) < 0 < U(β₀ - ε)`. -/
theorem score_add_neg_and_sub_pos {β₀ ε m : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < I b) (hU : |U β₀| < ε * m) :
    U (β₀ + ε) < 0 ∧ 0 < U (β₀ - ε) := by
  obtain ⟨c, hc, hc'⟩ := h.exists_score_sub_eq β₀ (β₀ + ε)
  obtain ⟨d, hd, hd'⟩ := h.exists_score_sub_eq β₀ (β₀ - ε)
  rw [Set.uIcc_of_le (by linarith)] at hc
  rw [Set.uIcc_of_ge (by linarith)] at hd
  have h1 := hI c ⟨by linarith [hc.1], hc.2⟩
  have h2 := hI d ⟨hd.1, by linarith [hd.2]⟩
  rw [abs_lt] at hU
  constructor <;> nlinarith

/-- **Deterministic core of consistency.** If the information exceeds `m` on
`[β₀ - ε, β₀ + ε]` and `|U(β₀)| < ε m`, then the criterion has a maximizer, and any `bh` that is
a maximizer whenever one exists is a root of the score within `ε` of `β₀`. -/
theorem score_eq_zero_and_abs_sub_lt {β₀ ε m bh : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < I b) (hU : |U β₀| < ε * m)
    (hbh : (∃ b, IsMaxOn ℓ Set.univ b) → IsMaxOn ℓ Set.univ bh) :
    U bh = 0 ∧ |bh - β₀| < ε := by
  obtain ⟨hplus, hminus⟩ := h.score_add_neg_and_sub_pos hε hI hU
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

/-! ### Tightness consequence of convergence in distribution -/

section Probability

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- If `X n` converges in distribution, then `X n / √n` converges to `0` in probability. -/
theorem tendstoInMeasure_div_sqrt {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') :
    TendstoInMeasure P (fun n ω => X n ω / √(n : ℝ)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨K, hK⟩ := exists_forall_measure_lt_norm_le_of_tendstoInDistribution h hη
  obtain ⟨M, hM, hMn⟩ : ∃ M : ℝ, 0 < M ∧ ∀ n, P {ω | M ≤ |X n ω|} ≤ η := by
    refine ⟨max K 0 + 1, by linarith [le_max_right K 0], fun n => le_trans ?_ (hK n)⟩
    refine measure_mono fun ω (hω : max K 0 + 1 ≤ |X n ω|) => ?_
    change K < |X n ω|
    linarith [le_max_left K 0]
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (M / ε)] with n hn'
  refine le_trans (measure_mono fun ω (hω : ε ≤ ‖X n ω / √(n : ℝ) - 0‖) => ?_) (hMn n)
  have hpos : 0 < √(n : ℝ) := lt_trans (by positivity) hn'
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hpos, le_div_iff₀ hpos] at hω
  rw [div_lt_iff₀ hε] at hn'
  change M ≤ |X n ω|
  nlinarith

end Probability

/-! ### Asymptotics of the maximizer of a random concave criterion -/

section Asymptotics

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℓ U I : ℕ → Ω → ℝ → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

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

end Asymptotics

end MathlibExt.Probability.Statistics.ConcaveScore
