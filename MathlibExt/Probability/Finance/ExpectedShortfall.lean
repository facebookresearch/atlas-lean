/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Quantile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-!
# Expected shortfall of finite losses

For a loss `X` on a finite sample space with probability weights `p` and a level
`0 < α < 1`, expected shortfall is defined by the Rockafellar-Uryasev convex formula
`expectedShortfall p α X = inf_c (c + E[(X - c)⁺] / (1 - α))` and by quantile integration
`quantileExpectedShortfall p α X = (1 - α)⁻¹ ∫_α^1 q_X(u) du`, where `q_X` is the lower
quantile (`ProbabilityTheory.cdfQuantile`) of the loss law. The infimum is attained at the
value-at-risk `q_X(α)`, the two definitions agree, and expected shortfall is subadditive. It is
not the naive conditional mean `E[X | X ≥ VaR]`, which differs when the loss has an atom at the
quantile.

## Main results

* `cdf_lossLaw_eq`: the cdf of the finite loss law.
* `expectedShortfall_eq_valueAtRisk_add`: the convex formula is minimized at value-at-risk.
* `quantileExpectedShortfall_eq_expectedShortfall`: the quantile-integral and convex
  definitions agree.
* `expectedShortfall_add_le`: subadditivity.

## References

* R. T. Rockafellar and S. Uryasev, *Optimization of conditional value-at-risk*, J. Risk 2
  (2000), 21–41.
* C. Acerbi and D. Tasche, *On the coherence of expected shortfall*, J. Banking Finance 26
  (2002), 1487–1503.
* H. Föllmer and T. Knispel, *Convex and coherent risk measures*, Encyclopedia of Quantitative
  Finance (2010), eq. (2.1).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ExpectedShortfall

open Set

open MeasureTheory ProbabilityTheory

/-- The law `∑ ω, p ω • δ_{X ω}` of the loss `X` on a finite sample space with probability
weights `p`. -/
noncomputable def lossLaw {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : Measure ℝ :=
  ∑ ω, ENNReal.ofReal (p ω) • Measure.dirac (X ω)

/-- Expected shortfall at level `α` of the loss `X` under the weights `p`, by the
Rockafellar-Uryasev convex formula `inf_c (c + E[(X - c)⁺] / (1 - α))`. -/
noncomputable def expectedShortfall {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (α : ℝ)
    (X : Ω → ℝ) : ℝ :=
  ⨅ c : ℝ, (c + (∑ ω, p ω * max (X ω - c) 0) / (1 - α))

/-- Expected shortfall at level `α` by quantile integration:
`(1 - α)⁻¹ ∫_α^1 q_X(u) du`, with `q_X` the lower quantile of the loss law. -/
noncomputable def quantileExpectedShortfall {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (α : ℝ)
    (X : Ω → ℝ) : ℝ :=
  (∫ u in α..1, cdfQuantile (lossLaw p X) u) / (1 - α)


/-- The loss law is a probability measure under the standing hypotheses. -/
theorem isProbabilityMeasure_lossLaw {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) :
    IsProbabilityMeasure (lossLaw p X) := by
  refine ⟨?_⟩
  unfold lossLaw
  rw [MeasureTheory.Measure.finsetSum_apply]
  have hdirac : ∀ a : ℝ, (Measure.dirac a) univ = 1 :=
    fun a => Measure.dirac_apply_of_mem (mem_univ a)
  simp only [MeasureTheory.Measure.smul_apply, hdirac, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hp1, ENNReal.ofReal_one]

/-- The cdf of the loss law counts the weights of outcomes with loss below `x`. -/
theorem cdf_lossLaw_eq {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (x : ℝ) :
    cdf (lossLaw p X) x = ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ x), p ω := by
  have : IsProbabilityMeasure (lossLaw p X) := isProbabilityMeasure_lossLaw hp hp1 X
  have h := ProbabilityTheory.ofReal_cdf (lossLaw p X) x
  have hsum : (lossLaw p X) (Iic x) =
      ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ x), ENNReal.ofReal (p ω) := by
    unfold lossLaw
    rw [MeasureTheory.Measure.finsetSum_apply, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    rw [MeasureTheory.Measure.smul_apply]
    by_cases hx : X ω ≤ x
    · have hmem : X ω ∈ Iic x := hx
      simp [Measure.dirac_apply_of_mem hmem, hx]
    · have hmem : X ω ∉ Iic x := hx
      simp [Measure.dirac_apply' _ measurableSet_Iic, hx]
  rw [hsum] at h
  have h2 := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_ofReal (cdf_nonneg (lossLaw p X) x)] at h2
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.ofReal_ne_top)] at h2
  rw [h2]
  apply Finset.sum_congr rfl
  intro ω _
  exact ENNReal.toReal_ofReal (hp ω)

/-- The mass at or below the quantile is at least `α`. -/
private theorem quantile_mass_ge {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X : Ω → ℝ) :
    α ≤ ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ cdfQuantile (lossLaw p X) α), p ω := by
  have hα : α ∈ Ioo (0 : ℝ) 1 := ⟨hα0, hα1⟩
  have hmem := ProbabilityTheory.cdfQuantile_mem (lossLaw p X) hα
  rw [cdf_lossLaw_eq hp hp1] at hmem
  exact hmem

/-- The mass strictly below the quantile is at most `α`. -/
private theorem quantile_mass_lt {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X : Ω → ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω => X ω < cdfQuantile (lossLaw p X) α), p ω ≤ α := by
  have hα : α ∈ Ioo (0 : ℝ) 1 := ⟨hα0, hα1⟩
  set q : ℝ := cdfQuantile (lossLaw p X) α with hq
  have hlt : ∀ x : ℝ, x < q → cdf (lossLaw p X) x < α := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hle := (ProbabilityTheory.cdfQuantile_le_iff (lossLaw p X) hα).mpr hcon
    linarith
  by_cases hS : (Finset.univ.filter (fun ω : Ω => X ω < q)).Nonempty
  · obtain ⟨ωstar, hmem, hmax⟩ := Finset.exists_max_image _ X hS
    have hstar : X ωstar < q := (Finset.mem_filter.mp hmem).2
    have hfilter : Finset.univ.filter (fun ω => X ω ≤ X ωstar) =
        Finset.univ.filter (fun ω => X ω < q) := by
      apply Finset.filter_congr
      intro ω _
      constructor
      · intro hle
        exact lt_of_le_of_lt hle hstar
      · intro hlt'
        have hω : ω ∈ Finset.univ.filter (fun ω => X ω < q) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hlt'⟩
        exact hmax ω hω
    have h1 := hlt (X ωstar) hstar
    rw [cdf_lossLaw_eq hp hp1] at h1
    rw [hfilter] at h1
    exact le_of_lt h1
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    exact le_of_lt hα0

/-- Mass above `c` plus mass at or below `c` is one. -/
private theorem mass_gt_eq {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (c : ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω => c < X ω), p ω =
      1 - ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ c), p ω := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => X ω ≤ c) p
  have hfilter : Finset.univ.filter (fun ω => ¬X ω ≤ c) =
      Finset.univ.filter (fun ω => c < X ω) := by
    apply Finset.filter_congr
    intro ω _
    exact not_le
  rw [hfilter] at h
  have hp1' : ∑ x ∈ Finset.univ, p x = 1 := hp1
  rw [hp1'] at h
  linarith

/-- Mass at or above `c` plus mass strictly below `c` is one. -/
private theorem mass_ge_eq {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) (c : ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω => c ≤ X ω), p ω =
      1 - ∑ ω ∈ Finset.univ.filter (fun ω => X ω < c), p ω := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => X ω < c) p
  have hfilter : Finset.univ.filter (fun ω => ¬X ω < c) =
      Finset.univ.filter (fun ω => c ≤ X ω) := by
    apply Finset.filter_congr
    intro ω _
    exact not_lt
  rw [hfilter] at h
  have hp1' : ∑ x ∈ Finset.univ, p x = 1 := hp1
  rw [hp1'] at h
  linarith

/-- Pointwise upper slope bound for the positive part. -/
private theorem posPart_sub_le {q c x pw : ℝ} (hpw : 0 ≤ pw) (_hqc : q < c) :
    pw * max (x - q) 0 - pw * max (x - c) 0 ≤ (if q < x then (c - q) * pw else 0) := by
  by_cases hx : q < x
  · simp only [hx, ite_true]
    have h1 : max (x - q) 0 = x - q := max_eq_left (by linarith)
    have h2 : x - c ≤ max (x - c) 0 := le_max_left _ _
    have h3 : pw * (x - c) ≤ pw * max (x - c) 0 :=
      mul_le_mul_of_nonneg_left h2 hpw
    rw [h1]
    linarith
  · simp only [hx, ite_false]
    have hx' : x ≤ q := le_of_not_gt hx
    have h1 : max (x - q) 0 = 0 := max_eq_right (by linarith)
    have h2 : 0 ≤ max (x - c) 0 := le_max_right _ _
    have h3 : 0 ≤ pw * max (x - c) 0 := mul_nonneg hpw h2
    rw [h1, mul_zero, zero_sub]
    linarith

/-- Pointwise lower slope bound for the positive part. -/
private theorem posPart_sub_ge {c q x pw : ℝ} (hpw : 0 ≤ pw) (hcq : c < q) :
    (if q ≤ x then (q - c) * pw else 0) ≤
      pw * max (x - c) 0 - pw * max (x - q) 0 := by
  by_cases hx : q ≤ x
  · simp only [hx, ite_true]
    have h1 : max (x - c) 0 = x - c := max_eq_left (by linarith)
    have h2 : max (x - q) 0 = x - q := max_eq_left (by linarith)
    rw [h1, h2]
    have heq : pw * (x - c) - pw * (x - q) = (q - c) * pw := by ring
    rw [heq]
  · simp only [hx, ite_false]
    have hx' : x < q := lt_of_not_ge hx
    have h1 : max (x - q) 0 = 0 := max_eq_right (by linarith)
    have h2 : 0 ≤ max (x - c) 0 := le_max_right _ _
    have h3 : 0 ≤ pw * max (x - c) 0 := mul_nonneg hpw h2
    rw [h1, mul_zero, sub_zero]
    exact h3

/-- The Rockafellar-Uryasev objective at any `c` exceeds its value at the quantile. -/
private theorem obj_ge_quantile {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X : Ω → ℝ) (c : ℝ) :
    cdfQuantile (lossLaw p X) α +
        (∑ ω, p ω * max (X ω - cdfQuantile (lossLaw p X) α) 0) / (1 - α) ≤
      c + (∑ ω, p ω * max (X ω - c) 0) / (1 - α) := by
  set q : ℝ := cdfQuantile (lossLaw p X) α with hq
  have hd : (0 : ℝ) < 1 - α := by linarith
  have key : (q - c) * (1 - α) ≤
      (∑ ω, p ω * max (X ω - c) 0) - (∑ ω, p ω * max (X ω - q) 0) := by
    rcases lt_trichotomy c q with hcq | hcq | hcq
    · have hper : ∀ ω ∈ Finset.univ,
          (if q ≤ X ω then (q - c) * p ω else 0) ≤
            p ω * max (X ω - c) 0 - p ω * max (X ω - q) 0 :=
        fun ω _ => posPart_sub_ge (hp ω) hcq
      have hsum := Finset.sum_le_sum hper
      rw [← Finset.sum_filter, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
      have hle : (1 : ℝ) - α ≤
          ∑ ω ∈ Finset.univ.filter (fun ω => q ≤ X ω), p ω := by
        rw [mass_ge_eq hp1 X q]
        have h2 := quantile_mass_lt hp hp1 hα0 hα1 X
        rw [← hq] at h2
        linarith
      have hmass := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ q - c by linarith)
      linarith
    · rw [hcq]
      simp
    · have hper : ∀ ω ∈ Finset.univ,
          p ω * max (X ω - q) 0 - p ω * max (X ω - c) 0 ≤
            (if q < X ω then (c - q) * p ω else 0) :=
        fun ω _ => posPart_sub_le (hp ω) hcq
      have hsum := Finset.sum_le_sum hper
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
      have hle : ∑ ω ∈ Finset.univ.filter (fun ω => q < X ω), p ω ≤ 1 - α := by
        rw [mass_gt_eq hp1 X q]
        have h1 := quantile_mass_ge hp hp1 hα0 hα1 X
        rw [← hq] at h1
        linarith
      have hmass := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ c - q by linarith)
      linarith
  have h2 : q - c ≤
      ((∑ ω, p ω * max (X ω - c) 0) - (∑ ω, p ω * max (X ω - q) 0)) / (1 - α) :=
    (le_div_iff₀ hd).mpr key
  rw [sub_div] at h2
  linarith

/-- The Rockafellar-Uryasev infimum is attained at the value-at-risk `q_X(α)`, the lower
`α`-quantile of the loss. -/
theorem expectedShortfall_eq_valueAtRisk_add {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X : Ω → ℝ) :
    expectedShortfall p α X =
      cdfQuantile (lossLaw p X) α +
        (∑ ω, p ω * max (X ω - cdfQuantile (lossLaw p X) α) 0) / (1 - α) := by
  unfold expectedShortfall
  exact ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun c => obj_ge_quantile hp hp1 hα0 hα1 X c)
    (fun _ ha' => ⟨cdfQuantile (lossLaw p X) α, ha'⟩)

/-- Upper bound for the quantile from a uniform upper bound on losses. -/
private theorem quantile_le_of_cdf_eq_one {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) {u x : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : ∀ ω, X ω ≤ x) :
    cdfQuantile (lossLaw p X) u ≤ x := by
  apply (ProbabilityTheory.cdfQuantile_le_iff _ hu).mpr
  have hfilter : Finset.univ.filter (fun ω => X ω ≤ x) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ => hx ω)
  rw [cdf_lossLaw_eq hp hp1 X, hfilter, hp1]
  exact hu.2.le

/-- Lower bound for the quantile from uniform bounds on losses. -/
private theorem le_quantile_of_cdf_eq_zero {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (X : Ω → ℝ) {u x y : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hx : ∀ ω, X ω ≤ x) (hy : ∀ ω, y ≤ X ω) :
    y ≤ cdfQuantile (lossLaw p X) u := by
  unfold ProbabilityTheory.cdfQuantile
  simp only [hu, ite_true]
  refine le_csInf ⟨x, ?_⟩ (fun z hz => ?_)
  · change u ≤ cdf (lossLaw p X) x
    have hfilter : Finset.univ.filter (fun ω => X ω ≤ x) = Finset.univ :=
      Finset.filter_true_of_mem (fun ω _ => hx ω)
    rw [cdf_lossLaw_eq hp hp1 X, hfilter, hp1]
    exact hu.2.le
  · have hz : u ≤ cdf (lossLaw p X) z := hz
    by_contra hcon
    push Not at hcon
    have hempty : Finset.univ.filter (fun ω => X ω ≤ z) = ∅ :=
      Finset.filter_false_of_mem (fun ω _ hle => by linarith [hy ω])
    rw [cdf_lossLaw_eq hp hp1 X, hempty, Finset.sum_empty] at hz
    linarith [hu.1]

/-- The quantile-integral and Rockafellar-Uryasev definitions of expected shortfall agree on
finite loss distributions. -/
theorem quantileExpectedShortfall_eq_expectedShortfall {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X : Ω → ℝ) :
    quantileExpectedShortfall p α X = expectedShortfall p α X := by
  have hES := expectedShortfall_eq_valueAtRisk_add hp hp1 hα0 hα1 X
  have hprob0 : IsProbabilityMeasure (lossLaw p X) := isProbabilityMeasure_lossLaw hp hp1 X
  have hd : (0 : ℝ) < 1 - α := by linarith
  have hd' : (1 : ℝ) - α ≠ 0 := ne_of_gt hd
  have hα : α ∈ Ioo (0 : ℝ) 1 := ⟨hα0, hα1⟩
  have hα1' : α ≤ 1 := le_of_lt hα1
  unfold quantileExpectedShortfall
  set μ : Measure ℝ := lossLaw p X with hμ
  set t : ℝ := cdfQuantile μ α with ht
  have hΩ : Nonempty Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have huniv : (Finset.univ : Finset Ω) = ∅ := Finset.univ_eq_empty
    rw [huniv, Finset.sum_empty] at hp1
    norm_num at hp1
  obtain ⟨ωmax, -, hmax⟩ := Finset.exists_max_image Finset.univ X
    (Finset.univ_nonempty_iff.mpr hΩ)
  obtain ⟨ωmin, -, hmin'⟩ := Finset.exists_max_image Finset.univ (fun ω => -X ω)
    (Finset.univ_nonempty_iff.mpr hΩ)
  have hmin : ∀ ω' ∈ (Finset.univ : Finset Ω), X ωmin ≤ X ω' := by
    intro ω' hω'
    have h := hmin' ω' hω'
    linarith
  have hqb : ∀ u ∈ Ioo (0 : ℝ) 1, ‖cdfQuantile μ u‖ ≤ |X ωmin| + |X ωmax| := by
    intro u hu
    have h1 := quantile_le_of_cdf_eq_one hp hp1 X hu
      (fun ω => hmax ω (Finset.mem_univ ω))
    have h2 := le_quantile_of_cdf_eq_zero hp hp1 X hu
      (fun ω => hmax ω (Finset.mem_univ ω)) (fun ω => hmin ω (Finset.mem_univ ω))
    rw [← hμ] at h1 h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1, h2, abs_nonneg (X ωmin), abs_nonneg (X ωmax),
      le_abs_self (X ωmin), le_abs_self (X ωmax),
      neg_abs_le (X ωmin), neg_abs_le (X ωmax)]
  have hq_all : ∀ u : ℝ, ‖cdfQuantile μ u‖ ≤ |X ωmin| + |X ωmax| := by
    intro u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · exact hqb u hu
    · have hq0 : cdfQuantile μ u = 0 := by
        unfold ProbabilityTheory.cdfQuantile
        simp only [hu, ite_false]
      rw [hq0, norm_zero]
      positivity
  have hf_all : ∀ u : ℝ, ‖max (cdfQuantile μ u - t) 0‖ ≤
      (|X ωmin| + |X ωmax|) + |t| := by
    intro u
    have hq := hq_all u
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have hq' : |cdfQuantile μ u| ≤ |X ωmin| + |X ωmax| := by
      rwa [Real.norm_eq_abs] at hq
    calc max (cdfQuantile μ u - t) 0 ≤ |cdfQuantile μ u - t| :=
            max_le (le_abs_self _) (abs_nonneg _)
      _ ≤ |cdfQuantile μ u| + |t| := abs_sub _ _
      _ ≤ (|X ωmin| + |X ωmax|) + |t| := by linarith
  have hq_meas : Measurable (cdfQuantile μ) :=
    ProbabilityTheory.measurable_cdfQuantile μ
  have hq_ae : AEStronglyMeasurable (cdfQuantile μ) (volume.restrict (Ioc α 1)) :=
    hq_meas.aestronglyMeasurable
  have hf_ae : AEStronglyMeasurable (fun u : ℝ => max (cdfQuantile μ u - t) 0)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((hq_meas.sub_const t).max measurable_const).aestronglyMeasurable
  have hvol_Ioc : volume (Ioc α 1 : Set ℝ) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hvol_Ioo01 : volume (Ioo (0 : ℝ) 1 : Set ℝ) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hq_intOn : IntegrableOn (cdfQuantile μ) (Ioc α 1) volume :=
    IntegrableOn.of_bound hvol_Ioc hq_ae (|X ωmin| + |X ωmax|)
      (Filter.Eventually.of_forall hq_all)
  have hf_intOn : IntegrableOn (fun u : ℝ => max (cdfQuantile μ u - t) 0)
      (Ioo (0 : ℝ) 1) volume :=
    IntegrableOn.of_bound hvol_Ioo01 hf_ae ((|X ωmin| + |X ωmax|) + |t|)
      (Filter.Eventually.of_forall hf_all)
  have hq_int : IntervalIntegrable (cdfQuantile μ) volume α 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hα1').mpr hq_intOn
  have ht_int : IntervalIntegrable (fun _ : ℝ => t) volume α 1 :=
    intervalIntegrable_const
  have hsub_int : IntervalIntegrable (fun u : ℝ => cdfQuantile μ u - t) volume α 1 :=
    hq_int.sub ht_int
  have hsplit : (∫ u in α..1, cdfQuantile μ u) =
      (∫ u in α..1, t) + ∫ u in α..1, (cdfQuantile μ u - t) := by
    have hrewrite : (fun u : ℝ => cdfQuantile μ u) =
        (fun u : ℝ => t + (cdfQuantile μ u - t)) := funext fun u => by ring
    rw [hrewrite]
    exact intervalIntegral.integral_add ht_int hsub_int
  have hconst : (∫ u in α..1, t) = t * (1 - α) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsub_eq : (∫ u in α..1, (cdfQuantile μ u - t)) =
      ∑ ω, p ω * max (X ω - t) 0 := by
    rw [intervalIntegral.integral_of_le hα1']
    have hae1 : (Ioc α 1 : Set ℝ) =ᵐ[volume] Ioo α 1 :=
      (Ioo_ae_eq_Ioc' Real.volume_singleton).symm
    rw [setIntegral_congr_set hae1]
    have hqf : EqOn (fun u : ℝ => cdfQuantile μ u - t)
        (fun u : ℝ => max (cdfQuantile μ u - t) 0) (Ioo α 1) := by
      intro u hu
      change cdfQuantile μ u - t = max (cdfQuantile μ u - t) 0
      have hu0 : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hα0 hu.1.le, hu.2⟩
      have hmono := ProbabilityTheory.cdfQuantile_monoOn μ hα hu0 hu.1.le
      rw [← ht] at hmono
      have hle : (0 : ℝ) ≤ cdfQuantile μ u - t := by linarith
      exact (max_eq_left hle).symm
    rw [setIntegral_congr_fun measurableSet_Ioo hqf]
    have hinter : (Ioo (0 : ℝ) 1) ∩ Ioo α 1 = Ioo α 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨⟨-, -⟩, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨⟨lt_trans hα0 h3, h4⟩, h3, h4⟩
    have hsdiff : (Ioo (0 : ℝ) 1) \ Ioo α 1 = Ioc 0 α := by
      ext u
      simp only [mem_sdiff, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, le_of_not_gt (fun h => h3 ⟨h, h2⟩)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, lt_of_le_of_lt h2 hα1⟩, ?_⟩
        rintro ⟨h3, -⟩
        linarith
    have htIoo : MeasurableSet (Ioo α 1 : Set ℝ) := measurableSet_Ioo
    have hsplit2 := integral_inter_add_sdiff htIoo hf_intOn
    rw [hinter, hsdiff] at hsplit2
    have hzero : (∫ u in Ioc (0 : ℝ) α, max (cdfQuantile μ u - t) 0) = 0 := by
      have hqf0 : EqOn (fun u : ℝ => max (cdfQuantile μ u - t) 0)
          (fun _ : ℝ => (0 : ℝ)) (Ioc 0 α) := by
        intro u hu
        change max (cdfQuantile μ u - t) 0 = 0
        have hu0 : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, lt_of_le_of_lt hu.2 hα1⟩
        have hmono := ProbabilityTheory.cdfQuantile_monoOn μ hu0 hα hu.2
        rw [← ht] at hmono
        apply max_eq_right
        linarith
      rw [setIntegral_congr_fun measurableSet_Ioc hqf0]
      exact integral_zero _ _
    have hIoo01 : (∫ u in Ioo α 1, max (cdfQuantile μ u - t) 0) =
        ∫ u in Ioo (0 : ℝ) 1, max (cdfQuantile μ u - t) 0 := by
      linarith [hsplit2, hzero]
    have hae2 : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] Icc 0 1 := Ioo_ae_eq_Icc
    have hdirac : (∫ x, max (x - t) 0 ∂μ) = ∑ ω, p ω * max (X ω - t) 0 := by
      have h_all : ∀ ω ∈ (Finset.univ : Finset Ω),
          Integrable (fun x : ℝ => max (x - t) 0)
            (ENNReal.ofReal (p ω) • Measure.dirac (X ω)) :=
        fun ω _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
      rw [hμ]
      unfold lossLaw
      rw [integral_finsetSum_measure h_all]
      apply Finset.sum_congr rfl
      intro ω _
      rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal (hp ω), smul_eq_mul]
    have hmap_eq := ProbabilityTheory.map_cdfQuantile_restrict_Icc μ
    have hφ : AEMeasurable (cdfQuantile μ) (volume.restrict (Icc (0 : ℝ) 1)) :=
      hq_meas.aemeasurable
    have hg_meas : AEStronglyMeasurable (fun x : ℝ => max (x - t) 0)
        (Measure.map (cdfQuantile μ) (volume.restrict (Icc (0 : ℝ) 1))) :=
      ((measurable_id.sub_const t).max measurable_const).aestronglyMeasurable
    have hpush : (∫ x, max (x - t) 0 ∂μ) =
        ∫ u, max (cdfQuantile μ u - t) 0 ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
      conv_lhs => rw [← hmap_eq]
      exact integral_map hφ hg_meas
    have hmap : (∫ u in Icc (0 : ℝ) 1, max (cdfQuantile μ u - t) 0) =
        ∑ ω, p ω * max (X ω - t) 0 := by
      rw [← hdirac]
      exact hpush.symm
    rw [hIoo01, setIntegral_congr_set hae2]
    exact hmap
  have hint : (∫ u in α..1, cdfQuantile μ u) =
      t * (1 - α) + (∑ ω, p ω * max (X ω - t) 0) := by
    rw [hsplit, hconst, hsub_eq]
  rw [hES, hint, add_div, mul_div_cancel_right₀ _ hd']

/-- **Subadditivity of expected shortfall** for losses on a finite probability space. -/
theorem expectedShortfall_add_le {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (X Y : Ω → ℝ) :
    expectedShortfall p α (X + Y) ≤ expectedShortfall p α X + expectedShortfall p α Y := by
  have hX := expectedShortfall_eq_valueAtRisk_add hp hp1 hα0 hα1 X
  have hY := expectedShortfall_eq_valueAtRisk_add hp hp1 hα0 hα1 Y
  have hd : (0 : ℝ) < 1 - α := by linarith
  set qX : ℝ := cdfQuantile (lossLaw p X) α with hqX
  set qY : ℝ := cdfQuantile (lossLaw p Y) α with hqY
  have hper : ∀ ω ∈ Finset.univ, p ω * max ((X + Y) ω - (qX + qY)) 0 ≤
      p ω * max (X ω - qX) 0 + p ω * max (Y ω - qY) 0 := by
    intro ω _
    have hmax : max ((X ω - qX) + (Y ω - qY)) 0 ≤
        max (X ω - qX) 0 + max (Y ω - qY) 0 := by
      apply max_le
      · linarith [le_max_left (X ω - qX) 0, le_max_left (Y ω - qY) 0]
      · linarith [le_max_right (X ω - qX) 0, le_max_right (Y ω - qY) 0]
    have hXYω : (X + Y) ω - (qX + qY) = (X ω - qX) + (Y ω - qY) := by
      rw [Pi.add_apply]; ring
    rw [hXYω]
    have h := mul_le_mul_of_nonneg_left hmax (hp ω)
    rw [mul_add] at h
    exact h
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib] at hsum
  have hdiv : (∑ ω, p ω * max ((X + Y) ω - (qX + qY)) 0) / (1 - α) ≤
      ((∑ ω, p ω * max (X ω - qX) 0) + (∑ ω, p ω * max (Y ω - qY) 0)) / (1 - α) := by
    have hd' : (0 : ℝ) ≤ (1 - α)⁻¹ := inv_nonneg.mpr (le_of_lt hd)
    have h := mul_le_mul_of_nonneg_right hsum hd'
    rwa [div_eq_mul_inv, div_eq_mul_inv]
  rw [add_div] at hdiv
  have hle : expectedShortfall p α (X + Y) ≤
      (qX + qY) + (∑ ω, p ω * max ((X + Y) ω - (qX + qY)) 0) / (1 - α) := by
    unfold expectedShortfall
    refine ciInf_le ?_ (qX + qY)
    refine ⟨cdfQuantile (lossLaw p (X + Y)) α +
      (∑ ω, p ω * max ((X + Y) ω - cdfQuantile (lossLaw p (X + Y)) α) 0) / (1 - α),
      ?_⟩
    rintro _ ⟨c, rfl⟩
    exact obj_ge_quantile hp hp1 hα0 hα1 (X + Y) c
  rw [hX, hY]
  linarith [hle, hdiv]

end MathlibExt.Probability.Finance.ExpectedShortfall
