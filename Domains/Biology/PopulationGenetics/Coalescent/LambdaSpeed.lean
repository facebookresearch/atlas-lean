/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace exponent and speed of coming down from infinity

For a finite measure `Λ` on `[0, 1]`, the Laplace exponent of the
Λ-coalescent is
`ψ(q) = ∫ (e^{-qx} - 1 + qx) x^{-2} Λ(dx)`, with the integrand at `x = 0`
read by continuity as `q² / 2`. Thus an atom at `0` contributes
`Λ {0} q² / 2`, and Kingman's coalescent `Λ = δ₀` has `ψ q = q² / 2`.

Under Grey's condition `∫_a^∞ dq / ψ(q) < ∞`, put
`u(t) = ∫_t^∞ dq / ψ(q)` and let `v` be its inverse, written here as
`psiTail` and `speed`. This file proves the basic analytic properties of
`ψ`, Grey's condition for some `a > 0` iff for every `a > 0`, the inverse
identities and limits for `u` and `v`, the Kingman-extremal lower bounds,
and the Kingman special case. The Beta(2 - α, α) asymptotic for `ψ` is a
separate statement.

## References

* J. Berestycki, N. Berestycki, and V. Limic, "The Λ-coalescent speed of
  coming down from infinity", *Annals of Probability* 38 (2010), 207–233.
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval Real ProbabilityTheory

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-- The kernel of `ψ`: `(e^{-qx} - 1 + qx) / x²` for `x ≠ 0`, with its continuous value
`q² / 2` at `x = 0`. -/
def psiKernel (q x : ℝ) : ℝ :=
  if x = 0 then q ^ 2 / 2 else (exp (-(q * x)) - 1 + q * x) / x ^ 2

/-- **The Laplace exponent** `ψ(q) = ∫_{[0,1]} (e^{-qx} - 1 + qx) x^{-2} Λ(dx)` of the
Λ-coalescent, for every real `q`, with the integrand at `x = 0` given its continuous value
`q² / 2` (`psiKernel`), so that an atom of `Λ` at `0` contributes `Λ{0} q² / 2` (BBL eq. (3)
with `ν = x^{-2} Λ`, the `x = 0` term as in eq. (6)). -/
def psi (Λ : Measure I) [IsFiniteMeasure Λ] (q : ℝ) : ℝ :=
  ∫ x, psiKernel q x ∂Λ

/-- **Grey's condition** (BBL eq. (4)): `Λ ≠ 0` and `q ↦ 1 / ψ(q)` integrable on `(a, ∞)` for
some `a > 0`, that is, the integral of the nonnegative `1 / ψ` over `(a, ∞)`, taken in `[0, ∞]`,
is finite. This is not finiteness of the real-valued `psiTail`, which is always finite (it is `0`
when `1 / ψ` is not integrable, e.g. for `Λ = δ₁`, where `ψ(q) = e^{-q} - 1 + q`). The clause
`Λ ≠ 0` excludes the degenerate case `ψ ≡ 0`, where `ψ⁻¹ = 0` (by `1 / 0 = 0`) would be
integrable. -/
def GreyCondition (Λ : Measure I) [IsFiniteMeasure Λ] : Prop :=
  Λ ≠ 0 ∧ ∃ a, 0 < a ∧ IntegrableOn (fun q => (psi Λ q)⁻¹) (Ioi a)

/-- `u(t) = ∫_t^∞ dq / ψ(q)` (BBL eq. (7)), with `1 / ψ(q)` read as `0` where `ψ(q) = 0`;
the integral is `0` when `1 / ψ` is not integrable on `(t, ∞)`. Hence `u ≡ 0` when Grey's
condition fails (for `Λ = 0` because the integrand is `0`), and `u(t) = 0` for `t ≤ 0` when
`Λ ≠ 0`, since `1 / ψ(q) ≥ 2 / (Λ[0,1] q²)` for `q > 0`. -/
def psiTail (Λ : Measure I) [IsFiniteMeasure Λ] (t : ℝ) : ℝ :=
  ∫ q in Ioi t, (psi Λ q)⁻¹

/-- **The speed of coming down from infinity** `v(t) = inf {s > 0 : ∫_s^∞ dq / ψ(q) < t}`
(BBL eq. (8)). The infimum of the empty set is `0`; as `u ≥ 0`, `v(t) = 0` for `t ≤ 0`. When
Grey's condition fails, `u ≡ 0`, so `v ≡ 0`. -/
def speed (Λ : Measure I) [IsFiniteMeasure Λ] (t : ℝ) : ℝ :=
  sInf {s | 0 < s ∧ psiTail Λ s < t}

/-! ### Pointwise facts about the kernel -/

private lemma kernel_num_nonneg (y : ℝ) : 0 ≤ Real.exp (-y) - 1 + y := by
  have := Real.add_one_le_exp (-y)
  linarith

private lemma psiKernel_nonneg (q x : ℝ) : 0 ≤ psiKernel q x := by
  unfold psiKernel
  split_ifs with h
  · positivity
  · exact div_nonneg (kernel_num_nonneg (q * x)) (sq_nonneg x)

private lemma psiKernel_pos {q : ℝ} (hq : q ≠ 0) (x : ℝ) : 0 < psiKernel q x := by
  unfold psiKernel
  split_ifs with h
  · positivity
  · have hqx : -(q * x) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hq h)
    have := Real.add_one_lt_exp hqx
    exact div_pos (by linarith) (by positivity)

private lemma exp_neg_sub_le {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) - 1 + y ≤ y ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hy
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-y) := Real.exp_pos _
  have hB : 0 < 1 + y + y ^ 2 / 2 := by positivity
  have h4 : Real.exp (-y) * (1 + y + y ^ 2 / 2) ≤ 1 := by
    calc Real.exp (-y) * (1 + y + y ^ 2 / 2) ≤ Real.exp (-y) * Real.exp y :=
          mul_le_mul_of_nonneg_left h1 h3.le
      _ = 1 := h2
  nlinarith [sq_nonneg (y ^ 2)]

private lemma exp_sub_one_sub_le (z : ℝ) : Real.exp z - 1 - z ≤ z ^ 2 * Real.exp |z| := by
  rcases le_or_gt (-1) z with hz | hz
  · have h1 := Real.add_one_le_exp (-z)
    have h2 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have h4 : 0 < Real.exp z := Real.exp_pos z
    have h5 : (1 - z) * Real.exp z ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right h1 h4.le]
    have h6 : Real.exp z - z ^ 2 * Real.exp z ≤ 1 + z := by
      nlinarith [mul_le_mul_of_nonneg_left h5 (show 0 ≤ 1 + z by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg z)]
  · have h1 : Real.exp z ≤ 1 := by
      have := Real.exp_le_exp.mpr (show z ≤ 0 by linarith)
      rwa [Real.exp_zero] at this
    have h2 : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
    have h3 : |z| = -z := abs_of_neg (by linarith)
    nlinarith [mul_pos_of_neg_of_neg (show z < 0 by linarith) (show z + 1 < 0 by linarith),
      le_mul_of_one_le_right (sq_nonneg z) h2]

private lemma psiKernel_le {q x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) : psiKernel q x ≤ q ^ 2 / 2 := by
  unfold psiKernel
  split_ifs with h
  · exact le_rfl
  · have hx2 : 0 < x ^ 2 := by positivity
    rw [div_le_iff₀ hx2]
    calc Real.exp (-(q * x)) - 1 + q * x ≤ (q * x) ^ 2 / 2 := exp_neg_sub_le (mul_nonneg hq hx)
      _ = q ^ 2 / 2 * x ^ 2 := by ring

private lemma psiKernel_abs_le {q x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |psiKernel q x| ≤ q ^ 2 * Real.exp |q| := by
  rw [abs_of_nonneg (psiKernel_nonneg q x)]
  have hE : 1 ≤ Real.exp |q| := Real.one_le_exp (abs_nonneg q)
  unfold psiKernel
  split_ifs with h
  · nlinarith [sq_nonneg q]
  · have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have hx2 : 0 < x ^ 2 := by positivity
    rw [div_le_iff₀ hx2]
    have h1 := exp_sub_one_sub_le (-(q * x))
    have h2 : |-(q * x)| ≤ |q| := by
      rw [abs_neg, abs_mul, abs_of_pos hx]
      exact mul_le_of_le_one_right (abs_nonneg q) hx1
    have h3 : Real.exp |-(q * x)| ≤ Real.exp |q| := Real.exp_le_exp.mpr h2
    calc Real.exp (-(q * x)) - 1 + q * x = Real.exp (-(q * x)) - 1 - -(q * x) := by ring
      _ ≤ (-(q * x)) ^ 2 * Real.exp |-(q * x)| := h1
      _ ≤ (-(q * x)) ^ 2 * Real.exp |q| := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = q ^ 2 * Real.exp |q| * x ^ 2 := by ring

private lemma psiKernel_convex (x : ℝ) {q₁ q₂ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    psiKernel (a * q₁ + b * q₂) x ≤ a * psiKernel q₁ x + b * psiKernel q₂ x := by
  unfold psiKernel
  split_ifs with h
  · have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg (q₁ - q₂), mul_nonneg ha hb]
  · have hx2 : 0 < x ^ 2 := by positivity
    have hconv := convexOn_exp.2 (Set.mem_univ (-(q₁ * x))) (Set.mem_univ (-(q₂ * x))) ha hb hab
    simp only [smul_eq_mul] at hconv
    have e : a * -(q₁ * x) + b * -(q₂ * x) = -((a * q₁ + b * q₂) * x) := by ring
    rw [e] at hconv
    have e2 : a * ((Real.exp (-(q₁ * x)) - 1 + q₁ * x) / x ^ 2) +
        b * ((Real.exp (-(q₂ * x)) - 1 + q₂ * x) / x ^ 2) =
        (a * (Real.exp (-(q₁ * x)) - 1 + q₁ * x) + b * (Real.exp (-(q₂ * x)) - 1 + q₂ * x)) /
          x ^ 2 := by ring
    rw [e2, div_le_div_iff_of_pos_right hx2]
    nlinarith

private lemma psiKernel_mono {q₁ q₂ x : ℝ} (hq₁ : 0 ≤ q₁) (h12 : q₁ ≤ q₂) (hx : 0 ≤ x) :
    psiKernel q₁ x ≤ psiKernel q₂ x := by
  unfold psiKernel
  split_ifs with h
  · nlinarith
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    have hx2 : 0 < x ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hx2]
    have hd : 0 ≤ q₂ * x - q₁ * x := by nlinarith
    have h1 := Real.add_one_le_exp (-(q₂ * x - q₁ * x))
    have h2 : Real.exp (-(q₂ * x)) =
        Real.exp (-(q₁ * x)) * Real.exp (-(q₂ * x - q₁ * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(q₁ * x)) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show -(q₁ * x) ≤ 0 by nlinarith)
      rwa [Real.exp_zero] at this
    have h4 : 0 < Real.exp (-(q₁ * x)) := Real.exp_pos _
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 h4.le, mul_le_mul_of_nonneg_right h3 hd]

private lemma measurable_psiKernel (q : ℝ) : Measurable (psiKernel q) := by
  have h : Measurable (fun x : ℝ => if x = 0 then q ^ 2 / 2 else
      (Real.exp (-(q * x)) - 1 + q * x) / x ^ 2) := by
    refine Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const ?_
    exact (Continuous.measurable (by fun_prop)).div (Continuous.measurable (by fun_prop))
  exact h

private lemma aestronglyMeasurable_psiKernel (Λ : Measure I) (q : ℝ) :
    AEStronglyMeasurable (fun x : I => psiKernel q x) Λ :=
  ((measurable_psiKernel q).comp measurable_subtype_coe).aestronglyMeasurable

private lemma integrable_psiKernel (Λ : Measure I) [IsFiniteMeasure Λ] (q : ℝ) :
    Integrable (fun x : I => psiKernel q x) Λ := by
  refine (integrable_const (q ^ 2 * Real.exp |q|)).mono'
    (aestronglyMeasurable_psiKernel Λ q) (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs]
  exact psiKernel_abs_le x.2.1 x.2.2

/-! ### `ψ` -/

/-- The atom at `0` splits off as `Λ {0} q² / 2` (BBL eq. (6)). -/
theorem psi_eq (Λ : Measure I) [IsFiniteMeasure Λ] (q : ℝ) :
    psi Λ q = Λ.real {0} * (q ^ 2 / 2) +
      ∫ x in ({0}ᶜ : Set I), (exp (-(q * x)) - 1 + q * x) / (x : ℝ) ^ 2 ∂Λ := by
  unfold psi
  rw [← integral_add_compl (measurableSet_singleton (0 : I)) (integrable_psiKernel Λ q),
    integral_singleton]
  congr 1
  · simp [psiKernel]
  · refine setIntegral_congr_fun (measurableSet_singleton (0 : I)).compl (fun x hx => ?_)
    have hx' : (x : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hx
    simp only [psiKernel, hx', ite_false]

theorem psi_zero (Λ : Measure I) [IsFiniteMeasure Λ] : psi Λ 0 = 0 := by
  have h : ∀ x : ℝ, psiKernel 0 x = 0 := fun x => by
    unfold psiKernel; split_ifs <;> simp
  simp [psi, h]

theorem psi_nonneg (Λ : Measure I) [IsFiniteMeasure Λ] (q : ℝ) : 0 ≤ psi Λ q := by
  exact integral_nonneg (fun x => psiKernel_nonneg q x)

theorem continuous_psi (Λ : Measure I) [IsFiniteMeasure Λ] : Continuous (psi Λ) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  have hmain : ContinuousAt (fun q => ∫ x, psiKernel q (x : ℝ) ∂Λ) q₀ := by
    refine continuousAt_of_dominated (bound := fun _ => (|q₀| + 1) ^ 2 * Real.exp (|q₀| + 1))
      (Filter.Eventually.of_forall (fun q => aestronglyMeasurable_psiKernel Λ q)) ?_
      (integrable_const _) ?_
    · filter_upwards [Metric.ball_mem_nhds q₀ one_pos] with q hq
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      have hq' : |q| ≤ |q₀| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hq
        have := abs_sub_abs_le_abs_sub q q₀
        linarith
      calc |psiKernel q x| ≤ q ^ 2 * Real.exp |q| := psiKernel_abs_le x.2.1 x.2.2
        _ ≤ (|q₀| + 1) ^ 2 * Real.exp (|q₀| + 1) := by
          have h1 : q ^ 2 ≤ (|q₀| + 1) ^ 2 := by
            rw [← sq_abs q]; exact pow_le_pow_left₀ (abs_nonneg q) hq' 2
          have h2 : Real.exp |q| ≤ Real.exp (|q₀| + 1) := Real.exp_le_exp.mpr hq'
          exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : (x : ℝ) = 0
      · simp only [psiKernel, hx, ite_true]
        fun_prop
      · simp only [psiKernel, hx, ite_false]
        fun_prop
  exact hmain

theorem convexOn_psi (Λ : Measure I) [IsFiniteMeasure Λ] : ConvexOn ℝ univ (psi Λ) := by
  refine ⟨convex_univ, fun q₁ _ q₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold psi
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_psiKernel Λ q₁).const_mul a)
      ((integrable_psiKernel Λ q₂).const_mul b)]
  exact integral_mono (integrable_psiKernel Λ _)
    (((integrable_psiKernel Λ q₁).const_mul a).add ((integrable_psiKernel Λ q₂).const_mul b))
    (fun x => psiKernel_convex (x : ℝ) ha hb hab)

theorem monotoneOn_psi (Λ : Measure I) [IsFiniteMeasure Λ] : MonotoneOn (psi Λ) (Ici 0) := by
  intro q₁ hq₁ q₂ _ h12
  exact integral_mono (integrable_psiKernel Λ q₁) (integrable_psiKernel Λ q₂)
    (fun x => psiKernel_mono hq₁ h12 x.2.1)

/-- `ψ(q) ≤ Λ[0,1] q² / 2` for `q ≥ 0` (BBL eq. (12)). -/
theorem psi_le (Λ : Measure I) [IsFiniteMeasure Λ] {q : ℝ} (hq : 0 ≤ q) : psi Λ q ≤ Λ.real univ * (q ^ 2 / 2) := by
  calc psi Λ q ≤ ∫ _ : I, q ^ 2 / 2 ∂Λ :=
        integral_mono (integrable_psiKernel Λ q) (integrable_const _)
          (fun x => psiKernel_le hq x.2.1)
    _ = Λ.real univ * (q ^ 2 / 2) := by rw [integral_const, smul_eq_mul]

theorem psi_pos (Λ : Measure I) [IsFiniteMeasure Λ] (hΛ : Λ ≠ 0) {q : ℝ} (hq : 0 < q) : 0 < psi Λ q := by
  refine (integral_pos_iff_support_of_nonneg (f := fun x : I => psiKernel q x)
    (fun x => psiKernel_nonneg q x) (integrable_psiKernel Λ q)).mpr ?_
  refine lt_of_lt_of_le (Measure.measure_univ_pos.mpr hΛ) (measure_mono (fun x _ => ?_))
  rw [Function.mem_support]
  exact (psiKernel_pos hq.ne' x).ne'

/-! ### Grey's condition, `u` and `v` -/

private lemma continuousOn_inv_psi (Λ : Measure I) [IsFiniteMeasure Λ] (hΛ : Λ ≠ 0) :
    ContinuousOn (fun q => (psi Λ q)⁻¹) (Ioi 0) :=
  (continuous_psi Λ).continuousOn.inv₀ (fun _ hq => (psi_pos Λ hΛ hq).ne')

private lemma real_univ_pos (Λ : Measure I) [IsFiniteMeasure Λ] (hΛ : Λ ≠ 0) :
    0 < Λ.real univ := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hΛ) (measure_ne_top Λ univ)

private lemma tendsto_two_div {L : ℝ} (hL : 0 < L) :
    Tendsto (fun s : ℝ => 2 / (L * s)) (𝓝[>] 0) atTop := by
  have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
    (show (0 : ℝ) < 2 / L by positivity)
  refine h.congr (fun s => ?_)
  ring

/-- Grey's condition holds iff `Λ ≠ 0` and `1 / ψ` is integrable on `(a, ∞)` for every `a > 0`:
once for some cutoff, then for every cutoff (BBL, after eq. (4)). The clause `Λ ≠ 0` is needed on
the right: for `Λ = 0`, `1 / ψ = 0` is integrable for every cutoff, yet Grey's condition fails. -/
theorem greyCondition_iff (Λ : Measure I) [IsFiniteMeasure Λ] :
    GreyCondition Λ ↔ Λ ≠ 0 ∧ ∀ a, 0 < a → IntegrableOn (fun q => (psi Λ q)⁻¹) (Ioi a) := by
  constructor
  · rintro ⟨hΛ, a, ha, hi⟩
    refine ⟨hΛ, fun b hb => ?_⟩
    rcases le_or_gt a b with hab | hab
    · exact hi.mono_set (Ioi_subset_Ioi hab)
    · have hc : IntegrableOn (fun q => (psi Λ q)⁻¹) (Icc b a) :=
        ((continuousOn_inv_psi Λ hΛ).mono
          (fun q (hq : q ∈ Icc b a) => lt_of_lt_of_le hb hq.1)).integrableOn_Icc
      refine (hc.union hi).mono_set (fun q hq => ?_)
      rcases le_or_gt q a with h | h
      · exact Or.inl ⟨le_of_lt hq, h⟩
      · exact Or.inr h
  · rintro ⟨hΛ, h⟩
    exact ⟨hΛ, 1, one_pos, h 1 one_pos⟩

private lemma integrableOn_inv_psi (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ)
    {t : ℝ} (ht : 0 < t) : IntegrableOn (fun q => (psi Λ q)⁻¹) (Ioi t) :=
  ((greyCondition_iff Λ).1 hG).2 t ht

/-- Under Grey's condition, `u(t) ∈ (0, ∞)` for `t > 0` (BBL eq. (7)). -/
theorem psiTail_pos (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun q => (psi Λ q)⁻¹) (Ioi t) ∧ 0 < psiTail Λ t := by
  have hi := integrableOn_inv_psi Λ hG ht
  refine ⟨hi, ?_⟩
  unfold psiTail
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun q => inv_nonneg.mpr (psi_nonneg Λ q))) hi]
  have hsub : Ioi t ⊆ Function.support (fun q => (psi Λ q)⁻¹) ∩ Ioi t := fun q hq =>
    ⟨(inv_pos.mpr (psi_pos Λ hG.1 (ht.trans hq))).ne', hq⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp [Real.volume_Ioi]

private lemma psiTail_sub (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ)
    {c t : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    psiTail Λ t = psiTail Λ c - ∫ q in c..t, (psi Λ q)⁻¹ := by
  have hi := integrableOn_inv_psi Λ hG hc
  have h := setIntegral_union (μ := volume) (f := fun q => (psi Λ q)⁻¹)
    (Ioc_disjoint_Ioi_same (a := c) (b := t)) measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hct))
  rw [Ioc_union_Ioi_eq_Ioi hct] at h
  rw [intervalIntegral.integral_of_le hct]
  unfold psiTail
  rw [h]
  ring

theorem continuousOn_psiTail (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) : ContinuousOn (psiTail Λ) (Ioi 0) := by
  rw [isOpen_Ioi.continuousOn_iff]
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hc : (0 : ℝ) < t₀ / 2 := by positivity
  have hle : t₀ / 2 ≤ 2 * t₀ := by linarith
  have hsub : Icc (t₀ / 2) (2 * t₀) ⊆ Ioi 0 := fun q hq => lt_of_lt_of_le hc hq.1
  have hint : IntegrableOn (fun q => (psi Λ q)⁻¹) (uIcc (t₀ / 2) (2 * t₀)) := by
    rw [uIcc_of_le hle]
    exact ((continuousOn_inv_psi Λ hG.1).mono hsub).integrableOn_Icc
  have hcont : ContinuousOn (fun t => psiTail Λ (t₀ / 2) - ∫ q in (t₀ / 2)..t, (psi Λ q)⁻¹)
      (uIcc (t₀ / 2) (2 * t₀)) :=
    continuousOn_const.sub (intervalIntegral.continuousOn_primitive_interval hint)
  have hmem : uIcc (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ := by
    rw [uIcc_of_le hle]
    exact Icc_mem_nhds (by linarith) (by linarith)
  refine (hcont.continuousAt hmem).congr ?_
  filter_upwards [Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)] with t ht
  exact (psiTail_sub Λ hG hc (le_of_lt ht)).symm

theorem strictAntiOn_psiTail (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) : StrictAntiOn (psiTail Λ) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  rw [psiTail_sub Λ hG hs' hst.le]
  have hpos : 0 < ∫ q in s..t, (psi Λ q)⁻¹ := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun q hq => ?_) hst
    · refine ContinuousOn.intervalIntegrable ((continuousOn_inv_psi Λ hG.1).mono ?_)
      rw [uIcc_of_le hst.le]
      exact fun q hq => lt_of_lt_of_le hs' hq.1
    · exact inv_pos.mpr (psi_pos Λ hG.1 (hs'.trans hq.1))
  linarith

theorem tendsto_psiTail_atTop (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) :
    Tendsto (psiTail Λ) atTop (𝓝 0) := by
  have hi := integrableOn_inv_psi Λ hG one_pos
  have h := intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_id
  have h2 : Tendsto (fun t => psiTail Λ 1 - ∫ q in (1 : ℝ)..t, (psi Λ q)⁻¹) atTop
      (𝓝 (psiTail Λ 1 - psiTail Λ 1)) := tendsto_const_nhds.sub h
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact (psiTail_sub Λ hG one_pos ht).symm

private lemma two_div_le_psiTail_aux (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ)
    {s : ℝ} (hs : 0 < s) : 2 / (Λ.real univ * s) ≤ psiTail Λ s := by
  have hL := real_univ_pos Λ hG.1
  have hi := integrableOn_inv_psi Λ hG hs
  have hr : IntegrableOn (fun q : ℝ => 2 / Λ.real univ * q ^ (-2 : ℝ)) (Ioi s) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) hs) _
  have hval : ∫ q in Ioi s, 2 / Λ.real univ * q ^ (-2 : ℝ) = 2 / (Λ.real univ * s) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hs]
    have e : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [e, Real.rpow_neg_one]
    ring
  rw [← hval]
  unfold psiTail
  refine setIntegral_mono_on hr hi measurableSet_Ioi (fun q hq => ?_)
  have hq : (0 : ℝ) < q := hs.trans hq
  have hpsi := psi_pos Λ hG.1 hq
  have hle := psi_le Λ hq.le
  rw [Real.rpow_neg hq.le, Real.rpow_two]
  calc 2 / Λ.real univ * (q ^ 2)⁻¹ = (Λ.real univ * (q ^ 2 / 2))⁻¹ := by ring
    _ ≤ (psi Λ q)⁻¹ := inv_anti₀ hpsi hle

theorem tendsto_psiTail_zero (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) :
    Tendsto (psiTail Λ) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_two_div (real_univ_pos Λ hG.1))
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact two_div_le_psiTail_aux Λ hG hs

private lemma speed_eq (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) : speed Λ (psiTail Λ s₀) = s₀ := by
  have hset : {s | 0 < s ∧ psiTail Λ s < psiTail Λ s₀} = Ioi s₀ := by
    ext s
    refine ⟨fun ⟨hs, hlt⟩ => ?_, fun h => ?_⟩
    · by_contra hle
      have := (strictAntiOn_psiTail Λ hG).antitoneOn hs hs₀ (not_lt.mp hle)
      linarith
    · exact ⟨hs₀.trans h, strictAntiOn_psiTail Λ hG hs₀ (hs₀.trans h) h⟩
  rw [speed, hset, csInf_Ioi]

private lemma exists_psiTail_eq (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ)
    {t : ℝ} (ht : 0 < t) : ∃ s₀, 0 < s₀ ∧ psiTail Λ s₀ = t := by
  obtain ⟨a, hat, ha⟩ :=
    (((tendsto_psiTail_zero Λ hG).eventually (eventually_gt_atTop t)).and
      self_mem_nhdsWithin).exists
  obtain ⟨b, hbt, hab⟩ :=
    (((tendsto_psiTail_atTop Λ hG).eventually (eventually_lt_nhds ht)).and
      (eventually_gt_atTop a)).exists
  have ha' : (0 : ℝ) < a := ha
  have hcont : ContinuousOn (psiTail Λ) (Icc a b) :=
    (continuousOn_psiTail Λ hG).mono (fun q hq => lt_of_lt_of_le ha' hq.1)
  obtain ⟨s₀, hs₀, hs₀t⟩ := intermediate_value_Icc' hab.le hcont ⟨hbt.le, hat.le⟩
  exact ⟨s₀, lt_of_lt_of_le ha' hs₀.1, hs₀t⟩

/-- Under Grey's condition `v` inverts `u`: for `t > 0`, `v t > 0` and `u (v t) = t`. -/
theorem psiTail_speed (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {t : ℝ} (ht : 0 < t) :
    0 < speed Λ t ∧ psiTail Λ (speed Λ t) = t := by
  obtain ⟨s₀, hs₀, rfl⟩ := exists_psiTail_eq Λ hG ht
  rw [speed_eq Λ hG hs₀]
  exact ⟨hs₀, rfl⟩

theorem speed_psiTail (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {s : ℝ} (hs : 0 < s) :
    speed Λ (psiTail Λ s) = s := by
  exact speed_eq Λ hG hs

theorem strictAntiOn_speed (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) : StrictAntiOn (speed Λ) (Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ h12
  obtain ⟨hp₁, he₁⟩ := psiTail_speed Λ hG ht₁
  obtain ⟨hp₂, he₂⟩ := psiTail_speed Λ hG ht₂
  by_contra hle
  have := (strictAntiOn_psiTail Λ hG).antitoneOn hp₁ hp₂ (not_lt.mp hle)
  rw [he₁, he₂] at this
  linarith

private lemma two_div_le_speed_aux (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ)
    {t : ℝ} (ht : 0 < t) : 2 / (Λ.real univ * t) ≤ speed Λ t := by
  obtain ⟨hp, he⟩ := psiTail_speed Λ hG ht
  have h := two_div_le_psiTail_aux Λ hG hp
  rw [he] at h
  have hL := real_univ_pos Λ hG.1
  rw [div_le_iff₀ (mul_pos hL hp)] at h
  rw [div_le_iff₀ (mul_pos hL ht)]
  nlinarith

/-- Under Grey's condition, `v(t) → ∞` as `t → 0+`. -/
theorem tendsto_speed_zero (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) :
    Tendsto (speed Λ) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_two_div (real_univ_pos Λ hG.1))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact two_div_le_speed_aux Λ hG ht

theorem tendsto_speed_atTop (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) :
    Tendsto (speed Λ) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact lt_trans ha (psiTail_speed Λ hG ht).1
  · have hua := (psiTail_pos Λ hG ha).2
    filter_upwards [eventually_gt_atTop (psiTail Λ a)] with t ht
    have h := strictAntiOn_speed Λ hG hua (hua.trans ht) ht
    rwa [speed_psiTail Λ hG ha] at h

/-- Kingman is extremal: under Grey's condition, `u(s) ≥ 2 / (Λ[0,1] s)` for `s > 0`
(BBL eq. (13)); `two_div_le_speed` gives `v(t) ≥ 2 / (Λ[0,1] t)`. -/
theorem two_div_le_psiTail (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {s : ℝ} (hs : 0 < s) :
    2 / (Λ.real univ * s) ≤ psiTail Λ s := by
  exact two_div_le_psiTail_aux Λ hG hs

theorem two_div_le_speed (Λ : Measure I) [IsFiniteMeasure Λ] (hG : GreyCondition Λ) {t : ℝ} (ht : 0 < t) :
    2 / (Λ.real univ * t) ≤ speed Λ t := by
  exact two_div_le_speed_aux Λ hG ht

/-! ### Kingman's coalescent `Λ = δ₀` -/

private lemma inv_half_sq_eq {q : ℝ} (hq : 0 < q) : (q ^ 2 / 2)⁻¹ = 2 * q ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hq.le, Real.rpow_two]
  ring

theorem psi_dirac_zero (q : ℝ) : psi (Measure.dirac (0 : I)) q = q ^ 2 / 2 := by
  unfold psi
  rw [integral_dirac]
  simp [psiKernel]

theorem psi_dirac_zero_two : psi (Measure.dirac (0 : I)) 2 = 2 := by
  rw [psi_dirac_zero]
  norm_num

theorem greyCondition_dirac_zero : GreyCondition (Measure.dirac (0 : I)) := by
  refine ⟨Measure.dirac_ne_zero, 1, one_pos, ?_⟩
  have h : IntegrableOn (fun q : ℝ => 2 * q ^ (-2 : ℝ)) (Ioi 1) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
  refine h.congr_fun (fun q hq => ?_) measurableSet_Ioi
  simp only [psi_dirac_zero]
  exact (inv_half_sq_eq (lt_trans one_pos hq)).symm

theorem psiTail_dirac_zero {t : ℝ} (ht : 0 < t) : psiTail (Measure.dirac (0 : I)) t = 2 / t := by
  unfold psiTail
  have heq : EqOn (fun q => (psi (Measure.dirac (0 : I)) q)⁻¹) (fun q => 2 * q ^ (-2 : ℝ))
      (Ioi t) := fun q hq => by
    simp only [psi_dirac_zero]
    exact inv_half_sq_eq (lt_trans ht hq)
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) ht]
  have e : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [e, Real.rpow_neg_one]
  ring

theorem speed_dirac_zero {t : ℝ} (ht : 0 < t) : speed (Measure.dirac (0 : I)) t = 2 / t := by
  have h2t : (0 : ℝ) < 2 / t := by positivity
  have h := speed_eq (Measure.dirac (0 : I)) greyCondition_dirac_zero h2t
  have e : 2 / (2 / t) = t := by field_simp
  rwa [psiTail_dirac_zero h2t, e] at h

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
