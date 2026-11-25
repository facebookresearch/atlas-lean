/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth parameter dependence of Gaussian moments

For bounded measurable real data, the moments of `exp (-a*y² + b*y)` depend
smoothly on both parameters on `a > 0`. Differentiating in `a` raises the moment
order by two and changes the sign; differentiating in `b` raises it by one.
Uniform polynomial-Gaussian bounds justify differentiation under the integral
and induction gives every finite order, without derivatives of the datum.

This is the Gaussian domination argument used in the heat-kernel smoothness proof
in M. Schmidt, *Partial Differential Equations*, HWS 2025, Chapter 4, Theorem 4.3:
https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ContDiff

namespace MathlibExt.Analysis.GaussianMoments

/-- The `n`th Gaussian moment of a datum, with parameter pair `p = (a, b)`.
The integral results below require `a > 0` and bounded measurable data. -/
noncomputable def gaussianMoment (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∫ y, y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y

private noncomputable def integrand (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (y : ℝ) : ℝ :=
  y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y

private theorem exp_bound {a R : ℝ} (ha : 0 < a) {p : ℝ × ℝ}
    (hap : a ≤ p.1) (hp : |p.2| ≤ R) (y : ℝ) :
    exp (-p.1 * y ^ 2 + p.2 * y) ≤
      exp (R ^ 2 / (2 * a)) * exp (-(a / 2) * y ^ 2) := by
  have hby : p.2 * y ≤ R * |y| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right hp (abs_nonneg y)))
  have hy : R * |y| ≤ a / 2 * y ^ 2 + R ^ 2 / (2 * a) := by
    calc
      _ ≤ (a ^ 2 * y ^ 2 + R ^ 2) / (2 * a) := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (a * |y| - R), sq_abs y]
      _ = _ := by field_simp
  rw [← exp_add]
  apply exp_le_exp.mpr
  have ht := mul_le_mul_of_nonneg_right hap (sq_nonneg y)
  nlinarith

private theorem integrand_measurable {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (n : ℕ) (p : ℝ × ℝ) : AEStronglyMeasurable (integrand f n p) := by
  have hc : Continuous (fun y : ℝ => y ^ n * exp (-p.1 * y ^ 2 + p.2 * y)) := by
    fun_prop
  exact hc.aestronglyMeasurable.mul hf

private theorem exists_integrable_bound {f : ℝ → ℝ} (hb : ∃ M, ∀ y, |f y| ≤ M)
    {a R : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ p : ℝ × ℝ, a ≤ p.1 → |p.2| ≤ R →
      ∀ y, ‖integrand f n p y‖ ≤ B y := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  let B : ℝ → ℝ := fun y => (|y| ^ n * exp (-(a / 2) * y ^ 2)) *
    (exp (R ^ 2 / (2 * a)) * M)
  refine ⟨B, ?_, ?_⟩
  · have hi := (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < a / 2)
        (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1 : ℝ) < (n : ℝ))).norm
    simp only [rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (exp_pos _)] at hi
    exact hi.mul_const _
  · intro p hap hp y
    simp only [integrand, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (exp_pos _)]
    calc
      _ ≤ (|y| ^ n * (exp (R ^ 2 / (2 * a)) * exp (-(a / 2) * y ^ 2))) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left (exp_bound ha hap hp y)
          (pow_nonneg (abs_nonneg y) _)) (hM y) (abs_nonneg _) (by positivity)
      _ = B y := by dsimp [B]; ring

/-- Every polynomial Gaussian moment is integrable for bounded measurable data. -/
theorem integrable_gaussianMoment {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ y, |f y| ≤ M) (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    Integrable (fun y => y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y) := by
  obtain ⟨B, hB, h⟩ := exists_integrable_bound hb (R := |p.2|) hp n
  exact hB.mono' (integrand_measurable hf n p) (ae_of_all _ (h p le_rfl le_rfl))

private noncomputable def integrandFDeriv (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ)
    (y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-integrand f (n + 2) p y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    integrand f (n + 1) p y • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem integrand_hasFDerivAt (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (y : ℝ) :
    HasFDerivAt (fun q => integrand f n q y) (integrandFDeriv f n p y) p := by
  have he : HasFDerivAt (fun q : ℝ × ℝ => -q.1 * y ^ 2 + q.2 * y)
      ((-(y ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        y • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    let L : (ℝ × ℝ) →L[ℝ] ℝ := (-(y ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      y • ContinuousLinearMap.snd ℝ ℝ ℝ
    have hl : (fun q : ℝ × ℝ => -q.1 * y ^ 2 + q.2 * y) = L := by
      funext q
      simp [L]
      ring
    rw [hl]
    exact L.hasFDerivAt
  have hd : HasFDerivAt (fun q => integrand f n q y)
      (f y • (y ^ n • (exp (-p.1 * y ^ 2 + p.2 * y) •
        ((-(y ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          y • ContinuousLinearMap.snd ℝ ℝ ℝ)))) p := by
    simpa only [integrand] using! (he.exp.const_mul (y ^ n)).mul_const (f y)
  have heq : integrandFDeriv f n p y =
      f y • (y ^ n • (exp (-p.1 * y ^ 2 + p.2 * y) •
        ((-(y ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          y • ContinuousLinearMap.snd ℝ ℝ ℝ))) := by
    apply ContinuousLinearMap.ext
    intro q
    simp [integrandFDeriv, integrand, pow_add]
    ring
  rw [heq]
  exact hd

private theorem norm_integrandFDeriv_le (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (y : ℝ) :
    ‖integrandFDeriv f n p y‖ ≤
      ‖integrand f (n + 2) p y‖ + ‖integrand f (n + 1) p y‖ := by
  simpa only [integrandFDeriv, norm_smul, norm_neg, ContinuousLinearMap.norm_fst,
    ContinuousLinearMap.norm_snd, mul_one] using
      norm_add_le ((-integrand f (n + 2) p y) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (integrand f (n + 1) p y • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The joint derivative raises the moment order by two in the decay parameter
(with a minus sign), and by one in the linear parameter. -/
theorem gaussianMoment_hasFDerivAt {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ y, |f y| ≤ M) (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    HasFDerivAt (gaussianMoment f n)
      ((-gaussianMoment f (n + 2) p) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        gaussianMoment f (n + 1) p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  obtain ⟨B₂, hi₂, hB₂⟩ := exists_integrable_bound hb
    (R := |p.2| + 1) (by positivity : 0 < p.1 / 2) (n + 2)
  obtain ⟨B₁, hi₁, hB₁⟩ := exists_integrable_bound hb
    (R := |p.2| + 1) (by positivity : 0 < p.1 / 2) (n + 1)
  let s : Set (ℝ × ℝ) := {q | p.1 / 2 < q.1 ∧ |q.2| < |p.2| + 1}
  have hs : s ∈ 𝓝 p := by
    have ho : IsOpen s := (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_snd.abs continuous_const)
    apply ho.mem_nhds
    change p.1 / 2 < p.1 ∧ |p.2| < |p.2| + 1
    constructor <;> linarith
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q y => integrand f n q y) (F' := integrandFDeriv f n)
    (bound := fun y => B₂ y + B₁ y) hs
    (Eventually.of_forall (integrand_measurable hf n))
    (integrable_gaussianMoment hf hb n hp) ?_ ?_ (hi₂.add hi₁) ?_
  · have h₂ : Integrable (fun y => (-integrand f (n + 2) p y) •
        ContinuousLinearMap.fst ℝ ℝ ℝ) :=
      (integrable_gaussianMoment hf hb (n + 2) hp).neg.smul_const _
    have h₁ : Integrable (fun y => integrand f (n + 1) p y •
        ContinuousLinearMap.snd ℝ ℝ ℝ) :=
      (integrable_gaussianMoment hf hb (n + 1) hp).smul_const _
    simp only [integrandFDeriv] at hd
    rw [integral_add h₂ h₁, integral_smul_const, integral_smul_const, integral_neg] at hd
    exact hd
  · exact ((integrand_measurable hf (n + 2) p).neg.smul_const
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
        ((integrand_measurable hf (n + 1) p).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  · filter_upwards with y q hq
    exact (norm_integrandFDeriv_le f n q y).trans
      (add_le_add (hB₂ q hq.1.le hq.2.le y) (hB₁ q hq.1.le hq.2.le y))
  · filter_upwards with y q _
    exact integrand_hasFDerivAt f n q y

/-- Gaussian moments of bounded measurable data are jointly smooth in the decay
and linear parameters wherever the decay parameter is positive. -/
theorem gaussianMoment_contDiffOn {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hb : ∃ M, ∀ y, |f y| ≤ M) (n : ℕ) :
    ContDiffOn ℝ ∞ (gaussianMoment f n) (Ioi 0 ×ˢ univ) := by
  have hd (m : ℕ) : DifferentiableOn ℝ (gaussianMoment f m) (Ioi 0 ×ˢ univ) :=
    fun p hp => (gaussianMoment_hasFDerivAt hf hb m hp.1).differentiableAt.differentiableWithinAt
  have hk (k : ℕ) : ∀ m, ContDiffOn ℝ k (gaussianMoment f m) (Ioi 0 ×ˢ univ) := by
    induction k with
    | zero => intro m; exact contDiffOn_zero.mpr (hd m).continuousOn
    | succ k ih =>
      intro m
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ)]
      refine ⟨hd m, by simp, ?_⟩
      have hc : ContDiffOn ℝ (k : ℕ∞ω) (fun p =>
          (-gaussianMoment f (m + 2) p) • ContinuousLinearMap.fst ℝ ℝ ℝ +
            gaussianMoment f (m + 1) p • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ioi 0 ×ˢ univ) :=
        ((ih (m + 2)).neg.smul contDiffOn_const).add ((ih (m + 1)).smul contDiffOn_const)
      exact hc.congr (fun p hp => (gaussianMoment_hasFDerivAt hf hb m hp.1).fderiv)
  exact contDiffOn_infty.mpr (fun k => hk k n)

end MathlibExt.Analysis.GaussianMoments
