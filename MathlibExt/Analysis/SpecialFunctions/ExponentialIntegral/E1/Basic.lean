/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.E1

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The DLMF `E1` two-term remainder bound

This development proves the outer-sector remainder estimate used by the
square-root-two omega theorem. The definitions of `Ein`, principal `E1`, its
asymptotic terms, partial sums, and remainders are imported from the preceding
exponential-integral modules.
-/

@[expose] public section

namespace Complex

noncomputable section

/-- **Two-term expansion of $1/(t + z)$.** Let $z \ne 0$ be a complex number and $t$ a real
number with $t + z \ne 0$. Then
$\frac{1}{t + z} = \frac{1}{z} - \frac{t}{z^2} + \frac{t^2}{z^2 (t + z)}$. -/
lemma two_term_kernel_identity (z : ℂ) (t : ℝ) (hz : z ≠ 0)
    (htz : (t : ℂ) + z ≠ 0) :
    1 / ((t : ℂ) + z) =
      1 / z - (t : ℂ) / z ^ 2 + (t : ℂ) ^ 2 / (z ^ 2 * ((t : ℂ) + z)) := by
  field_simp
  ring

/-- **Integrability of $e^{-t} t^n$ on $(0, \infty)$.** For every natural number $n$, the
function $t \mapsto e^{-t} t^n$ is Lebesgue integrable on the open interval $(0, \infty)$. -/
theorem integrableOn_exp_neg_mul_pow (n : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) := by
  simpa using
    (Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity))

/-- **The moments of $e^{-t}$ are factorials.** For every natural number $n$, the integral of
$e^{-t} t^n$ over the open interval $(0, \infty)$ equals $n!$. -/
theorem integral_exp_neg_mul_pow_Ioi (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ n = (n.factorial : ℝ) := by
  calc
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ n = Real.Gamma ((n : ℝ) + 1) := by
      simpa using
        (Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)).symm
    _ = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n

/-- **Positivity of $\sin |\arg z|$ in the outer sector.** Let $z \ne 0$ be a complex number with
$\pi/2 \le |\arg z| < \pi$, where $\arg z \in (-\pi, \pi]$ is the principal argument. Then
$\sin |\arg z| > 0$. -/
lemma outer_sector_sin_abs_arg_pos
    (z : ℂ) (_hz : z ≠ 0) (hargLower : Real.pi / 2 ≤ |z.arg|)
    (hargUpper : |z.arg| < Real.pi) :
    0 < Real.sin |z.arg| := by
  exact Real.sin_pos_of_pos_of_lt_pi
    (Real.pi_div_two_pos.trans_le hargLower) hargUpper

/-- **Lower bound for $|t + z|$ in the outer sector.** Let $z \ne 0$ be a complex number with
$\pi/2 \le |\arg z| < \pi$, where $\arg z \in (-\pi, \pi]$ is the principal argument, and let
$t \ge 0$ be a real number. Then $|z| \sin |\arg z| \le |t + z|$. -/
lemma outer_sector_distance
    (z : ℂ) (t : ℝ) (_hz : z ≠ 0) (_ht : 0 ≤ t)
    (_hargLower : Real.pi / 2 ≤ |z.arg|)
    (_hargUpper : |z.arg| < Real.pi) :
    ‖z‖ * Real.sin |z.arg| ≤ ‖(t : ℂ) + z‖ := by
  calc
    ‖z‖ * Real.sin |z.arg| = |‖z‖ * Real.sin z.arg| := by
      rw [abs_mul, abs_norm,
        Real.abs_sin_eq_sin_abs_of_abs_le_pi (Complex.abs_arg_le_pi z)]
    _ = |z.im| := by rw [Complex.norm_mul_sin_arg]
    _ = |((t : ℂ) + z).im| := by simp
    _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _

/-- **Outer-sector bound for the quadratic integral remainder.** Let $z \ne 0$ be a complex number
with $\pi/2 \le |\arg z| < \pi$, where $\arg z \in (-\pi, \pi]$ is the principal argument, and
let $T_2(z) = \frac{e^{-z}}{z} \cdot \frac{(-1)^2 \, 2!}{z^2}$ be the $n = 2$ term of the
asymptotic expansion of $E_1$. Then
$$\left| \frac{e^{-z}}{z^2} \int_0^\infty \frac{e^{-t} t^2}{t + z} \, dt \right| \le
\frac{|T_2(z)|}{\sin |\arg z|},$$
where the integral is taken over the open interval $(0, \infty)$. -/
theorem integral_remainder_bound
    (z : ℂ) (hz : z ≠ 0) (hargLower : Real.pi / 2 ≤ |z.arg|)
    (hargUpper : |z.arg| < Real.pi) :
    ‖Complex.exp (-z) / z^2 *
        ∫ t : ℝ in Set.Ioi 0,
          (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖
      ≤ (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
  have hs : 0 < Real.sin |z.arg| :=
    outer_sector_sin_abs_arg_pos z hz hargLower hargUpper
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < ‖z‖ * Real.sin |z.arg| := mul_pos hzn hs
  have hg : MeasureTheory.IntegrableOn
      (fun t : ℝ => (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2))
      (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul_pow 2).const_mul _
  have hInt :
      ∫ t : ℝ in Set.Ioi 0,
          ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖
        ≤ ∫ t : ℝ in Set.Ioi 0,
          (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hdist : ‖z‖ * Real.sin |z.arg| ≤ ‖(t : ℂ) + z‖ :=
      outer_sector_distance z t hz ht0 hargLower hargUpper
    calc
      ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ =
          (Real.exp (-t) * t ^ 2) / ‖(t : ℂ) + z‖ := by
            simp [norm_pow, Complex.norm_real,
              Real.norm_eq_abs, Complex.norm_exp,
              abs_of_nonneg ht0]
      _ ≤ (Real.exp (-t) * t ^ 2) / (‖z‖ * Real.sin |z.arg|) := by
        exact div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (sq_nonneg t))
          hd hdist
      _ = (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2) := by
        rw [div_eq_inv_mul]
  calc
    ‖Complex.exp (-z) / z^2 *
        ∫ t : ℝ in Set.Ioi 0,
          (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ =
        ‖Complex.exp (-z) / z^2‖ *
          ‖∫ t : ℝ in Set.Ioi 0,
            (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖ := by
      rw [norm_mul]
    _ ≤ ‖Complex.exp (-z) / z^2‖ *
          (∫ t : ℝ in Set.Ioi 0,
            ‖(Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖) := by
      exact mul_le_mul_of_nonneg_left
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
          (fun t : ℝ =>
            (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)))
        (norm_nonneg _)
    _ ≤ ‖Complex.exp (-z) / z^2‖ *
          (∫ t : ℝ in Set.Ioi 0,
            (‖z‖ * Real.sin |z.arg|)⁻¹ * (Real.exp (-t) * t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hInt (norm_nonneg _)
    _ = (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_pow_Ioi]
      simp [e1AsymptoticTerm, e1AsymptoticTermRaw, norm_pow, Complex.norm_exp,
        Nat.factorial]
      field_simp

end

end Complex
