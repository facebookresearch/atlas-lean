/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathlibExt.Analysis.Ramanujan.Part1Ch8Entry8Digammaseries

/-!
# Digamma evaluation of a hyperbolic Laplace integral

`watson_cosh_integral_digamma` evaluates the integral by expanding each of two decaying
exponentials against a geometric series and applying the alternating digamma series.
-/

namespace MetaMathlibExt

open Filter MeasureTheory Set
open scoped Topology

namespace watson_cosh_integral_digamma

open MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

private noncomputable def kernel (z : ℂ) (c x : ℝ) : ℂ :=
  Complex.exp (-z * x) / ((1 + Real.exp (-c * x) : ℝ) : ℂ)

private lemma integrable_kernel {z : ℂ} (hz : 0 < z.re) (c : ℝ) :
    IntegrableOn (kernel z c) (Ioi 0) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
  apply Integrable.mono h
  · apply Continuous.aestronglyMeasurable
    unfold kernel
    exact (by fun_prop : Continuous (fun x : ℝ ↦ Complex.exp (-z * x))).div
      (by fun_prop) (fun x ↦ Complex.ofReal_ne_zero.mpr (by positivity))
  · filter_upwards with x
    rw [kernel, norm_div, Complex.norm_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.exp_pos (-c * x)])

/-- Integrate the finite geometric sums, then pass to their limit on the open half-line. -/
private lemma integral_kernel {z : ℂ} {c : ℝ} (hz : 0 < z.re) (hc : 0 < c) :
    (∫ x in Ioi 0, kernel z c x) =
      (Complex.digamma ((z + c) / (2 * c)) - Complex.digamma (z / (2 * c))) / (2 * c) := by
  let rate (j : ℕ) : ℂ := z + (c : ℂ) * j
  have hrate (j : ℕ) : 0 < (rate j).re := by
    simpa [rate] using add_pos_of_pos_of_nonneg hz (mul_nonneg hc.le (Nat.cast_nonneg j))
  let term (j : ℕ) (x : ℝ) := (-1 : ℂ) ^ j * Complex.exp (-rate j * x)
  have hint (j : ℕ) : IntegrableOn (term j) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -rate j) (by simpa using hrate j) 0).const_mul _
  let q (x : ℝ) : ℂ := -(Real.exp (-c * x) : ℂ)
  have hgeom (n : ℕ) (x : ℝ) :
      ∑ j ∈ Finset.range n, term j x = kernel z c x * (1 - q x ^ n) := by
    have hterm (j : ℕ) : term j x = Complex.exp (-z * x) * q x ^ j := by
      have e : -rate j * x = -z * x + j * ((-c * x : ℝ) : ℂ) := by
        simp only [rate, Complex.ofReal_mul, Complex.ofReal_neg]
        ring
      dsimp only [term]
      rw [e, Complex.exp_add, Complex.exp_nat_mul, ← Complex.ofReal_exp]
      dsimp only [q]
      rw [← neg_one_mul (Real.exp _ : ℂ), mul_pow]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← geom_sum_mul_neg]
    have hden : ((1 + Real.exp (-c * x) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    have heq : 1 - q x = ((1 + Real.exp (-c * x) : ℝ) : ℂ) := by simp [q]
    rw [heq, kernel, mul_comm (∑ j ∈ Finset.range n, q x ^ j), ← mul_assoc,
      div_mul_cancel₀ _ hden]
  have hq {x : ℝ} (hx : 0 < x) : ‖q x‖ < 1 := by
    dsimp only [q]
    rw [norm_neg, Complex.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc) hx
  have hlim : Tendsto (fun n ↦ ∫ x in Ioi 0, ∑ j ∈ Finset.range n, term j x)
      atTop (𝓝 (∫ x in Ioi 0, kernel z c x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖kernel z c x‖ * 2)
      (fun n ↦ (integrable_finsetSum _ fun j _ ↦ hint j).aestronglyMeasurable)
      ((integrable_kernel hz c).norm.mul_const 2)
    · intro n
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      rw [hgeom, norm_mul]
      gcongr
      calc ‖1 - q x ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖q x ^ n‖ := norm_sub_le _ _
        _ ≤ 2 := by
          rw [norm_one, norm_pow]
          linarith [pow_le_one₀ (norm_nonneg _) (hq hx).le (n := n)]
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      simp_rw [hgeom]
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hq hx)).const_sub 1
        |>.const_mul (kernel z c x)
  have den (j : ℕ) : z - c + c * ((j + 1 : ℕ) : ℂ) = rate j := by
    simp only [rate, Nat.cast_add_one]
    ring
  have hseries := ramanujan_part1_ch8_entry8_digammaseries_complex_digamma (z - c) c
    (Complex.ofReal_ne_zero.mpr hc.ne') (fun j ↦ by
      rw [den]
      exact fun h ↦ (hrate j).ne' (by simp [h]))
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hseries
  have heval (n : ℕ) : (∫ x in Ioi 0, ∑ j ∈ Finset.range n, term j x) =
      ∑ j ∈ Finset.range n, chapter8Entry8Term (z - c) c j := by
    rw [integral_finsetSum _ fun j _ ↦ hint j]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [term]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using hrate j)]
    rw [chapter8Entry8Term, den]
    simp [div_eq_mul_inv]
  simp_rw [heval] at hlim
  rw [show z - c + 2 * (c : ℂ) = z + c by ring, sub_add_cancel] at hseries
  exact tendsto_nhds_unique hlim hseries

private lemma cosh_split (b : ℝ) (α β : ℂ) (x : ℝ) :
    Complex.exp (-α * x) * Complex.cosh (β * x) / Complex.cosh ((b : ℂ) * x) =
      kernel (α + b - β) (2 * b) x + kernel (α + b + β) (2 * b) x := by
  rw [Complex.cosh, Complex.cosh, ← mul_div_assoc, div_div_div_cancel_right₀ two_ne_zero,
    kernel, kernel, ← add_div]
  conv_lhs => rw [← mul_div_mul_left _ _ (Complex.exp_ne_zero (-((b : ℂ) * x)))]
  congr 1
  · rw [← mul_assoc, mul_add]
    simp only [← Complex.exp_add]
    congr 1 <;> congr 1 <;> ring
  · push_cast
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero]
    congr 2
    ring

end watson_cosh_integral_digamma

open watson_cosh_integral_digamma

/--
**Digamma evaluation of a hyperbolic Laplace integral.** Let $b > 0$ be a real number and let
$\alpha, \beta$ be complex numbers with $\operatorname{Re}(\alpha + b - \beta) > 0$ and
$\operatorname{Re}(\alpha + b + \beta) > 0$. Then the function
$x \mapsto e^{-\alpha x} \cosh(\beta x) / \cosh(bx)$ is integrable on $(0, \infty)$, and, writing
$\psi$ for the digamma function,
$$
\int_0^\infty \frac{e^{-\alpha x} \cosh(\beta x)}{\cosh(bx)} \, dx =
\frac{1}{4b} \Bigl[ \psi\bigl(\tfrac34 + \tfrac{\alpha+\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha-\beta}{4b}\bigr) +
\psi\bigl(\tfrac34 + \tfrac{\alpha-\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha+\beta}{4b}\bigr) \Bigr].
$$

The source prints only the condition $\operatorname{Re}(\alpha + b - \beta) > 0$; the condition
$\operatorname{Re}(\alpha + b + \beta) > 0$ is also needed, since the integrand is even in $\beta$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Lemma 1.
-/
public theorem watson_cosh_integral_digamma
    (b : ℝ) (α β : ℂ) (hb : 0 < b)
    (hminus : 0 < (α + (b : ℂ) - β).re)
    (hplus : 0 < (α + (b : ℂ) + β).re) :
    IntegrableOn
        (fun x : ℝ =>
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ)))
        (Set.Ioi 0) ∧
      (∫ (x : ℝ) in Set.Ioi 0,
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ))) =
        (1 / (4 * (b : ℂ))) *
          (Complex.digamma ((3 / 4 : ℂ) + (α + β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) +
            Complex.digamma ((3 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α + β) / (4 * (b : ℂ)))) := by
  simp_rw [cosh_split]
  have hm := integrable_kernel hminus (2 * b)
  have hp := integrable_kernel hplus (2 * b)
  refine ⟨hm.add hp, ?_⟩
  rw [integral_add hm hp, integral_kernel hminus (by positivity),
    integral_kernel hplus (by positivity)]
  push_cast
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have low (w : ℂ) : (w + b) / (2 * (2 * b : ℂ)) = 1 / 4 + w / (4 * b) := by
    field_simp
    ring
  have high (w : ℂ) : (w + b + 2 * b) / (2 * (2 * b : ℂ)) = 3 / 4 + w / (4 * b) := by
    field_simp
    ring
  rw [show α + b - β = (α - β) + b by ring, show α + b + β = (α + β) + b by ring,
    high, high, low, low]
  ring

end MetaMathlibExt
