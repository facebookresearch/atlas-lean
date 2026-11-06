/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.TaylorExpansion

@[expose] public section

namespace Complex

noncomputable section

/-- **Radial majorant.** For a function $f : \mathbb{C} \to \mathbb{C}$ with Taylor coefficients
$a_n = f^{(n)}(0) / n!$ at the origin and a real number $r$, the radial majorant of $f$ at $r$ is
$M_f(r) = \sum_{n \ge 0} |a_n| \, |r|^n$, the sum of the radial Taylor terms at radius $|r|$.
By convention $M_f(r) = 0$ when this series diverges. -/
def wimanMajorant (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∑' n, wimanTerm f r n

/-- **Radial Taylor terms are nonnegative.** For every function $f : \mathbb{C} \to \mathbb{C}$
with Taylor coefficients $a_n = f^{(n)}(0) / n!$ at the origin, every real $r$ and every
$n \in \mathbb{N}$, we have $0 \le |a_n| \, |r|^n$. -/
theorem wimanTerm_nonneg (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    0 ≤ wimanTerm f r n := by
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg r) _)

/-- **Summability of the radial Taylor terms.** Let $f$ be an entire function with Taylor
coefficients $a_n = f^{(n)}(0) / n!$ at the origin. For every real $r$, the series
$\sum_{n \ge 0} |a_n| \, |r|^n$ converges. -/
theorem summable_wimanTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℝ) :
    Summable (wimanTerm f r) := by
  let p := cauchyPowerSeries f 0 (1 : NNReal)
  have hp : HasFPowerSeriesOnBall f p 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) zero_lt_one
  have hp_radius : p.radius = ⊤ := le_antisymm le_top hp.r_le
  have hs : Summable (fun n : ℕ => ‖p n (fun _ => ((|r| : ℝ) : ℂ))‖) :=
    p.summable_norm_apply (by simp [hp_radius])
  apply hs.congr
  intro n
  have hfactorial := hp.factorial_smul ((|r| : ℝ) : ℂ) n
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hfactorial
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_fin, smul_eq_mul] at hfactorial
  have hcoeff : p n (fun _ => ((|r| : ℝ) : ℂ)) =
      wimanTaylorCoefficient f n * ((|r| : ℝ) : ℂ) ^ n := by
    rw [wimanTaylorCoefficient, div_mul_eq_mul_div,
      eq_div_iff (mod_cast n.factorial_ne_zero)]
    simpa only [mul_comm] using hfactorial
  rw [hcoeff, wimanTerm, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_abs]

/-- The normalized radial majorant is nonnegative. -/
theorem wimanMajorant_nonneg (f : ℂ → ℂ) (r : ℝ) :
    0 ≤ wimanMajorant f r := by
  exact tsum_nonneg fun n => wimanTerm_nonneg f r n

/-- **Each radial Taylor term is at most the radial majorant.** Let $f$ be an entire function with
Taylor coefficients $a_n = f^{(n)}(0) / n!$ at the origin, and let
$M_f(r) = \sum_{k \ge 0} |a_k| \, |r|^k$ be its radial majorant. For every real $r$ and every
$n \in \mathbb{N}$, $|a_n| \, |r|^n \le M_f(r)$. -/
theorem wimanTerm_le_wimanMajorant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℝ) (n : ℕ) :
    wimanTerm f r n ≤ wimanMajorant f r := by
  rw [wimanMajorant]
  exact (summable_wimanTerm f hf r).le_tsum n fun m _ => wimanTerm_nonneg f r m

end

end Complex
