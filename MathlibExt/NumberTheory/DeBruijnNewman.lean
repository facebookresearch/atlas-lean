/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.NumberTheory.DeBruijnNewman

open Real MeasureTheory

/-!
# The de Bruijn--Newman constant

Newman's kernel `Φ` (an absolutely convergent series, proved summable
here), its heat-flow deformation `H λ z = ∫₀^∞ e^{λu²} Φ(u) cos(zu) du`,
and the de Bruijn--Newman constant as the totalized infimum of times at
which all zeros of `H` are real.

Source: Optimization Problems, record 21a, "de Bruijn–Newman constant",
frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/21a.md` SHA-256
`0c51f29928c74cf9032138fbd59c873cac97108204f4e0eb14c2f2ae858ef338`.

Scope notes: Newman's threshold theorem (zeros all real iff `λ ≥ Λ`),
monotonicity in `λ`, integrability of the `H` integrand, and the
equivalence of `Λ = 0` with the Riemann hypothesis are not formalized;
without Newman's theorem `deBruijnNewmanConstant` is the totalized
infimum of the all-real-zero times, which is how the literature bounds
in `WantedExt` are phrased below.
-/

/-- **Summands of Newman's kernel.** For real $u$ and a natural number $n$, the $n$-th summand
of Newman's kernel, counted from $n = 0$, is
$$\left(2\pi^2 (n+1)^4 e^{9u} - 3\pi (n+1)^2 e^{5u}\right) e^{-\pi (n+1)^2 e^{4u}}.$$ -/
noncomputable def phiTerm (u : ℝ) (n : ℕ) : ℝ :=
  (2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) -
    3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u))

theorem summable_phiTerm (u : ℝ) : Summable (phiTerm u) := by
  set A : ℝ := π * Real.exp (4 * u) with hAdef
  have hA : 0 < A := mul_pos Real.pi_pos (Real.exp_pos _)
  set C : ℝ := 2 * π ^ 2 * Real.exp (9 * u) + 3 * π * Real.exp (5 * u) with hCdef
  have hC : 0 ≤ C := by positivity
  have hr : ‖Real.exp (-A)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable fun n : ℕ => C * ((n + 1 : ℝ) ^ 4 * Real.exp (-A) ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 4 hr
    have h2 : Summable fun n : ℕ => ((n + 1 : ℝ) ^ 4 * Real.exp (-A) ^ (n + 1)) := by
      have := (summable_nat_add_iff 1).mpr h
      simpa [pow_add] using this
    exact h2.mul_left C
  refine Summable.of_norm_bounded hsum fun n => ?_
  set m : ℝ := (n + 1 : ℝ) with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact_mod_cast Nat.le_add_left 1 n
  have hmnn : (0 : ℝ) ≤ m := by linarith
  have hterm : phiTerm u n =
      (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)) *
        Real.exp (-A * m ^ 2) := by
    have he : -π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) = -A * m ^ 2 := by
      rw [hAdef, hm]
      ring
    rw [phiTerm, he, ← hm]
  rw [hterm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)|
      ≤ C * m ^ 4 := by
    have h2 : m ^ 2 ≤ m ^ 4 := by
      nlinarith [sq_nonneg (m ^ 2 - 1), sq_nonneg (m - 1)]
    calc |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)|
        ≤ 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) + 3 * π * m ^ 2 * Real.exp (5 * u) := by
          have ha : (0:ℝ) ≤ 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) := by positivity
          have hb : (0:ℝ) ≤ 3 * π * m ^ 2 * Real.exp (5 * u) := by positivity
          refine (abs_sub _ _).trans_eq ?_
          rw [abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ C * m ^ 4 := by
          rw [hCdef]
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 3 * π * Real.exp (5 * u))
            (sub_nonneg.mpr h2)]
  have h2 : Real.exp (-A * m ^ 2) ≤ Real.exp (-A) ^ (n + 1) := by
    have hsq : m ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
    have : -A * m ^ 2 ≤ -A * m := by nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hsq)]
    refine (Real.exp_le_exp.mpr this).trans_eq ?_
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hm]
    push_cast
    ring
  calc |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) - 3 * π * m ^ 2 * Real.exp (5 * u)| *
        Real.exp (-A * m ^ 2)
      ≤ (C * m ^ 4) * Real.exp (-A) ^ (n + 1) := by
        exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)
    _ = C * (m ^ 4 * Real.exp (-A) ^ (n + 1)) := by ring

/-- **Newman's kernel.** For real $u$, Newman's kernel is the sum of the series
$$\Phi(u) = \sum_{n=1}^{\infty} (2\pi^2 n^4 e^{9u} - 3\pi n^2 e^{5u}) e^{-\pi n^2 e^{4u}},$$
which converges absolutely for every real $u$. -/
noncomputable def phi (u : ℝ) : ℝ :=
  ∑' n : ℕ, phiTerm u n

/-- **The de Bruijn–Newman deformation.** For real $\lambda$ and complex $z$,
$$H_\lambda(z) = \int_0^\infty e^{\lambda u^2}\, \Phi(u) \cos(zu)\, du,$$
where $\Phi$ is Newman's kernel and the integral runs over $u > 0$.

The integral is a Lebesgue integral, taken to be $0$ when the integrand is not integrable. -/
noncomputable def H (lam : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (lam * u ^ 2) * phi u : ℝ) : ℂ) *
    Complex.cos (z * (u : ℂ))

/-- **Real-rootedness of the de Bruijn–Newman deformation.** For real $\lambda$, this is the
statement that every zero of the de Bruijn–Newman deformation $H_\lambda$ is real: every complex
$z$ with $H_\lambda(z) = 0$ has imaginary part $0$. -/
def ZerosAllReal (lam : ℝ) : Prop :=
  ∀ z : ℂ, H lam z = 0 → z.im = 0

/-- **The de Bruijn–Newman constant.** The de Bruijn–Newman constant $\Lambda$ is the infimum of
the set of real numbers $\lambda$ such that every zero of the de Bruijn–Newman deformation
$H_\lambda$ is real. The infimum is taken in $\mathbb{R}$, with the convention that it is $0$
when this set is empty or not bounded below.

Newman's theorem, that every zero of $H_\lambda$ is real exactly when $\lambda \ge \Lambda$, is
not part of this definition. -/
noncomputable def deBruijnNewmanConstant : ℝ :=
  sInf { lam : ℝ | ZerosAllReal lam }

end MathlibExt.NumberTheory.DeBruijnNewman
