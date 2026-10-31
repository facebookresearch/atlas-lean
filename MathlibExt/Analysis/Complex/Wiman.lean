/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Wiman maximum-term theorem

This file fixes the Taylor-coefficient, maximum-term, and maximum-modulus
normalizations used by the Wiman route. A strict unbounded-radius corollary of
the classical Wiman-Valiron inequality quoted by Filevych (2003), specialized
to transcendental entire functions and exponent `2 / 3`, is proved in
`MathlibExt.Analysis.Complex.Wiman.Filevych`.
-/

@[expose] public section

namespace Complex

noncomputable section

open Complex Set

/-- **Wiman Taylor coefficient.** For a function $f : \mathbb{C} \to \mathbb{C}$ and
$n \in \mathbb{N}$, the $n$th Taylor coefficient of $f$ at the origin is
$a_n = f^{(n)}(0) / n!$, where $f^{(n)}$ is the $n$th iterated complex derivative of $f$.

Here the derivative at a point where a function is not complex differentiable is taken to be
$0$. For an entire function these are the coefficients of its Taylor series at $0$. -/
def wimanTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- **Wiman term.** For a function $f : \mathbb{C} \to \mathbb{C}$, a real number $r$ and a natural
number $n$, the Wiman term of $f$ at radius $r$ and index $n$ is the real number $|a_n| \, |r|^n$,
where $a_n = f^{(n)}(0) / n!$ is the $n$th Taylor coefficient of $f$ at the origin. It is the
modulus of the $n$th Taylor term of $f$ on the circle of radius $|r|$.

Using $|r|$ makes a negative input denote the same radius as its absolute value, so the Wiman
term is always nonnegative. -/
def wimanTerm (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℝ :=
  ‖wimanTaylorCoefficient f n‖ * |r| ^ n

/-- **Wiman maximum term.** For a function $f : \mathbb{C} \to \mathbb{C}$ and a real number $r$,
the Wiman maximum term $\mu(f, r)$ is the supremum over $n \in \mathbb{N}$ of the Wiman terms
$|a_n| \, |r|^n$, where $a_n = f^{(n)}(0) / n!$ is the $n$th Wiman Taylor coefficient of $f$.

Here the supremum of a set of real numbers that is not bounded above is taken to be $0$. -/
def wimanMaximumTerm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (range (wimanTerm f r))

/-- **Wiman maximum modulus.** For a function $f : \mathbb{C} \to \mathbb{C}$ and a real number
$r$, the Wiman maximum modulus $M(f, r)$ is the supremum of $|f(z)|$ over all $z \in \mathbb{C}$
with $|z| = |r|$.

Here the supremum of a set of real numbers that is not bounded above is taken to be $0$. -/
def wimanMaximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖f z‖) '' Metric.sphere 0 |r|)

/-- **Wiman term at the absolute value of the radius.** For every function
$f : \mathbb{C} \to \mathbb{C}$, every real number $r$ and every natural number $n$, the Wiman term
of $f$ at radius $|r|$ and index $n$ equals the Wiman term of $f$ at radius $r$ and index $n$. -/
@[simp]
theorem wimanTerm_abs (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    wimanTerm f |r| n = wimanTerm f r n := by
  simp [wimanTerm]

/-- **Wiman maximum term at the absolute value of the radius.** For every function
$f : \mathbb{C} \to \mathbb{C}$ and every real number $r$, the Wiman maximum term of $f$ at
radius $|r|$ equals the Wiman maximum term of $f$ at radius $r$. -/
@[simp]
theorem wimanMaximumTerm_abs (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumTerm f |r| = wimanMaximumTerm f r := by
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_abs f r n

/-- **Wiman maximum modulus at the absolute value of the radius.** For every function
$f : \mathbb{C} \to \mathbb{C}$ and every real number $r$, the Wiman maximum modulus of $f$ at
radius $|r|$ equals the Wiman maximum modulus of $f$ at radius $r$. -/
@[simp]
theorem wimanMaximumModulus_abs (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumModulus f |r| = wimanMaximumModulus f r := by
  simp [wimanMaximumModulus]

/-- **Wiman term at a negated radius.** For every function $f : \mathbb{C} \to \mathbb{C}$, every
real number $r$ and every natural number $n$, the Wiman term of $f$ at radius $-r$ and index $n$
equals the Wiman term of $f$ at radius $r$ and index $n$. -/
@[simp]
theorem wimanTerm_neg (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    wimanTerm f (-r) n = wimanTerm f r n := by
  simp [wimanTerm]

/-- **The Wiman maximum term is even in the radius.** For every function
$f : \mathbb{C} \to \mathbb{C}$ and every real number $r$, the Wiman maximum term of $f$ at
radius $-r$ equals the Wiman maximum term of $f$ at radius $r$. -/
@[simp]
theorem wimanMaximumTerm_neg (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumTerm f (-r) = wimanMaximumTerm f r := by
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_neg f r n

/-- **The Wiman maximum modulus is even in the radius.** For every function
$f : \mathbb{C} \to \mathbb{C}$ and every real number $r$, the Wiman maximum modulus of $f$ at
radius $-r$ equals the Wiman maximum modulus of $f$ at radius $r$. -/
@[simp]
theorem wimanMaximumModulus_neg (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumModulus f (-r) = wimanMaximumModulus f r := by
  simp [wimanMaximumModulus]

/-- **Transcendental functions.** A function $f : \mathbb{C} \to \mathbb{C}$ is
transcendental when there is no complex polynomial $p$ with $f(z) = p(z)$ for all
$z \in \mathbb{C}$.

No analyticity is assumed; results about transcendental entire functions assume it separately. -/
def IsTranscendental (f : ℂ → ℂ) : Prop :=
  ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z

/-- **Values on a circle are bounded by the maximum modulus.** Let $f : \mathbb{C} \to \mathbb{C}$
be continuous, let $r$ be a real number and let $z \in \mathbb{C}$ with $|z| = r$. Then
$|f(z)| \le M(f, r)$, where $M(f, r)$ is the Wiman maximum modulus of $f$ at radius $r$. -/
theorem norm_le_wimanMaximumModulus {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hf : Continuous f) (hz : ‖z‖ = r) :
    ‖f z‖ ≤ wimanMaximumModulus f r := by
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  apply le_csSup
  · exact (isCompact_sphere (0 : ℂ) |r|).bddAbove_image
      ((continuous_norm.comp hf).continuousOn)
  · exact ⟨z, by simpa [Metric.mem_sphere, abs_of_nonneg hr] using hz, rfl⟩

/-- **Cubing a Wiman 2/3 bound.** Let $M$ and $\mu$ be real numbers with $M \ge 0$,
$\mu \ge 0$ and $\log \mu \ge 0$, where $\log$ is the real logarithm with $\log 0 = 0$.
If $M \le \mu (\log \mu)^{2/3}$, then $M^3 \le \mu^3 (\log \mu)^2$. -/
theorem cube_le_cube_mul_log_sq_of_wiman {M μ : ℝ}
    (hM : 0 ≤ M) (_hμ : 0 ≤ μ) (hlog : 0 ≤ Real.log μ)
    (hWiman : M ≤ μ * Real.log μ ^ (2 / 3 : ℝ)) :
    M ^ 3 ≤ μ ^ 3 * Real.log μ ^ 2 := by
  calc
    M ^ 3 ≤ (μ * Real.log μ ^ (2 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hM hWiman 3
    _ = μ ^ 3 * (Real.log μ ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [mul_pow]
    _ = μ ^ 3 * Real.log μ ^ 2 := by
      congr 1
      rw [← Real.rpow_mul_natCast hlog]
      norm_num [Real.rpow_two]

end

end Complex
