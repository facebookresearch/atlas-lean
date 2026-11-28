/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Series over a family of Lucas polynomial squares

We prove `hasSum_lucasPoly_sq_family`: a series whose denominators are squares of Lucas
polynomials, each shifted by a constant multiple of a square of a Fibonacci polynomial, converges
unconditionally to `l_{tk+r} / l_{tk} - α ^ r`. It is the Lucas-polynomial case of the theorem of
Koshy cited in its docstring.

The Fibonacci polynomials `f_n(x)` (`f_0 = 0`, `f_1 = 1`) and Lucas polynomials `l_n(x)`
(`l_0 = 2`, `l_1 = x`), both with `z_{n+2} = x z_{n+1} + z_n`, are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at a real `x` with
`Polynomial.aeval`; `Δ = √(x² + 4)` and `α = (x + Δ)/2`. The paper takes `x` an arbitrary
integer; the statement needs `x > 0`: at `x = 0` the Lucas polynomials of odd index vanish, and
for `x < 0` the ratio `l_{m+r}/l_m` tends to `((x - Δ)/2)^r`, not `α^r`. It is stated for real
`x > 0`, which contains the positive integers.

The generalized Catalan identity `l_{m+i} l_{m+j} - l_m l_{m+i+j} = (-1)^m (-Δ²) f_i f_j` turns
the `n`-th term, counted from `n = 0`, into `l_{e+r} / l_e - l_{e'+r} / l_{e'}` with
`e = (2pn + t)k` and `e' = e + 2pk`, so the series is the case `λ = 1` of the telescoping series
`hasSum_gibonacciPoly_pow_ratio_telescoping`.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Positivity for the gibonacci recurrence.** A real sequence satisfying
$\ell_{n+2} = x\ell_{n+1} + \ell_n$ is positive at every index when $x$, $\ell_0$ and $\ell_1$
are positive. -/
public theorem pos_of_gibonacci_recurrence {x : ℝ} (hx : 0 < x) (l : ℕ → ℝ)
    (hl : ∀ n, l (n + 2) = x * l (n + 1) + 1 * l n) (h₀ : 0 < l 0) (h₁ : 0 < l 1) (n : ℕ) :
    0 < l n := by
  have h : ∀ n, 0 < l n ∧ 0 < l (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h₀, h₁⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hl, one_mul]
      exact add_pos (mul_pos hx ih.2) ih.1
  exact (h n).1

namespace hasSum_lucasPoly_sq_family

/-- Let `l` be a nonvanishing solution of `z_{n+2} = x z_{n+1} + z_n`, let `f` be the solution with
`f_0 = 0` and `f_1 = 1`, and let `C = l_1^2 - l_0 l_2`. Then the term of index `n` of the family is
the difference `l_{e+r} / l_e - l_{e'+r} / l_{e'}`, where `e = (2pn + t)k` and `e' = e + 2pk`. -/
private theorem summand_eq {x C : ℝ} (l f : ℕ → ℝ)
    (hl : ∀ n, l (n + 2) = x * l (n + 1) + 1 * l n)
    (hf : ∀ n, f (n + 2) = x * f (n + 1) + 1 * f n) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
    (hC : l 1 * l 1 - l 0 * l 2 = C) (hpos : ∀ n, 0 < l n) (k p r t n : ℕ) :
    (-1) ^ (t * k) * C * f r * f (2 * p * k) /
        (l ((2 * p * (n + 1) + t - p) * k) ^ 2 - (-1) ^ (t * k) * C * f (p * k) ^ 2) =
      l ((2 * p * (n + 1) + t - 2 * p) * k + r) / l ((2 * p * (n + 1) + t - 2 * p) * k) -
        l ((2 * p * (n + 1) + t) * k + r) / l ((2 * p * (n + 1) + t) * k) := by
  have catalan := horadam_generalized_catalan_identity x 1 l l f hl hl hf hf₀ hf₁
  have det (m i j : ℕ) :
      l (m + i) * l (m + j) - l m * l (m + i + j) = (-1) ^ m * C * f j * f i := by
    have h := catalan 0 j 1
    simp only [Nat.zero_add, pow_zero, one_mul, mul_comm (l j) (l 1), hC] at h
    rw [catalan, h]
    ring
  have hsign : (-1 : ℝ) ^ ((2 * p * n + t) * k) = (-1) ^ (t * k) := by
    rw [show (2 * p * n + t) * k = 2 * (p * n * k) + t * k by ring, pow_add, pow_mul]
    norm_num
  have i₀ : 2 * p * (n + 1) + t - 2 * p = 2 * p * n + t := by
    rw [mul_add_one]
    omega
  have i₁ : 2 * p * (n + 1) + t - p = 2 * p * n + t + p := by
    rw [mul_add_one]
    omega
  have e₀ : (2 * p * (n + 1) + t - 2 * p) * k = (2 * p * n + t) * k := by rw [i₀]
  have e₁ : (2 * p * (n + 1) + t - p) * k = (2 * p * n + t) * k + p * k := by
    rw [i₁, Nat.add_mul]
  have e₂ : (2 * p * (n + 1) + t) * k = (2 * p * n + t) * k + 2 * p * k := by ring
  rw [e₀, e₁, e₂]
  generalize (2 * p * n + t) * k = e at hsign ⊢
  have d₁ := det e (p * k) (p * k)
  have d₂ := det e r (2 * p * k)
  rw [hsign, show e + p * k + p * k = e + 2 * p * k by ring] at d₁
  rw [hsign, show e + r + 2 * p * k = e + 2 * p * k + r by ring] at d₂
  have hden : l (e + p * k) ^ 2 - (-1) ^ (t * k) * C * f (p * k) ^ 2 =
      l e * l (e + 2 * p * k) := by
    linear_combination d₁
  rw [hden, div_sub_div _ _ (hpos e).ne' (hpos _).ne']
  congr 1
  linear_combination -d₂

end hasSum_lucasPoly_sq_family

/-- **Series over a family of Lucas polynomial squares.** Let $x > 0$ be real, let
$\Delta = \sqrt{x^2 + 4}$ and $\alpha = (x + \Delta)/2$, and let $f_n$ and $l_n$ be the
Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$,
$l_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both. Let $k$, $r$, $t$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \frac{-(-1)^{tk} \Delta^2 f_r f_{2pk}}
{l_{(2pn+t-p)k}^2 + (-1)^{tk} \Delta^2 f_{pk}^2}$$
converges unconditionally, and its sum is $l_{tk+r} / l_{tk} - \alpha^r$.

This is the Lucas-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1
(`fq-2024-koshy11112023-thm-3.1`). -/
public theorem hasSum_lucasPoly_sq_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hr : 0 < r) (ht : 0 < t) (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (-1) ^ (t * k) * (-(x ^ 2 + 4)) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 r) *
            aeval x (generalizedFibonacciPolynomial 0 1 X 1 (2 * p * k)) /
          (aeval x (generalizedFibonacciPolynomial 2 X X 1 ((2 * p * (n + 1) + t - p) * k)) ^ 2 -
            (-1) ^ (t * k) * (-(x ^ 2 + 4)) *
              aeval x (generalizedFibonacciPolynomial 0 1 X 1 (p * k)) ^ 2))
      (aeval x (generalizedFibonacciPolynomial 2 X X 1 (t * k + r)) /
          aeval x (generalizedFibonacciPolynomial 2 X X 1 (t * k)) -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ r) := by
  have hl (n : ℕ) : aeval x (generalizedFibonacciPolynomial 2 X X 1 (n + 2)) =
      x * aeval x (generalizedFibonacciPolynomial 2 X X 1 (n + 1)) +
        1 * aeval x (generalizedFibonacciPolynomial 2 X X 1 n) := by
    simp
  have hf (n : ℕ) : aeval x (generalizedFibonacciPolynomial 0 1 X 1 (n + 2)) =
      x * aeval x (generalizedFibonacciPolynomial 0 1 X 1 (n + 1)) +
        1 * aeval x (generalizedFibonacciPolynomial 0 1 X 1 n) := by
    simp
  have hpos := pos_of_gibonacci_recurrence hx
    (fun n => aeval x (generalizedFibonacciPolynomial 2 X X 1 n)) hl
    (by norm_num [map_ofNat]) (by simpa using hx)
  have h := hasSum_gibonacciPoly_pow_ratio_telescoping _ (Or.inr rfl) hx hk hr ht Nat.one_pos htp
  simp only [pow_one, one_mul] at h
  refine h.congr_fun fun n => ?_
  exact hasSum_lucasPoly_sq_family.summand_eq
    (fun n => aeval x (generalizedFibonacciPolynomial 2 X X 1 n))
    (fun n => aeval x (generalizedFibonacciPolynomial 0 1 X 1 n)) hl hf (by simp) (by simp)
    (by norm_num [generalizedFibonacciPolynomial, map_ofNat]; ring) hpos k p r t n

end MetaMathlibExt
