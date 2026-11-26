/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Poly-Bernoulli polynomials

The polynomial `polyBernoulliPoly` evaluates to the corresponding poly-Bernoulli number at zero
and is the constant one in degree zero.
-/

namespace MetaMathlibExt

@[expose] public section

/--
**Poly-Bernoulli polynomials.** For a natural number $n$, an integer $k$ and a rational number
$x$, the poly-Bernoulli polynomial of degree $n$ and order $k$ at $x$ is the rational number
$$B_n^{(k)}(x) = \sum_{i=0}^{n} \binom{n}{i} B_i^{(k)} x^{n-i},$$
where $B_i^{(k)}$ are the poly-Bernoulli numbers.

These are the coefficients of the generating function
$\frac{\mathrm{Li}_k(1-e^{-t})}{1-e^{-t}} e^{xt} = \sum_{n \ge 0} B_n^{(k)}(x) \frac{t^n}{n!}$,
which is how the source defines them.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public def polyBernoulliPoly (n : ℕ) (p : ℤ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℚ) * polyBernoulli i p * x ^ (n - i)

/--
**Poly-Bernoulli polynomials at zero.** For every natural number $n$ and every integer $k$, the
poly-Bernoulli polynomial of degree $n$ and order $k$ evaluated at $0$ equals the
poly-Bernoulli number of index $n$ and order $k$: $B_n^{(k)}(0) = B_n^{(k)}$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero (n : ℕ) (p : ℤ) :
    polyBernoulliPoly n p 0 = polyBernoulli n p := by
  rw [polyBernoulliPoly, Finset.sum_range_succ]
  have hzero :
      (∑ i ∈ Finset.range n,
        (n.choose i : ℚ) * polyBernoulli i p * (0 : ℚ) ^ (n - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hsub : n - i ≠ 0 := by omega
    simp [hsub]
  rw [hzero]
  simp

/--
**Poly-Bernoulli polynomials of degree zero.** For every integer $k$ and every rational number
$x$, the poly-Bernoulli polynomial of degree $0$ and order $k$ satisfies $B_0^{(k)}(x) = 1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero_index (p : ℤ) (x : ℚ) :
    polyBernoulliPoly 0 p x = 1 := by
  simp [polyBernoulliPoly, polyBernoulli]

end

end MetaMathlibExt
