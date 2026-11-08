/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An explicit formula and a recurrence for OEIS A265233

Statements from Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", *Journal of Integer
Sequences* 29 (2026), Article 26.5.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Jin/jin48.html>).

The OEIS definition of `(a_n)` is not reproduced in the
extracted statements, so `a265233` is defined over `ℚ`
by the paper's Theorem 1(2) recurrence together with its
initial values `a_0 = 1`, `a_1 = 1`, `a_2 = 7`,
`a_3 = 56`, which determine the sequence. The explicit
formula of Theorem 1(1), the diagonal coefficient of
Lemma 3, and both parts of Corollary 2 are then stated
as properties of this sequence; the paper's Franel
numbers `f_m = ∑_k C(m, k)^3` are the existing
`MetaMathlibExt.binomialPowerSeq 3 0 m`, cast to `ℚ`.
The
recurrence and the explicit formula were checked to
agree for `1 ≤ n ≤ 13` (values `1, 1, 7, 56, 495, 4686,
…`), and the Lemma 3 coefficient was checked against
`f_m` for `m ≤ 5`.

Corollary 2(1) is stated analytically on the common
convergence domain `|x| < 1/12` and
`|27x(1 - 4x)^2| < 1` (Mathlib's `₂F₁` takes the junk
value `0` outside its radius of convergence).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA265233Wanted

/-- OEIS A265233, defined over `ℚ` by the recurrence of
the paper's Theorem 1(2) with its initial values
`a_0 = 1`, `a_1 = 1`, `a_2 = 7`, `a_3 = 56`: for
`N ≥ 4`, `N^2 a_N = (19N^2 - 19N + 6) a_{N-1}
- 96(N-1)^2 a_{N-2} + 144(N-1)(N-2) a_{N-3}`. -/
def a265233 : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 7
  | 3 => 56
  | n + 4 =>
      ((19 * ((n : ℚ) + 4) ^ 2 - 19 * ((n : ℚ) + 4) + 6) *
          a265233 (n + 3)
        - 96 * ((n : ℚ) + 3) ^ 2 * a265233 (n + 2)
        + 144 * ((n : ℚ) + 3) * ((n : ℚ) + 2) *
          a265233 (n + 1))
        / ((n : ℚ) + 4) ^ 2

/-- **Theorem 1**(1): for `n ≥ 1`,
`a_n = (1/6) ∑_{m=0}^{n} C(n, m) 4^{n-m} f_m`, where
`f_m` is the Franel number
`MetaMathlibExt.binomialPowerSeq 3 0 m`.

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Theorem 1. -/
theorem_wanted a265233_eq_sum_franel (n : ℕ) (hn : 1 ≤ n) :
    a265233 n = (1 / 6) * ∑ m ∈ Finset.range (n + 1),
      (Nat.choose n m : ℚ) * 4 ^ (n - m) *
        (MetaMathlibExt.binomialPowerSeq 3 0 m : ℚ)

/-- **Lemma 3**: for every `m ≥ 0`, the coefficient of
`x^m y^m z^m` in `((x + y)(y + z)(z + x))^m` is the
Franel number `f_m`
(`MetaMathlibExt.binomialPowerSeq 3 0 m`).

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Lemma 3. -/
theorem_wanted coeff_pow_eq_franel (m : ℕ) :
    (((MvPolynomial.X 0 + MvPolynomial.X 1) *
        (MvPolynomial.X 1 + MvPolynomial.X 2) *
        (MvPolynomial.X 2 + MvPolynomial.X 0)) ^ m :
        MvPolynomial (Fin 3) ℚ).coeff
      (Finsupp.single (0 : Fin 3) m +
        Finsupp.single (1 : Fin 3) m +
        Finsupp.single (2 : Fin 3) m)
      = (MetaMathlibExt.binomialPowerSeq 3 0 m : ℚ)

/-- **Corollary 2**(1): the ordinary generating function
satisfies `∑_{n ≥ 0} a_n x^n
= (₂F₁(1/3, 2/3; 1; 27x(1 - 4x)^2) + 5) / 6` on the
common convergence domain.

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Corollary 2. -/
theorem_wanted tsum_a265233_eq (x : ℝ) (hx : |x| < 1 / 12)
    (hz : |27 * x * (1 - 4 * x) ^ 2| < 1) :
    ∑' n : ℕ, (a265233 n : ℝ) * x ^ n =
      (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
        (27 * x * (1 - 4 * x) ^ 2) + 5) / 6

/-- **Corollary 2**(2): `a_n ~ (√3 / (6π)) · 12^n / n`
as `n → ∞`.

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Corollary 2. -/
theorem_wanted a265233_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (a265233 n : ℝ))
      (fun n : ℕ => Real.sqrt 3 / (6 * Real.pi) * 12 ^ n / n)

end MathlibExt.NumberTheory.OeisA265233Wanted
