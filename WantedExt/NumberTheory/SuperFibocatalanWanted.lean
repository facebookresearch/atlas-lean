/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Super FiboCatalan numbers and their Lucas analogues

Statements from Kendra Killpatrick, "Super FiboCatalan Numbers
and Their Lucas Analogues", *Journal of Integer Sequences* 28
(2025), Article 25.5.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Killpatrick/killp6.tex>).

The Fibonacci factorial `F_n!` is MathlibExt's
`MetaMathlibExt.fibonacciFactorial` (in `ℚ`), and the
FiboCatalan number and fibonomial below are the displayed
quotients built from it. The Lucas polynomials `{n}` of the
paper (`{0} = 0`, `{1} = 1`, `{n} = s{n-1} + t{n-2}`) are
`lucasPoly n` in `MvPolynomial (Fin 2) ℤ`, with `X 0 = s` and
`X 1 = t`, and `{n}!` is `lucasFactorial`. Statements of the
form "this quotient is a polynomial with non-negative integer
coefficients" are stated as the existence of such a polynomial
`p` with `p * (denominator) = (numerator)` in
`MvPolynomial (Fin 2) ℤ`, and rational identities are cleared
of denominators, as in the paper's proofs.

Of the paper's thirteen numbered statements, ten are
formalized below (including the super FiboCatalan half of
Corollary 5). One further statement is already covered in
MathlibExt and is not restated: Corollary 9, via
`MetaMathlibExt.generalizedFibonacciCatalan_isPosInt` (with
`generalizedFibonacciCatalan_r1`), which also proves the
generalized half of Corollary 5. Theorem 1 and Lemma 2, which
concern the Sagan-Tirrell Lucas-atom factorization
(`log_d` exponents of the atoms `P_d`), are not formalized
here: that factorization infrastructure does not exist in the
repository.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.NumberTheory.GeneralizedFibocatalanNumber

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperFibocatalanWanted

open MetaMathlibExt

/-- The paper's FiboCatalan number
`C_{n,F} = F_{2n}!/(F_n! F_{n+1}!)`, in `ℚ`. -/
noncomputable def fiboCatalan (n : ℕ) : ℚ :=
  fibonacciFactorial (2 * n) /
    (fibonacciFactorial n * fibonacciFactorial (n + 1))

/-- The paper's fibonomial coefficient
`⟨n k⟩_F = F_n!/(F_k! F_{n-k}!)`, in `ℚ`, for `k ≤ n`;
extended by `0` for `k > n` (outside the paper's domain the
raw quotient would use truncated subtraction). -/
noncomputable def fibonomial (n k : ℕ) : ℚ :=
  if k ≤ n then
    fibonacciFactorial n /
      (fibonacciFactorial k * fibonacciFactorial (n - k))
  else 0

/-- **Corollary 5** (super FiboCatalan half): the super
FiboCatalan numbers
`S(m,n)_F = F_{2m}! F_{2n}!/(F_m! F_n! F_{m+n}!)` are positive
integers (the generalized half is
`MetaMathlibExt.generalizedFibonacciCatalan_isPosInt`).

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Corollary 5. -/
theorem_wanted superFibonacciCatalan_isPosInt (m n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ (k : ℚ) =
      fibonacciFactorial (2 * m) * fibonacciFactorial (2 * n) /
        (fibonacciFactorial m * fibonacciFactorial n *
          fibonacciFactorial (m + n))

/-- **Lemma 6**: `F_{2n} F_{n+2} - F_{2n+2} F_n = (-1)^n F_n`.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Lemma 6. -/
theorem_wanted fib_mul_sub_mul (n : ℕ) :
    (Nat.fib (2 * n) : ℤ) * (Nat.fib (n + 2) : ℤ) -
        (Nat.fib (2 * n + 2) : ℤ) * (Nat.fib n : ℤ) =
      (-1) ^ n * (Nat.fib n : ℤ)

/-- **Theorem 7**:
`F_{2n+1} F_{2n} C_{n,F} - F_{n+1} F_n C_{n+1,F}
= (-1)^n F_n F_{2n+1} F_{2n}!/(F_{n+2}! F_n!)`.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 7. -/
theorem_wanted fiboCatalan_identity (n : ℕ) :
    (Nat.fib (2 * n + 1) : ℚ) * (Nat.fib (2 * n) : ℚ) *
          fiboCatalan n -
        (Nat.fib (n + 1) : ℚ) * (Nat.fib n : ℚ) *
          fiboCatalan (n + 1) =
      (-1) ^ n * (Nat.fib n : ℚ) * (Nat.fib (2 * n + 1) : ℚ) *
        (fibonacciFactorial (2 * n) /
          (fibonacciFactorial (n + 2) * fibonacciFactorial n))

/-- **Corollary 8**: for `n ≥ 1`,
`F_{2n+1} F_{2n}!/(F_{n+2}! F_n!)
= (1/F_{n+2}) ⟨2n+1 n⟩_F` is an integer.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Corollary 8. -/
theorem_wanted fib_mul_factorialQuotient_eq_and_isInt
    (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (2 * n + 1) : ℚ) *
          (fibonacciFactorial (2 * n) /
            (fibonacciFactorial (n + 2) * fibonacciFactorial n)) =
        fibonomial (2 * n + 1) n / (Nat.fib (n + 2) : ℚ) ∧
      ∃ k : ℤ, (k : ℚ) =
        (Nat.fib (2 * n + 1) : ℚ) *
          (fibonacciFactorial (2 * n) /
            (fibonacciFactorial (n + 2) * fibonacciFactorial n))

/-- The paper's Lucas polynomial `{n}` in variables `s, t`:
`{0} = 0`, `{1} = 1`, `{n} = s{n-1} + t{n-2}`, with
`X 0 = s` and `X 1 = t`. -/
noncomputable def lucasPoly : ℕ → MvPolynomial (Fin 2) ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => MvPolynomial.X 0 * lucasPoly (n + 1) +
      MvPolynomial.X 1 * lucasPoly n

/-- The paper's Lucas factorial
`{n}! = {n}{n-1} ⋯ {1}` (empty product `1` at `n = 0`). -/
noncomputable def lucasFactorial (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∏ i ∈ Finset.Icc 1 n, lucasPoly i

/-- The paper's `k`-divisible Lucas factorial
`{n : k}! = {k}{2k} ⋯ {nk}`. -/
noncomputable def lucasKDivFactorial (k n : ℕ) :
    MvPolynomial (Fin 2) ℤ :=
  ∏ i ∈ Finset.Icc 1 n, lucasPoly (k * i)

/-- **Theorem 3**: the Lucas analogues of the super FiboCatalan
numbers `S{m, n} = {2m}! {2n}!/({m}! {n}! {m+n}!)` are
polynomials with non-negative integer coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 3. -/
theorem_wanted exists_nonneg_poly_superLucasCatalan (m n : ℕ) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasFactorial m * lucasFactorial n *
          lucasFactorial (m + n)) =
        lucasFactorial (2 * m) * lucasFactorial (2 * n)

/-- **Theorem 4**: the Lucas analogues of the generalized
FiboCatalan numbers `J_{{r}} {2n}!/({n}! {n+r+1}!)`, where
`J_{{r}} = {2r+1}!/{r}!`, are polynomials with non-negative
integer coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 4. -/
theorem_wanted exists_nonneg_poly_generalizedLucasCatalan
    (r n : ℕ) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasFactorial r * lucasFactorial n *
          lucasFactorial (n + r + 1)) =
        lucasFactorial (2 * r + 1) * lucasFactorial (2 * n)

/-- **Lemma 10**:
`{2n} {n+2} - {2n+2} {n} = (-1)^n {2} t^n {n}`.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Lemma 10. -/
theorem_wanted lucasPoly_mul_sub_mul (n : ℕ) :
    lucasPoly (2 * n) * lucasPoly (n + 2) -
        lucasPoly (2 * n + 2) * lucasPoly n =
      (-1) ^ n * lucasPoly 2 * MvPolynomial.X 1 ^ n * lucasPoly n

/-- **Theorem 11**, cleared of denominators via
`C_{{n}} = {2n}!/({n+1} {n}! {n}!)`: the identity
`{2n+1} {2n} C_{{n}} - {n+1} {n} C_{{n+1}}
= (-1)^n t^n {2} {n} {2n+1} {2n}!/({n+2}! {n}!)`, multiplied
through by `{n+2}! {n}!`.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 11. -/
theorem_wanted lucasCatalan_identity_mul_factorial (n : ℕ) :
    (lucasPoly (2 * n + 1) * lucasPoly (2 * n) * lucasPoly (n + 2) -
        lucasPoly (2 * n + 2) * lucasPoly (2 * n + 1) *
          lucasPoly n) * lucasFactorial (2 * n) =
      (-1) ^ n * MvPolynomial.X 1 ^ n * lucasPoly 2 *
        lucasPoly n * lucasPoly (2 * n + 1) *
        lucasFactorial (2 * n)

/-- **Corollary 12**: for `n ≥ 1`, the number
`{2n+1} {2} {2n}!/({n+2}! {n}!)`, which equals
`{2} (1/{n+2}) ⟨2n+1 n⟩` (the displayed equality cleared of
denominators), is a polynomial with non-negative integer
coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Corollary 12. -/
theorem_wanted exists_nonneg_poly_lucasQuotient (n : ℕ)
    (hn : 1 ≤ n) :
    lucasPoly (n + 2) *
          (lucasPoly (2 * n + 1) * lucasFactorial (2 * n)) *
        (lucasFactorial n * lucasFactorial (n + 1)) =
      (lucasFactorial (n + 2) * lucasFactorial n) *
        lucasFactorial (2 * n + 1) ∧
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasFactorial (n + 2) * lucasFactorial n) =
        lucasPoly (2 * n + 1) * lucasPoly 2 *
          lucasFactorial (2 * n)

/-- **Theorem 13**: the `k`-divisible lucanomial analogues
`S{m, n : k}` of the super Catalan numbers are polynomials
with non-negative integer coefficients, for `k ≥ 1`.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 13. -/
theorem_wanted exists_nonneg_poly_kDivLucasCatalan
    (k m n : ℕ) (hk : 1 ≤ k) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasKDivFactorial k m * lucasKDivFactorial k n *
          lucasKDivFactorial k (m + n)) =
        lucasKDivFactorial k (2 * m) * lucasKDivFactorial k (2 * n)

end MathlibExt.NumberTheory.SuperFibocatalanWanted
