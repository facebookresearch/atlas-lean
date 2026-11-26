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
FiboCatalan number and fibonomial are the displayed
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
available here (including the super FiboCatalan half of
Corollary 5). The product identities, FiboCatalan numbers and their identity,
super FiboCatalan integrality, fibonomial coefficients and the integral fibonomial quotient,
Lucas factorial and Lucas Catalan identity are imported from
`MathlibExt.NumberTheory.SuperFibocatalan`. One further statement is already covered in
MathlibExt and is not restated: Corollary 9, via
`MetaMathlibExt.generalizedFibonacciCatalan_isPosInt` (with
`generalizedFibonacciCatalan_r1`), which also proves the
generalized half of Corollary 5. Theorem 1 and Lemma 2 (quoted
from Sagan and Tirrell) use the Lucas atoms `P_d`, which the
paper introduces only through `{n} = ∏_{d ∣ n} P_d(s,t)`; in
Lemma 2 they enter as a function `P` with that property for
`n ≥ 1`, which determines `P d` for every `d ≥ 1`
(`MvPolynomial (Fin 2) ℤ` is a domain). Theorem 1's criterion
is stated through the exponents alone, so it takes no atoms.
The exponent `log_d` of `P_d` in a product of Lucas
polynomials is the number of factors `{n_i}` with `d ∣ n_i`
(Theorem 1), and in Lemma 2 it is the exact power of `P d`
dividing `{n}!`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.GeneralizedFibocatalanNumber
public import MathlibExt.NumberTheory.SuperFibocatalan

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperFibocatalanWanted

open MetaMathlibExt

/-- **$k$-divisible Lucas factorial.** For natural numbers $k$ and $n$, the $k$-divisible Lucas
factorial $\{n : k\}!$ is the product $\{n : k\}! = \{k\}\{2k\} \cdots \{nk\}$ of the Lucas
polynomials $\{ki\}$ in $s$ and $t$ for $1 \le i \le n$; in particular $\{0 : k\}! = 1$,
the empty product. -/
noncomputable def lucasKDivFactorial (k n : ℕ) :
    MvPolynomial (Fin 2) ℤ :=
  ∏ i ∈ Finset.Icc 1 n, lucasPoly (k * i)

/-- **Lucas super FiboCatalan numbers have non-negative coefficients.** Let $\{k\}$ be the
Lucas polynomials in $s$ and $t$ ($\{0\} = 0$, $\{1\} = 1$, $\{k+2\} = s\{k+1\} + t\{k\}$) and
let $\{k\}! = \{1\}\{2\} \cdots \{k\}$ be the Lucas factorial. For all natural numbers $m$
and $n$ there is a polynomial $p \in \mathbb{Z}[s, t]$ with non-negative coefficients such
that $p \, \{m\}! \, \{n\}! \, \{m+n\}! = \{2m\}! \, \{2n\}!$; that is, the Lucas analogue
$S\{m, n\} = \{2m\}! \, \{2n\}!/(\{m\}! \, \{n\}! \, \{m+n\}!)$ of the super FiboCatalan number
is a polynomial in $s$ and $t$ with non-negative integer coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 3. -/
theorem_wanted exists_nonneg_poly_superLucasCatalan (m n : ℕ) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasFactorial m * lucasFactorial n *
          lucasFactorial (m + n)) =
        lucasFactorial (2 * m) * lucasFactorial (2 * n)

/-- **Lucas generalized FiboCatalan numbers have non-negative coefficients.** Let $\{k\}$ be
the Lucas polynomials in $s$ and $t$ ($\{0\} = 0$, $\{1\} = 1$, $\{k+2\} = s\{k+1\} + t\{k\}$)
and let $\{k\}! = \{1\}\{2\} \cdots \{k\}$ be the Lucas factorial. For all natural numbers
$r$ and $n$ there is a polynomial $p \in \mathbb{Z}[s, t]$ with non-negative coefficients such
that $p \, \{r\}! \, \{n\}! \, \{n+r+1\}! = \{2r+1\}! \, \{2n\}!$; that is, with
$J_{\{r\}} = \{2r+1\}!/\{r\}!$, the Lucas analogue $J_{\{r\}} \, \{2n\}!/(\{n\}! \, \{n+r+1\}!)$
of the generalized FiboCatalan number is a polynomial in $s$ and $t$ with non-negative integer
coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 4. -/
theorem_wanted exists_nonneg_poly_generalizedLucasCatalan
    (r n : ℕ) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasFactorial r * lucasFactorial n *
          lucasFactorial (n + r + 1)) =
        lucasFactorial (2 * r + 1) * lucasFactorial (2 * n)

/-- **The Lucas quotient $\{2n+1\} \{2\} \{2n\}!/(\{n+2\}! \, \{n\}!)$ has non-negative
coefficients.** Let $\{k\}$ be the Lucas polynomials in $s$ and $t$ ($\{0\} = 0$, $\{1\} = 1$,
$\{k+2\} = s\{k+1\} + t\{k\}$) and let $\{k\}! = \{1\}\{2\} \cdots \{k\}$ be the Lucas
factorial. For every natural number $n \ge 1$,
$$\{n+2\} \, \{2n+1\} \, \{2n\}! \, \{n\}! \, \{n+1\}! = \{n+2\}! \, \{n\}! \, \{2n+1\}!,$$
and there is a polynomial $p \in \mathbb{Z}[s, t]$ with non-negative coefficients such that
$p \, \{n+2\}! \, \{n\}! = \{2n+1\} \, \{2\} \, \{2n\}!$. That is, the quotient
$\{2n+1\} \{2\} \{2n\}!/(\{n+2\}! \, \{n\}!)$, which by the first identity equals
$\{2\} \, \frac{1}{\{n+2\}} \, \{2n+1\}!/(\{n\}! \, \{n+1\}!)$, is a polynomial in $s$ and $t$
with non-negative integer coefficients.

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

/-- **$k$-divisible Lucas super Catalan numbers have non-negative coefficients.** Let $\{j\}$ be
the Lucas polynomials in $s$ and $t$ ($\{0\} = 0$, $\{1\} = 1$, $\{j+2\} = s\{j+1\} + t\{j\}$)
and let $\{n : k\}! = \{k\}\{2k\} \cdots \{nk\}$ be the $k$-divisible Lucas factorial. For all
natural numbers $k$, $m$ and $n$ with $k \ge 1$ there is a polynomial $p \in \mathbb{Z}[s, t]$
with non-negative coefficients such that
$$p \, \{m : k\}! \, \{n : k\}! \, \{m+n : k\}! = \{2m : k\}! \, \{2n : k\}!;$$
that is, the $k$-divisible lucanomial analogue
$S\{m, n : k\} = \{2m : k\}! \, \{2n : k\}!/(\{m : k\}! \, \{n : k\}! \, \{m+n : k\}!)$ of the
super Catalan numbers is a polynomial in $s$ and $t$ with non-negative integer coefficients.

Source: Kendra Killpatrick, "Super FiboCatalan Numbers and
Their Lucas Analogues", Theorem 13. -/
theorem_wanted exists_nonneg_poly_kDivLucasCatalan
    (k m n : ℕ) (hk : 1 ≤ k) :
    ∃ p : MvPolynomial (Fin 2) ℤ,
      (∀ σ : Fin 2 →₀ ℕ, 0 ≤ p.coeff σ) ∧
      p * (lucasKDivFactorial k m * lucasKDivFactorial k n *
          lucasKDivFactorial k (m + n)) =
        lucasKDivFactorial k (2 * m) * lucasKDivFactorial k (2 * n)

/-- **Theorem 1** (Sagan and Tirrell, Theorem 1.1, quoted): for
`f = ∏ {n_i}` and `g = ∏ {k_j}` with positive indices, whose
decompositions into the Lucas atoms `P_d` (`{n} = ∏_{d ∣ n} P_d`)
have exponents `a_d = #{i : d ∣ n_i}` and `b_d = #{j : d ∣ k_j}`,
`f/g` is a polynomial iff `a_d ≥ b_d` for all `d ≥ 2`; in that
case `f/g` has non-negative integer coefficients. The criterion
involves only the exponents, so the atoms do not appear.

Source: Kendra Killpatrick, *Super FiboCatalan Numbers and Their
Lucas Analogues*, Journal of Integer Sequences 28 (2025), Article
25.5.8, Theorem 1. -/
theorem_wanted lucasPoly_prod_quotient_iff
    (ns ks : List ℕ) (hns : ∀ n ∈ ns, 1 ≤ n) (hks : ∀ k ∈ ks, 1 ≤ k) :
    ((∃ q : MvPolynomial (Fin 2) ℤ,
        q * (ks.map lucasPoly).prod = (ns.map lucasPoly).prod) ↔
      ∀ d, 2 ≤ d → ks.countP (fun k => d ∣ k) ≤ ns.countP (fun n => d ∣ n)) ∧
    ∀ q : MvPolynomial (Fin 2) ℤ,
      q * (ks.map lucasPoly).prod = (ns.map lucasPoly).prod →
        ∀ σ : Fin 2 →₀ ℕ, 0 ≤ q.coeff σ

/-- **Lemma 2** (Sagan and Tirrell, Lemma 3.1, quoted): for
`d ≥ 2`, `log_d {n}! = ⌊n/d⌋`, i.e. `P_d^{⌊n/d⌋}` exactly divides
`{n}!`, where `P` is the Lucas atoms (`{n} = ∏_{d ∣ n} P_d` for
`n ≥ 1`); and
`⌊m/d⌋ + ⌊n/d⌋ ≤ ⌊(m+n)/d⌋` for integers `m`, `n`, `d`.

Source: Kendra Killpatrick, *Super FiboCatalan Numbers and Their
Lucas Analogues*, Journal of Integer Sequences 28 (2025), Article
25.5.8, Lemma 2. -/
theorem_wanted lucasAtom_pow_dvd_lucasFactorial (P : ℕ → MvPolynomial (Fin 2) ℤ)
    (hP : ∀ n, 1 ≤ n → lucasPoly n = ∏ d ∈ n.divisors, P d) :
    (∀ d n : ℕ, 2 ≤ d →
      P d ^ (n / d) ∣ lucasFactorial n ∧ ¬ P d ^ (n / d + 1) ∣ lucasFactorial n) ∧
    ∀ m n d : ℤ, ⌊(m : ℚ) / d⌋ + ⌊(n : ℚ) / d⌋ ≤ ⌊((m + n : ℤ) : ℚ) / d⌋

end MathlibExt.NumberTheory.SuperFibocatalanWanted
