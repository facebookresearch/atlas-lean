/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fibonacci numbers via Dirichlet convolution

Statements from Emil Daniel Schwab, "Fibonacci
Numbers via Dirichlet Convolution and Lucas Numbers
via Unitary Convolution", *Journal of Integer
Sequences* 28 (2025), Article 25.1.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schwab/schwab3.html>).

`fibAB a b` and `lucasAB a b` are the paper's
`F^{a, b}` and `L^{a, b}` over `ℂ` (`F_0 = 0`,
`F_1 = 1`, `L_0 = 2`, `L_1 = a`, both with recurrence
`s_{n+2} = a s_{n+1} + b s_n`; at integer parameters
these are the Lucas sequences `U(a, -b)`, `V(a, -b)`).
Every identity below was verified numerically over
random complex parameters. In Theorem 10,
`Δ = a^2 + 4b`; parts (b), (c), (d) are the
Fibonacci `(1, 1)`, Pell `(2, 1)` and Jacobsthal
`(1, 2)` specializations.

Theorem 3 uses the multiplicative arithmetic functions
`𝓕_{a,b} = α^Ω ∗ β^Ω` (Dirichlet) and `𝓛_{a,b} = α^Ω ⊔ β^Ω`
(unitary convolution), built from the MathlibExt API
`MetaMathlibExt.powOmega`, `MetaMathlibExt.unitaryConv` and
`MetaMathlibExt.multiplicativeOfPrimePowers`, with `α, β` the roots
of `x² - ax - b`; `horadamAB a b r s` is Horadam's
`H_m^{a,b}(r, s)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
public import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentities
public import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionLucasABFibAB

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

open MetaMathlibExt (powOmega unitaryConv multiplicativeOfPrimePowers)

/-- **Sums of (a, b)-Lucas numbers weighted by powers of -b.** Let $a, b$ be complex numbers
with $b \ne 0$, and let $(F_n)$ and $(L_n)$ be the $(a, b)$-Fibonacci and $(a, b)$-Lucas
numbers. Then for every integer $n \ge 0$,
$$\sum_{i=0}^{n} (-b)^{n-i} L_{2i+1} = F_{2n+2}
\quad\text{and}\quad \sum_{i=0}^{n} (-b)^{n-i} L_{2i} = F_{2n+1} + (-b)^n.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 5(a). -/
theorem_wanted sum_neg_b_pow_lucasAB (a b : ℂ) (hb : b ≠ 0)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * i + 1) =
      fibAB a b (2 * n + 2)) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * i) =
      fibAB a b (2 * n + 1) + (-b) ^ n)

/-- **Shifted sums of (a, b)-Lucas numbers weighted by powers of -b.** Let $a, b$ be complex
numbers with $b \ne 0$, and let $(F_n)$ and $(L_n)$ be the $(a, b)$-Fibonacci and
$(a, b)$-Lucas numbers. Then for all integers $m, n \ge 0$,
$$\sum_{i=0}^{n} (-b)^{n-i} L_{2(i+m)+1} = F_{2(n+m)+2} + (-1)^n b^{n+1} F_{2m},$$
and this sum also equals $F_{n+m+1} L_{n+m+1} + (-1)^n b^{n+1} F_m L_m$. If moreover $m \ge 1$,
then
$$\sum_{i=0}^{n} (-b)^{n-i} L_{2(i+m)} = F_{2(n+m)+1} + (-1)^n b^{n+1} F_{2m-1},$$
and this sum also equals $F_{n+m+1} L_{n+m} + (-1)^n b^{n+1} F_m L_{m-1}$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 5(b). -/
theorem_wanted sum_neg_b_pow_lucasAB_shift (a b : ℂ) (hb : b ≠ 0)
    (m n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * (i + m) + 1) =
      fibAB a b (2 * (n + m) + 2) +
        (-1) ^ n * b ^ (n + 1) * fibAB a b (2 * m) ∧
    ∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * (i + m) + 1) =
      fibAB a b (n + m + 1) * lucasAB a b (n + m + 1) +
        (-1) ^ n * b ^ (n + 1) * fibAB a b m * lucasAB a b m) ∧
    (1 ≤ m →
      ∑ i ∈ Finset.range (n + 1),
          (-b) ^ (n - i) * lucasAB a b (2 * (i + m)) =
        fibAB a b (2 * (n + m) + 1) +
          (-1) ^ n * b ^ (n + 1) * fibAB a b (2 * m - 1) ∧
      ∑ i ∈ Finset.range (n + 1),
          (-b) ^ (n - i) * lucasAB a b (2 * (i + m)) =
        fibAB a b (n + m + 1) * lucasAB a b (n + m) +
          (-1) ^ n * b ^ (n + 1) * fibAB a b m * lucasAB a b (m - 1))

/-- **Alternating sums of Fibonacci and Lucas numbers.** Let $(F_n)$ and $(L_n)$ be the
Fibonacci and Lucas numbers, that is, the $(1, 1)$-Fibonacci and $(1, 1)$-Lucas numbers, viewed
as complex numbers. Then for every integer $n \ge 0$,
$$\sum_{i=0}^{n} (-1)^i F_{2i} = \frac{(-1)^n L_{2n+1} - 1}{5}, \qquad
\sum_{i=0}^{n} (-1)^i L_{2i} = (-1)^n F_{2n+1} + 1,$$
$$\sum_{i=0}^{n} (-1)^i F_{2i+1} = \frac{(-1)^n L_{2n+2} + 2}{5}, \qquad
\sum_{i=0}^{n} (-1)^i L_{2i+1} = (-1)^n F_{2n+2}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(b). -/
theorem_wanted sum_neg_one_pow_fib (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * fibAB 1 1 (2 * i) =
      ((-1) ^ n * lucasAB 1 1 (2 * n + 1) - 1) / 5) ∧
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * lucasAB 1 1 (2 * i) =
      (-1) ^ n * fibAB 1 1 (2 * n + 1) + 1) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * fibAB 1 1 (2 * i + 1) =
      ((-1) ^ n * lucasAB 1 1 (2 * n + 2) + 2) / 5) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB 1 1 (2 * i + 1) =
      (-1) ^ n * fibAB 1 1 (2 * n + 2))

/-- **Alternating sums of even-indexed k-Lucas numbers.** Let $k$ be a complex number, and let
$(F_{k,n})$ and $(L_{k,n})$ be the $k$-Fibonacci and $k$-Lucas numbers, that is, the
$(k, 1)$-Fibonacci and $(k, 1)$-Lucas numbers. Then for all integers $m \ge 1$ and $n \ge 0$,
$$\sum_{i=0}^{n} (-1)^i L_{k,2(i+m)} = (-1)^n F_{k,2(n+m)+1} + F_{k,2m-1}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 9. -/
theorem_wanted sum_neg_one_pow_k_lucasAB (k : ℂ) (m n : ℕ)
    (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB k 1 (2 * (i + m)) =
      (-1) ^ n * fibAB k 1 (2 * (n + m) + 1) + fibAB k 1 (2 * m - 1)

/-- **Fibonacci, Jacobsthal and Pell convolution identities.** Write $F_n$ and $L_n$ for the
Fibonacci and Lucas numbers (the $(1,1)$-Fibonacci and $(1,1)$-Lucas numbers), $J_n$ and $j_n$
for the Jacobsthal and Jacobsthal–Lucas numbers (the $(1,2)$-Fibonacci and $(1,2)$-Lucas
numbers), and $P_n$ and $Q_n$ for the Pell and Pell–Lucas numbers (the $(2,1)$-Fibonacci and
$(2,1)$-Lucas numbers), all as complex numbers. Then for every natural number $n$:
(i) $\sum_{i=1}^{n} L_{n-i} J_i = j_{n+1} - L_{n+1}$ and
$\sum_{i=1}^{n} j_{n-i} F_i = j_{n+1} - L_{n+1}$;
(ii) $2 \sum_{i=1}^{n} P_i = (Q_{n+1} - 2)/2$ and $\sum_{i=1}^{n} i \, Q_{n-i} = (Q_{n+1} - 2)/2$;
(iii) $\sum_{i=1}^{n} L_{2(n-i)} (2^i - 1) = L_{2n+2} - 2^{n+1} - 1$ and
$\sum_{i=1}^{n} (2^{n-i} + 1) F_{2i} = L_{2n+2} - 2^{n+1} - 1$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 14(b). -/
theorem_wanted convolution_specializations (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, lucasAB 1 1 (n - i) * fibAB 1 2 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1) ∧
      ∑ i ∈ Finset.Icc 1 n, lucasAB 1 2 (n - i) * fibAB 1 1 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1)) ∧
    (2 * ∑ i ∈ Finset.Icc 1 n, fibAB 2 1 i =
        (lucasAB 2 1 (n + 1) - 2) / 2 ∧
      ∑ i ∈ Finset.Icc 1 n, (i : ℂ) * lucasAB 2 1 (n - i) =
        (lucasAB 2 1 (n + 1) - 2) / 2) ∧
    (∑ i ∈ Finset.Icc 1 n,
        lucasAB 1 1 (2 * (n - i)) * (2 ^ i - 1) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1 ∧
      ∑ i ∈ Finset.Icc 1 n, (2 ^ (n - i) + 1) * fibAB 1 1 (2 * i) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1)

/-- **Lemma 6**: `H_m^{a,b}((-b)ⁿ, 0) = (-1)ⁿ b^{n+1} F_{m-1}^{a,b}`,
stated for `m + 1` (every `m ≥ 1`) and, for `b ≠ 0`, at
`m = 0` with the backward value `F_{-1} = 1/b`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Lemma 6. -/
theorem_wanted horadamAB_neg_pow_zero (a b : ℂ) (n : ℕ) :
    (∀ m : ℕ, horadamAB a b ((-b) ^ n) 0 (m + 1) =
        (-1) ^ n * b ^ (n + 1) * fibAB a b m) ∧
      (b ≠ 0 → horadamAB a b ((-b) ^ n) 0 0 = (-1) ^ n * b ^ (n + 1) * b⁻¹)

/-- **Theorem 3**: with `α, β` the roots of `x² - ax - b`,
`𝓕_{a,b} = α^Ω ∗ β^Ω`, `𝓛_{a,b} = α^Ω ⊔ β^Ω`, and `±γ` the
roots of `x² + b` (so `𝓕_{0,-b} = γ^Ω ∗ (-γ)^Ω`):
(i) `𝓕_{a,b}(p^m) = F_{m+1}^{a,b}` and `𝓛_{a,b}(p^m) = 1` for
`m = 0`, `L_m^{a,b}` for `m > 0`; (ii) `[𝓕/𝓛]_D = 𝓕_{0,-b}`, as
`𝓕_{a,b} = 𝓛_{a,b} ∗ 𝓕_{0,-b}`, and
`[𝓛/𝓕]_U = 𝓗^{(0)}_{a,b} = μ_a ∗ 𝓕_{a,b}`, as
`𝓛_{a,b} = 𝓕_{a,b} ⊔ 𝓗^{(0)}_{a,b}` and
`𝓗^{(0)}_{a,b} = μ_a ∗ 𝓕_{a,b}`, where
`𝓗^{(0)}_{a,b}(p^m) = H_m^{a,b}(1, 0)` and `μ_a(p^m)` is
`1, -a, 0` for `m = 0, 1, ≥ 2`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Theorem 3. -/
theorem_wanted fibLucas_arithmeticFunction_identities (a b α β γ : ℂ)
    (hsum : α + β = a) (hprod : α * β = -b) (hγ : γ ^ 2 = -b) :
    (∀ p m : ℕ, p.Prime →
        (powOmega α * powOmega β) (p ^ m) = fibAB a b (m + 1) ∧
          unitaryConv (powOmega α) (powOmega β) (p ^ m) =
            if m = 0 then 1 else lucasAB a b m) ∧
      powOmega α * powOmega β =
        unitaryConv (powOmega α) (powOmega β) * (powOmega γ * powOmega (-γ)) ∧
      unitaryConv (powOmega α) (powOmega β) =
        unitaryConv (powOmega α * powOmega β)
          (multiplicativeOfPrimePowers (horadamAB a b 1 0)) ∧
      multiplicativeOfPrimePowers (horadamAB a b 1 0) =
        multiplicativeOfPrimePowers (fun m => if m = 0 then 1 else if m = 1 then -a else 0) *
          (powOmega α * powOmega β)

/-- **Theorem 13**: for the roots `α, β` of `x² - ax - b`,
neither a zero of `x² - cx - d`,
`∑_{i=1}^n L_{n-i}^{a,b} F_i^{c,d} =
(α^{n+1} - α F_{n+1}^{c,d} - d F_n^{c,d})/(α² - cα - d) +
(β^{n+1} - β F_{n+1}^{c,d} - d F_n^{c,d})/(β² - cβ - d)`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Theorem 13. -/
theorem_wanted sum_lucasAB_mul_fibAB (a b c d α β : ℂ) (hsum : α + β = a)
    (hprod : α * β = -b) (hα : α ^ 2 - c * α - d ≠ 0) (hβ : β ^ 2 - c * β - d ≠ 0)
    (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB c d i =
      (α ^ (n + 1) - α * fibAB c d (n + 1) - d * fibAB c d n) / (α ^ 2 - c * α - d) +
        (β ^ (n + 1) - β * fibAB c d (n + 1) - d * fibAB c d n) / (β ^ 2 - c * β - d)

/-- **Theorem 15** (Szakács): `Δ ∑_{i=0}^n F_i F_{n-i} =
(n + 1) L_n - 2 F_{n+1}` with `Δ = a² + 4b`, for the
`(a, b)`-Fibonacci and Lucas numbers. The paper's
hypothesis `Δ ≠ 0` is dropped: at `Δ = 0` both sides
vanish.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Theorem 15, quoting
T. Szakács, "Convolution of second order linear
recursive sequences II", Communications in
Mathematics 25 (2017), 137–148, Theorem 4. -/
theorem_wanted disc_mul_sum_fibAB_mul_fibAB (a b : ℂ) (n : ℕ) :
    (a ^ 2 + 4 * b) * ∑ i ∈ Finset.range (n + 1), fibAB a b i * fibAB a b (n - i) =
      (n + 1) * lucasAB a b n - 2 * fibAB a b (n + 1)

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted
