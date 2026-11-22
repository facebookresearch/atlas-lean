/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.JacobsthalLucasNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Cauchy convolutions with Oresme numbers

Statements from M. R. Bacon and C. K. Cook on the Cauchy convolutions
`∑_{k=0}^n a_k O_{n-k}` of the Oresme numbers `O_n = n/2^n` (the closed form of
Definition 1.1) with the Fibonacci, Lucas, Pell, Pell–Lucas, Jacobsthal and
Jacobsthal–Lucas numbers, and the congruences read off from them. The Oresme numbers are
written inline as `n / 2^n` over `ℚ`. The paper's Pell–Lucas numbers are the odd sequence
`Q_0 = Q_1 = 1` (`pellLucasSequence`), its Jacobsthal numbers are `lucasU (1, -2)`, and its
Jacobsthal–Lucas numbers `j_0 = 2, j_1 = 1` are `jacobsthalLucasNumber`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Self-convolution of the Oresme numbers.** Let $O_m = m/2^m$ denote the Oresme numbers. For
every natural number $n$, $\sum_{k=0}^{n} O_k O_{n-k} = \frac{(n+1) n (n-1)}{6 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 2.1 (`fq-2024-cookbacon061124-prop-2.1`). -/
public theorem_wanted oresme_convolution_self (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℚ) / 2 ^ k) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      ((n : ℚ) + 1) * n * ((n : ℚ) - 1) / (6 * 2 ^ n)

/-- **Fibonacci–Oresme convolution.** Let $F_m$ denote the Fibonacci numbers, with $F_0 = 0$,
$F_1 = 1$ and $F_{m+2} = F_{m+1} + F_m$, and let $O_m = m/2^m$ denote the Oresme numbers. For
every natural number $n$,
$\sum_{k=0}^{n} F_k O_{n-k} = \frac{2}{5} F_{n+1} - \frac{2(n+1)}{5 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.1 (`fq-2024-cookbacon061124-prop-4.1`). -/
public theorem_wanted fib_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.fib k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (Nat.fib (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (5 * 2 ^ n)

/-- **Oresme–Fibonacci congruence modulo 5.** Let $F_n$ denote the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every natural number $n$, $2^{n-1} F_n \equiv n \pmod 5$, where at
$n = 0$ the exponent $n - 1$ is taken to be $0$ (both sides are then $0$).

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.2 (`fq-2024-cookbacon061124-cor-4.2`). -/
public theorem_wanted two_pow_pred_mul_fib_modEq_five (n : ℕ) :
    2 ^ (n - 1) * Nat.fib n ≡ n [MOD 5]

/-- **Lucas–Oresme convolution.** Let $L_m$ denote the Lucas numbers and let $O_m = m/2^m$
denote the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} L_k O_{n-k} = \frac{2}{5} L_{n+1} - \frac{2}{5 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.3 (`fq-2024-cookbacon061124-prop-4.3`). -/
public theorem_wanted lucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (lucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (lucasNumber (n + 1) : ℚ) - 2 / (5 * 2 ^ n)

/-- **Powers of two times Lucas numbers modulo 5.** Let $L_m$ denote the Lucas numbers. For every
natural number $n$, $2^n L_{n+1} \equiv 1 \pmod{5}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.4 (`fq-2024-cookbacon061124-cor-4.4`). -/
public theorem_wanted two_pow_mul_lucasNumber_succ_modEq_five (n : ℕ) :
    2 ^ n * lucasNumber (n + 1) ≡ 1 [MOD 5]

/-- **Pell–Oresme convolution.** Let $P_m$ denote the Pell numbers and let $O_m = m/2^m$ denote
the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} P_k O_{n-k} = \frac{2}{49}(5 P_{n+1} - 4 P_n) - \frac{2(7n + 5)}{49 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.2 (`fq-2024-cookbacon061124-prop-5.2`). -/
public theorem_wanted pellNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (pellNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellNumber (n + 1) : ℚ) - 4 * pellNumber n) -
        2 / 49 * ((7 * (n : ℚ) + 5) / 2 ^ n)

/-- **Oresme–Pell congruence modulo 49.** For every natural number $n$, the Pell numbers $P_n$
satisfy $2^n (5 P_{n+1} - 4 P_n) \equiv 7n + 5 \pmod{49}$ as integers.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.3 (`fq-2024-cookbacon061124-cor-5.3`). -/
public theorem_wanted two_pow_mul_pellNumber_combination_modEq (n : ℕ) :
    2 ^ n * (5 * (pellNumber (n + 1) : ℤ) - 4 * pellNumber n) ≡ 7 * n + 5 [ZMOD 49]

/-- **Pell–Lucas–Oresme convolution.** Let $Q_m$ denote the Pell–Lucas numbers, with
$Q_0 = Q_1 = 1$ and $Q_{m+2} = 2Q_{m+1} + Q_m$, and let $O_m = m/2^m$ denote the Oresme numbers.
For every natural number $n$,
$\sum_{k=0}^{n} Q_k O_{n-k} = \frac{2}{49}(5 Q_{n+1} - 4 Q_n) + \frac{7n - 2}{49 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.4 (`fq-2024-cookbacon061124-prop-5.4`). -/
public theorem_wanted pellLucasSequence_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (pellLucasSequence k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellLucasSequence (n + 1) : ℚ) - 4 * pellLucasSequence n) +
        1 / 49 * ((7 * (n : ℚ) - 2) / 2 ^ n)

/-- **Oresme–Pell–Lucas congruence modulo 49.** Let $Q_n$ denote the Pell–Lucas numbers, with
$Q_0 = Q_1 = 1$. For every natural number $n$,
$2^{n+1} (5 Q_{n+1} - 4 Q_n) \equiv 2 - 7n \pmod{49}$ as integers.

The paper prints $2^{n+1}(5Q_{n+1} - 4Q_n) \equiv 2 - 7n \equiv 0$. Its proof (base values $2$ and
$44$ on both sides, inductive hypothesis $2^{n+1}(5Q_{n+1} - 4Q_n) - (2 - 7n) \equiv 0$)
establishes the single congruence above, while the second link $2 - 7n \equiv 0 \pmod{49}$ fails
at $n = 0$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.5 (`fq-2024-cookbacon061124-cor-5.5`). -/
public theorem_wanted two_pow_succ_mul_pellLucasSequence_combination_modEq (n : ℕ) :
    2 ^ (n + 1) * (5 * (pellLucasSequence (n + 1) : ℤ) - 4 * pellLucasSequence n) ≡
      2 - 7 * n [ZMOD 49]

/-- **Jacobsthal–Oresme convolution.** Let $J_m$ denote the Jacobsthal numbers, the terms of the
Lucas sequence $U(1, -2)$, and let $O_m = m/2^m$ denote the Oresme numbers. For every natural
number $n$,
$\sum_{k=0}^{n} J_k O_{n-k} = \frac{2}{9} J_{n+1} - \frac{2(n+1)}{9 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.2 (`fq-2024-cookbacon061124-prop-6.2`). -/
public theorem_wanted jacobsthal_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (9 * 2 ^ n)

/-- **Powers of two times Jacobsthal numbers modulo 9.** Let $J_m$ denote the Jacobsthal numbers,
the terms of the Lucas sequence $U(1, -2)$. For every natural number $n$,
$2^n J_{n+1} \equiv n + 1 \pmod{9}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.3 (`fq-2024-cookbacon061124-cor-6.3`). -/
public theorem_wanted two_pow_mul_jacobsthal_succ_modEq_nine (n : ℕ) :
    2 ^ n * lucasU ⟨1, -2, by decide⟩ (n + 1) ≡ n + 1 [ZMOD 9]

/-- **Jacobsthal–Lucas–Oresme convolution.** Let $j_m$ denote the Jacobsthal–Lucas numbers and
let $O_m = m/2^m$ denote the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} j_k O_{n-k} = \frac{2}{9} j_{n+1} - \frac{2}{9 \cdot 2^n}$.

The paper prints $+$ where the equality sign belongs, with no relation between the two sides;
this is the equality reading, which matches Propositions 4.3 and 6.2 and Corollary 6.5.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.4 (`fq-2024-cookbacon061124-prop-6.4`). -/
public theorem_wanted jacobsthalLucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (jacobsthalLucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (jacobsthalLucasNumber (n + 1) : ℚ) - 2 / (9 * 2 ^ n)

/-- **Powers of two times Jacobsthal–Lucas numbers modulo 9.** Let $j_m$ denote the
Jacobsthal–Lucas numbers. For every natural number $n$, $2^n j_{n+1} \equiv 1 \pmod{9}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.5 (`fq-2024-cookbacon061124-cor-6.5`). -/
public theorem_wanted two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n : ℕ) :
    2 ^ n * jacobsthalLucasNumber (n + 1) ≡ 1 [MOD 9]

end

end MetaMathlibExt
