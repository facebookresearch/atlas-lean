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

/-- The self-convolution of the Oresme numbers `O_n = n/2^n`:
`∑_{k=0}^n O_k O_{n-k} = (n+1) n (n-1) / (6 · 2^n)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 2.1 (`fq-2024-cookbacon061124-prop-2.1`). -/
public theorem_wanted oresme_convolution_self (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℚ) / 2 ^ k) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      ((n : ℚ) + 1) * n * ((n : ℚ) - 1) / (6 * 2 ^ n)

/-- The Fibonacci–Oresme convolution:
`∑_{k=0}^n F_k O_{n-k} = (2/5) F_{n+1} - 2(n+1)/(5 · 2^n)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.1 (`fq-2024-cookbacon061124-prop-4.1`). -/
public theorem_wanted fib_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.fib k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (Nat.fib (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (5 * 2 ^ n)

/-- `2^{n-1} F_n ≡ n (mod 5)` for every `n ≥ 0` (at `n = 0` both sides vanish, so the
truncated exponent `0 - 1 = 0` is harmless).

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.2 (`fq-2024-cookbacon061124-cor-4.2`). -/
public theorem_wanted two_pow_pred_mul_fib_modEq_five (n : ℕ) :
    2 ^ (n - 1) * Nat.fib n ≡ n [MOD 5]

/-- The Lucas–Oresme convolution:
`∑_{k=0}^n L_k O_{n-k} = (2/5) L_{n+1} - 2/(5 · 2^n)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.3 (`fq-2024-cookbacon061124-prop-4.3`). -/
public theorem_wanted lucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (lucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (lucasNumber (n + 1) : ℚ) - 2 / (5 * 2 ^ n)

/-- `2^n L_{n+1} ≡ 1 (mod 5)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.4 (`fq-2024-cookbacon061124-cor-4.4`). -/
public theorem_wanted two_pow_mul_lucasNumber_succ_modEq_five (n : ℕ) :
    2 ^ n * lucasNumber (n + 1) ≡ 1 [MOD 5]

/-- The Pell–Oresme convolution:
`∑_{k=0}^n P_k O_{n-k} = (2/49)(5 P_{n+1} - 4 P_n) - (2/49)(7n+5)/2^n` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.2 (`fq-2024-cookbacon061124-prop-5.2`). -/
public theorem_wanted pellNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (pellNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellNumber (n + 1) : ℚ) - 4 * pellNumber n) -
        2 / 49 * ((7 * (n : ℚ) + 5) / 2 ^ n)

/-- `2^n (5 P_{n+1} - 4 P_n) ≡ 7n + 5 (mod 49)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.3 (`fq-2024-cookbacon061124-cor-5.3`). -/
public theorem_wanted two_pow_mul_pellNumber_combination_modEq (n : ℕ) :
    2 ^ n * (5 * (pellNumber (n + 1) : ℤ) - 4 * pellNumber n) ≡ 7 * n + 5 [ZMOD 49]

/-- The Pell–Lucas–Oresme convolution, for the odd Pell–Lucas numbers `Q_0 = Q_1 = 1`:
`∑_{k=0}^n Q_k O_{n-k} = (2/49)(5 Q_{n+1} - 4 Q_n) + (1/49)(7n-2)/2^n` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.4 (`fq-2024-cookbacon061124-prop-5.4`). -/
public theorem_wanted pellLucasSequence_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (pellLucasSequence k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellLucasSequence (n + 1) : ℚ) - 4 * pellLucasSequence n) +
        1 / 49 * ((7 * (n : ℚ) - 2) / 2 ^ n)

/-- `2^{n+1} (5 Q_{n+1} - 4 Q_n) ≡ 2 - 7n (mod 49)` for every `n ≥ 0`, with the odd
Pell–Lucas numbers `Q_0 = Q_1 = 1`. The paper prints `2^{n+1}(5Q_{n+1} - 4Q_n) ≡ (2 - 7n) ≡ 0`;
its proof (base values `2` and `44` on both sides, inductive hypothesis
`2^{n+1}(5Q_{n+1} - 4Q_n) - (2 - 7n) ≡ 0`) establishes this single congruence, while the
second link `2 - 7n ≡ 0 (mod 49)` fails at `n = 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.5 (`fq-2024-cookbacon061124-cor-5.5`). -/
public theorem_wanted two_pow_succ_mul_pellLucasSequence_combination_modEq (n : ℕ) :
    2 ^ (n + 1) * (5 * (pellLucasSequence (n + 1) : ℤ) - 4 * pellLucasSequence n) ≡
      2 - 7 * n [ZMOD 49]

/-- The Jacobsthal–Oresme convolution, with `J = lucasU (1, -2)`:
`∑_{k=0}^n J_k O_{n-k} = (2/9) J_{n+1} - 2(n+1)/(9 · 2^n)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.2 (`fq-2024-cookbacon061124-prop-6.2`). -/
public theorem_wanted jacobsthal_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (9 * 2 ^ n)

/-- `2^n J_{n+1} ≡ n + 1 (mod 9)` for every `n ≥ 0`, with `J = lucasU (1, -2)`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.3 (`fq-2024-cookbacon061124-cor-6.3`). -/
public theorem_wanted two_pow_mul_jacobsthal_succ_modEq_nine (n : ℕ) :
    2 ^ n * lucasU ⟨1, -2, by decide⟩ (n + 1) ≡ n + 1 [ZMOD 9]

/-- The Jacobsthal–Lucas–Oresme convolution, `j_0 = 2`, `j_1 = 1`:
`∑_{k=0}^n j_k O_{n-k} = (2/9) j_{n+1} - 2/(9 · 2^n)` for every `n ≥ 0`. The paper prints
`+` where the relation sign belongs (`∑ j_k O_{n-k} + (2/9) j_{n+1} - 2/(9 · 2^n)`, with no
relation); this is the `=` reading, matching Propositions 4.3 and 6.2 and Corollary 6.5.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.4 (`fq-2024-cookbacon061124-prop-6.4`). -/
public theorem_wanted jacobsthalLucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (jacobsthalLucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (jacobsthalLucasNumber (n + 1) : ℚ) - 2 / (9 * 2 ^ n)

/-- `2^n j_{n+1} ≡ 1 (mod 9)` for every `n ≥ 0`.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.5 (`fq-2024-cookbacon061124-cor-6.5`). -/
public theorem_wanted two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n : ℕ) :
    2 ^ n * jacobsthalLucasNumber (n + 1) ≡ 1 [MOD 9]

end

end MetaMathlibExt
