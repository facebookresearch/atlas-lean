/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.LucasSequence
public import WantedExt.NumberTheory.SecondOrderGenFunIntegerValuesWanted

/-!
# Binomial sums involving `U_n = p U_{n-1} + U_{n-2}` and `V_n = p V_{n-1} + V_{n-2}`

Statements from John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly
Recurrent Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64.

The paper's sequences `U_0 = 0`, `U_1 = 1`, `V_0 = 2`, `V_1 = p`, `X_n = p X_{n-1} + X_{n-2}` are
the Lucas sequences `U(p, -1)` and `V(p, -1)`, written `lucasU ⟨p, -1, _⟩` and
`lucasV ⟨p, -1, _⟩`. Section 3 sums over negative indices; there `U` and `V` are the two-sided
sequences `secondOrderBiSeq p 0 1` and `secondOrderBiSeq p 2 p` (same initial values and the same
recurrence on all of `ℤ`). The paper leaves the parameter `p` unrestricted; the statements take
`p` an arbitrary integer. `C_n` is the Catalan number `catalan n`, and `Δ = p² + 4`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `∑_{k=0}^{2n} binom(2n, k)² (-1)^k U_{2n-k} V_k = (-1)^n binom(2n, n) U_{2n}`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Theorem 2.1. -/
public theorem_wanted lucasU_lucasV_sum_choose_sq_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((2 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- Dixon-type analogue: `∑_{k=0}^{2n} binom(2n, k)³ (-1)^k U_{2n-k} V_k =
(-1)^n binom(3n; n, n, n) U_{2n}`, with the trinomial coefficient written as
`binom(3n, n) binom(2n, n)`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Theorem 2.2. -/
public theorem_wanted lucasU_lucasV_sum_choose_cube_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 3 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((3 * n).choose n * (2 * n).choose n : ℕ) * lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{n} binom(n, k)² U_{n-k} V_k = binom(2n, n) U_n`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.3. -/
public theorem_wanted lucasU_lucasV_sum_choose_sq (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℤ) ^ 2 * lucasU ⟨p, -1, by decide⟩ (n - k) * lucasV ⟨p, -1, by decide⟩ k =
      ((2 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{n} C_{2n-2k} C_{2k} U_k V_{n-k} = 2^{2n-1} (n + 2)/(2n + 1) C_{n+1} U_n`, over `ℚ`
(with `2^{2n-1}` written `2^{2n}/2`).

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.4. -/
public theorem_wanted lucasU_lucasV_sum_catalan_even (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (catalan (2 * n - 2 * k) * catalan (2 * k) : ℚ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      (2 : ℚ) ^ (2 * n) / 2 * ((n + 2 : ℚ) / (2 * n + 1)) * catalan (n + 1) *
        lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{n} C_{n-k+m} C_{k+m} U_k V_{n-k} =
2 binom(2m-1, m) (n+m+2)(n+1) / ((n+2m+1)(n+2m+2)) C_{n+m+1} U_n`, over `ℚ`, for `m ≥ 1`.
The paper states `m ∈ ℕ₀`; at `m = 0` the printed right side is twice the sum
(`p = 1`, `n = 1`: the sum is `2`, the printed right side is `4`), so `m = 0` is excluded.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.5. -/
public theorem_wanted lucasU_lucasV_sum_catalan_shifted (p : ℤ) (n m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range (n + 1),
        (catalan (n - k + m) * catalan (k + m) : ℚ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      2 * ((2 * m - 1).choose m : ℚ) *
          (((n + m + 2) * (n + 1) : ℚ) / ((n + 2 * m + 1) * (n + 2 * m + 2))) *
        catalan (n + m + 1) * lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{n} binom(2n, k) binom(2n, n+k) U_k V_{n-k} = binom(4n, n) U_n`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.6. -/
public theorem_wanted lucasU_lucasV_sum_choose_two_n (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((2 * n).choose k * (2 * n).choose (n + k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      ((4 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{2n} binom(2n, k) binom(4n, 2k) (-1)^k U_k V_{2n-k} =
(-1)^n binom(6n, 2n) binom(2n, n) binom(3n, n)⁻¹ U_{2n}`, over `ℚ`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.7. -/
public theorem_wanted lucasU_lucasV_sum_choose_four_n_even_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k * (4 * n).choose (2 * k) : ℚ) * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (2 * n - k) =
      (-1) ^ n * ((6 * n).choose (2 * n) * (2 * n).choose n : ℚ) / (3 * n).choose n *
        lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{2n} binom(2n, k) binom(4n, k) binom(4n, 2n+k) (-1)^k U_k V_{2n-k} =
(-1)^n binom(2n, n) binom(5n, 2n) U_{2n}`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.8. -/
public theorem_wanted lucasU_lucasV_sum_choose_triple_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k * (4 * n).choose k * (4 * n).choose (2 * n + k) : ℤ) * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (2 * n - k) =
      (-1) ^ n * ((2 * n).choose n * (5 * n).choose (2 * n) : ℤ) *
        lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{2n} binom(2n, k) binom(4n, k)⁻¹ binom(4n, 2n+k)⁻¹ (-1)^k U_k V_{2n-k} =
(4n + 1)/(3n + 1) binom(4n, 2n)⁻¹ U_{2n}`, over `ℚ`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.9. -/
public theorem_wanted lucasU_lucasV_sum_choose_inv_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℚ) / ((4 * n).choose k * (4 * n).choose (2 * n + k)) * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (2 * n - k) =
      (4 * n + 1 : ℚ) / (3 * n + 1) / (4 * n).choose (2 * n) * lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{n} binom(n, k) binom(2n, n+k) binom(n+k, k) U_k V_{n-k} = binom(2n, n)² U_n`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.10. -/
public theorem_wanted lucasU_lucasV_sum_choose_n_plus_k (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k * (2 * n).choose (n + k) * (n + k).choose k : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      ((2 * n).choose n : ℤ) ^ 2 * lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{n} binom(2n, 2k) C_k C_{n-k} U_{n-k} V_k = C_n C_{n+1} U_n`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023,
Proposition 2.11. -/
public theorem_wanted lucasU_lucasV_sum_choose_catalan (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((2 * n).choose (2 * k) * catalan k * catalan (n - k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ (n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (catalan n * catalan (n + 1) : ℤ) * lucasU ⟨p, -1, by decide⟩ n

/-- `∑_{k=0}^{2n} (-1)^k binom(4n, 2k) C_k C_{2n-k} U_{2n-k} V_k = (-1)^n C_n C_{2n} U_{2n}`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023,
Proposition 2.12. -/
public theorem_wanted lucasU_lucasV_sum_choose_catalan_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        (-1) ^ k * ((4 * n).choose (2 * k) * catalan k * catalan (2 * n - k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * (catalan n * catalan (2 * n) : ℤ) * lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{2n} (-1)^k binom(2n, k) binom(4n, 2k) C_k C_{2n-k} U_{2n-k} V_k =
(-1)^n binom(3n+1, n) C_n C_{2n} U_{2n}`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023,
Proposition 2.13. -/
public theorem_wanted lucasU_lucasV_sum_choose_sq_catalan_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        (-1) ^ k *
            ((2 * n).choose k * (4 * n).choose (2 * k) * catalan k * catalan (2 * n - k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((3 * n + 1).choose n * catalan n * catalan (2 * n) : ℤ) *
        lucasU ⟨p, -1, by decide⟩ (2 * n)

/-- `∑_{k=0}^{4n+1} binom(4n+1, k) (-1)^{binom(k, 2)} U_k V_{4n+1-k} =
∑_{k=0}^{4n+1} binom(4n+1, k) (-1)^{binom(k, 2)} V_k U_{4n+1-k} = (-1)^n 2^{2n+1} U_{4n+1}`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 3.1. -/
public theorem_wanted lucasU_lucasV_sum_choose_sign_choose_two (p : ℤ) (n : ℕ) :
    (∑ k ∈ Finset.range (4 * n + 2),
        ((4 * n + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (4 * n + 1 - k) =
      (-1) ^ n * 2 ^ (2 * n + 1) * lucasU ⟨p, -1, by decide⟩ (4 * n + 1)) ∧
    ∑ k ∈ Finset.range (4 * n + 2),
        ((4 * n + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
          lucasV ⟨p, -1, by decide⟩ k * lucasU ⟨p, -1, by decide⟩ (4 * n + 1 - k) =
      (-1) ^ n * 2 ^ (2 * n + 1) * lucasU ⟨p, -1, by decide⟩ (4 * n + 1)

/-- For `n > 0` and integers `m, r`, with the two-sided sequences `U = secondOrderBiSeq p 0 1`,
`V = secondOrderBiSeq p 2 p` and `Δ = p² + 4`:
`∑_{k=-n}^{n} binom(2n, n+k) U_{k+m} U_{k+r} = Δ^{n-1} V_{m+r}`,
`∑_{k=-n}^{n} binom(2n, n+k) V_{k+m} V_{k+r} = Δ^n V_{m+r}`, and
`∑_{k=-n}^{n} binom(2n, n+k) X_{k+m} X̄_{k+r} = Δ^n U_{m+r}` for `(X, X̄) = (U, V)` and `(V, U)`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 3.2. -/
public theorem_wanted secondOrderBiSeq_sum_central_choose_mul (p : ℤ) (n : ℕ) (hn : 0 < n)
    (m r : ℤ) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 0 1 (k + r) =
      (p ^ 2 + 4) ^ (n - 1) * secondOrderBiSeq p 2 p (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 2 p (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 2 p (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 2 p (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 0 1 (m + r)) ∧
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 0 1 (k + r) =
      (p ^ 2 + 4) ^ n * secondOrderBiSeq p 0 1 (m + r)

/-- For `n > 0` and integers `m, r`, with `U`, `V`, `Δ` as in Proposition 3.2:
`∑_{k=-n}^{n} binom(2n, n+k) k U_{k+m} U_{k+r} = n p Δ^{n-1} U_{m+r}`,
`∑_{k=-n}^{n} binom(2n, n+k) k V_{k+m} V_{k+r} = n p Δ^n U_{m+r}`, and
`∑_{k=-n}^{n} binom(2n, n+k) k X_{k+m} X̄_{k+r} = n p Δ^{n-1} V_{m+r}` for `(X, X̄) = (U, V)` and
`(V, U)`.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 3.3. -/
public theorem_wanted secondOrderBiSeq_sum_central_choose_mul_weighted (p : ℤ) (n : ℕ)
    (hn : 0 < n) (m r : ℤ) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 0 1 (k + r) * k =
      n * p * (p ^ 2 + 4) ^ (n - 1) * secondOrderBiSeq p 0 1 (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 2 p (k + r) * k =
      n * p * (p ^ 2 + 4) ^ n * secondOrderBiSeq p 0 1 (m + r)) ∧
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 0 1 (k + m) * secondOrderBiSeq p 2 p (k + r) * k =
      n * p * (p ^ 2 + 4) ^ (n - 1) * secondOrderBiSeq p 2 p (m + r)) ∧
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
        secondOrderBiSeq p 2 p (k + m) * secondOrderBiSeq p 0 1 (k + r) * k =
      n * p * (p ^ 2 + 4) ^ (n - 1) * secondOrderBiSeq p 2 p (m + r)

end

end MetaMathlibExt
