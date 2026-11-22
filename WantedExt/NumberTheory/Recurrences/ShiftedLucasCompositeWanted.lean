/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-! # Shifting Lucas sequences away from primes

Composite values of Lucas sequences `U_n(P, Q)` and of their unit shifts. An integer `m` is
composite when `1 < m` and `m` is not prime.
-/

/-- The Lucas sequence `U_n(3, -4) = 0, 1, 3, 13, 51, 205, 819, …` is composite for every
`n ≥ 4`.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 1
(`integers-2025-A42-thm-1`). -/
public theorem_wanted lucasU_three_neg_four_composite {n : ℕ} (hn : 4 ≤ n) :
    1 < lucasU ⟨3, -4, by decide⟩ n ∧ ¬ (lucasU ⟨3, -4, by decide⟩ n).natAbs.Prime

/-- For `P ≥ 3` and `Q = 1`, for all but finitely many `n` the three integers
`U_n(P, 1) - 1`, `U_n(P, 1)` and `U_n(P, 1) + 1` are all composite.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 2
(`integers-2025-A42-thm-2`). -/
public theorem_wanted lucasU_q_one_shifts_eventually_composite {P : ℤ} (hP : 3 ≤ P) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < lucasU ⟨P, 1, by decide⟩ n + d ∧ ¬ (lucasU ⟨P, 1, by decide⟩ n + d).natAbs.Prime

/-- For `P ≥ 1` and `Q = -1` there is a positive integer `K` such that
`U_n(P, -1) + K - 1`, `U_n(P, -1) + K` and `U_n(P, -1) + K + 1` are composite for every
`n ≥ 0`.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 3
(`integers-2025-A42-thm-3`). -/
public theorem_wanted exists_shift_lucasU_q_neg_one_composite {P : ℤ} (hP : 1 ≤ P) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < lucasU ⟨P, -1, by decide⟩ n + K + d ∧
        ¬ (lucasU ⟨P, -1, by decide⟩ n + K + d).natAbs.Prime

/-- If `P ≥ 1`, `P² - 4Q > 0` and `Q ≠ 0` is a perfect square, then `U_n(P, Q)` is prime
for only finitely many `n`.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(a)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem_wanted lucasU_square_q_finite_primes {P Q : ℤ} (hQ : Q ≠ 0) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) (hsq : IsSquare Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite

/-- Let `x ≠ y` be real numbers with `x + y` and `x y` integers, and let `r > 1`. If
`P = x ^ r + y ^ r` and `Q = x ^ r y ^ r ≠ 0` satisfy `P ≥ 1` and `P² - 4Q > 0`, then
`U_n(P, Q)` is prime for only finitely many `n`.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(b)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem_wanted lucasU_power_params_finite_primes {x y : ℝ} (hxy : x ≠ y) {a b : ℤ}
    (hs : x + y = a) (hp : x * y = b) {r : ℕ} (hr : 1 < r) {P Q : ℤ} (hQ : Q ≠ 0)
    (hPdef : (P : ℝ) = x ^ r + y ^ r) (hQdef : (Q : ℝ) = x ^ r * y ^ r) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite

/-- `F_n + 14475` is composite for every `n ≥ 0`.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 5
(`integers-2025-A42-thm-5`). -/
public theorem_wanted fib_add_14475_not_prime (n : ℕ) : ¬ (Nat.fib n + 14475).Prime

end

end MetaMathlibExt
