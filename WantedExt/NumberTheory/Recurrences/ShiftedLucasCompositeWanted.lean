/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.LucasQOneShiftComposite
public import MathlibExt.NumberTheory.Recurrences.ShiftedLucasComposite
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-! # Shifting Lucas sequences away from primes

Composite values of Lucas sequences `U_n(P, Q)` and of their unit shifts. An integer `m` is
composite when `1 < m` and `m` is not prime.
-/

/-- **A shift of $U_n(P, -1)$ away from primes.** Let $P \ge 1$ be an integer and let
$U_n = U_n(P, -1)$ be the Lucas sequence with $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = PU_{n+1} + U_n$. Then there is an integer $K > 0$ such that for every natural
number $n$ the three integers $U_n + K - 1$, $U_n + K$ and $U_n + K + 1$ are all composite,
that is, each is greater than $1$ and not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 3
(`integers-2025-A42-thm-3`). -/
public theorem_wanted exists_shift_lucasU_q_neg_one_composite {P : ℤ} (hP : 1 ≤ P) :
    ∃ K : ℤ, 0 < K ∧ ∀ n : ℕ, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < lucasU ⟨P, -1, by decide⟩ n + K + d ∧
        ¬ (lucasU ⟨P, -1, by decide⟩ n + K + d).natAbs.Prime

/-- **Lucas sequences with square $Q$ have finitely many prime terms.** Let $P$ and $Q$ be
integers with $P \ge 1$ and $P^2 - 4Q > 0$, where $Q \ne 0$ is a perfect square, and let
$U_n = U_n(P, Q)$ be the Lucas sequence with $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = PU_{n+1} - QU_n$. Then $|U_n|$ is prime for only finitely many natural
numbers $n$.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(a)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem_wanted lucasU_square_q_finite_primes {P Q : ℤ} (hQ : Q ≠ 0) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) (hsq : IsSquare Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite

/-- **Lucas sequences with power parameters have finitely many prime terms.** Let $x \ne y$
be real numbers such that $x + y$ and $xy$ are integers, and let $r > 1$ be a natural
number. Let $P$ and $Q$ be integers with $P = x^r + y^r$ and $Q = x^r y^r$, and suppose
$Q \ne 0$, $P \ge 1$ and $P^2 - 4Q > 0$. Let $U_n = U_n(P, Q)$ be the Lucas sequence with
$U_0 = 0$, $U_1 = 1$ and $U_{n+2} = PU_{n+1} - QU_n$. Then $|U_n|$ is prime for only
finitely many natural numbers $n$.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(b)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem_wanted lucasU_power_params_finite_primes {x y : ℝ} (hxy : x ≠ y) {a b : ℤ}
    (hs : x + y = a) (hp : x * y = b) {r : ℕ} (hr : 1 < r) {P Q : ℤ} (hQ : Q ≠ 0)
    (hPdef : (P : ℝ) = x ^ r + y ^ r) (hQdef : (Q : ℝ) = x ^ r * y ^ r) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite

end

end MetaMathlibExt
