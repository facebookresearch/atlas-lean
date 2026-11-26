/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.LucasPowerParamsFinitePrimes
public import MathlibExt.NumberTheory.Recurrences.LucasQOneShiftComposite
public import MathlibExt.NumberTheory.Recurrences.LucasSquareQFinitePrimes
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

end

end MetaMathlibExt
