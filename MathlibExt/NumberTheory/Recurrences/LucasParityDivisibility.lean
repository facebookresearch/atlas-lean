/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.Ring.Divisibility.Basic

/-! # Divisibility by the first Lucas parameter at indices of fixed parity -/

namespace MetaMathlibExt

/-- **$P$ divides $U_{2n}$, and $V_n$ for odd $n$.** Let $P$ and $Q$ be integers with $Q \ne 0$,
and let $U$ and $V$ be the Lucas sequences $U(P, Q)$ and $V(P, Q)$. Then $P \mid U_{2n}$ for every
natural number $n$, and $P \mid V_n$ for every odd natural number $n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (v), (vi)
(`integers-2025-A107-prop-2-3`). -/
public theorem p_dvd_lucasU_two_mul_and_lucasV_of_odd
    (L : LucasSequenceParams) :
    (∀ n : ℕ, L.p ∣ lucasU L (2 * n)) ∧ ∀ n : ℕ, Odd n → L.p ∣ lucasV L n := by
  constructor
  · intro n
    induction n with
    | zero => simp [lucasU]
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, lucasU_add_two]
      exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)
  · have hodd (j : ℕ) : L.p ∣ lucasV L (2 * j + 1) := by
      induction j with
      | zero => simp [lucasV]
      | succ j ih =>
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
        change L.p ∣ L.p * lucasV L ((2 * j + 1) + 1) - L.q * lucasV L (2 * j + 1)
        exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)
    rintro n ⟨j, rfl⟩
    exact hodd j

end MetaMathlibExt
