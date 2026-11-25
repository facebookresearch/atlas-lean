/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellLucasSequence

/-!
# Consecutive Pell–Lucas numbers

Consecutive terms of the Pell–Lucas sequence are coprime.
-/

public section

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

/-- **Consecutive Pell–Lucas numbers are coprime.** For every natural number $n$, the Pell–Lucas
numbers $Q_n$ and $Q_{n+1}$ satisfy $\gcd(Q_n, Q_{n+1}) = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 4. -/
theorem gcd_pellLucasSequence_succ (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellLucasSequence n)
      (MetaMathlibExt.pellLucasSequence (n + 1)) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MetaMathlibExt.pellLucasSequence_succ_succ, Nat.gcd_mul_right_add_right, Nat.gcd_comm]
    exact ih

end MathlibExt.NumberTheory.PellLucasDiophantineWanted
