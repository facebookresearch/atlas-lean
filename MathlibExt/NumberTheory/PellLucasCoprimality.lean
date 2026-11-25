/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Coprimality of Pell and Pell–Lucas numbers

The Pell and Pell–Lucas numbers at the same index are coprime: their sum is the next Pell number,
and consecutive Pell numbers are coprime.
-/

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

open MetaMathlibExt

-- Equation (6) of Mendes: both sides satisfy the same second-order recurrence.
private theorem pellNumber_add_pellLucasSequence (n : ℕ) :
    pellNumber n + pellLucasSequence n = pellNumber (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
    change (2 * pellNumber (n + 1) + pellNumber n) +
      (2 * pellLucasSequence (n + 1) + pellLucasSequence n) =
      2 * pellNumber (n + 1 + 1) + pellNumber (n + 1)
    rw [Nat.add_add_add_comm, ← Nat.mul_add, ih₁, ih₀]

private theorem gcd_pellNumber_succ (n : ℕ) :
    Nat.gcd (pellNumber n) (pellNumber (n + 1)) = 1 := by
  induction n with
  | zero => simp [pellNumber]
  | succ n ih =>
    change Nat.gcd (pellNumber (n + 1)) (2 * pellNumber (n + 1) + pellNumber n) = 1
    rw [Nat.gcd_mul_right_add_right, Nat.gcd_comm]
    exact ih

/-- **Pell and Pell–Lucas numbers are coprime.** For every natural number $n$, the Pell number
$P_n$ and the Pell–Lucas number $Q_n$ satisfy $\gcd(P_n, Q_n) = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 3. -/
public theorem gcd_pellNumber_pellLucasSequence (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellNumber n)
      (MetaMathlibExt.pellLucasSequence n) = 1 := by
  rw [← Nat.gcd_self_add_right, pellNumber_add_pellLucasSequence, gcd_pellNumber_succ]

end MathlibExt.NumberTheory.PellLucasDiophantineWanted
