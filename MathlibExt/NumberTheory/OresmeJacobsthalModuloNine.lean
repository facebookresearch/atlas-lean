/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-!
# A congruence modulo nine for Jacobsthal numbers

## References

- M. R. Bacon and C. K. Cook, *Some Properties of Oresme Numbers and Convolutions with Various
  Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3, pp. 233–240,
  Corollary 6.3.
- A. F. Horadam, *Jacobsthal Representation Numbers*, The Fibonacci Quarterly 34 (1996),
  no. 1, pp. 40–53, equation (1.1) for the Jacobsthal recurrence.
- A. F. Horadam, *Oresme numbers*, The Fibonacci Quarterly 12 (1974), no. 3, pp. 267–271,
  cited by Bacon and Cook in their introduction for background on the Oresme numbers, not for
  the proof of Corollary 6.3.
-/

namespace MetaMathlibExt

/-- **Powers of two times Jacobsthal numbers modulo 9.** Let $J_m$ denote the Jacobsthal numbers,
the terms of the Lucas sequence $U(1, -2)$. For every natural number $n$,
$2^n J_{n+1} \equiv n + 1 \pmod{9}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.3 (`fq-2024-cookbacon061124-cor-6.3`). -/
public theorem two_pow_mul_jacobsthal_succ_modEq_nine (n : ℕ) :
    2 ^ n * lucasU ⟨1, -2, by decide⟩ (n + 1) ≡ n + 1 [ZMOD 9] := by
  let a (k : ℕ) : ℤ := 2 ^ k * lucasU ⟨1, -2, by decide⟩ (k + 1)
  have hrec (k : ℕ) : a (k + 2) = 2 * a (k + 1) + 8 * a k := by
    change (2 : ℤ) ^ (k + 2) * lucasU ⟨1, -2, by decide⟩ ((k + 1) + 2) = _
    rw [lucasU_add_two _ (k + 1)]
    dsimp only [a]
    rw [pow_succ (2 : ℤ) (k + 1), pow_succ (2 : ℤ) k]
    ring
  change a n ≡ (n : ℤ) + 1 [ZMOD 9]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih₀ ih₁ =>
    rw [hrec]
    have h₂ := (Int.ModEq.refl (n := 9) (2 : ℤ)).mul ih₁
    have h₈ := (Int.ModEq.refl (n := 9) (8 : ℤ)).mul ih₀
    refine (h₂.add h₈).trans (Int.modEq_iff_dvd.mpr ?_)
    refine ⟨-((k : ℤ) + 1), ?_⟩
    push_cast
    ring

end MetaMathlibExt
