/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-!
# Lucas numbers weighted by powers of two modulo five

The Lucas recurrence gives a two-step recurrence for the weighted sequence, which preserves
residue one modulo five.

## References

* Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
  Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
  233–240, Corollary 4.4 (p. 236).
* A. F. Horadam, *Oresme numbers*, The Fibonacci Quarterly 12 (1974), no. 3, 267–271.
  Bacon and Cook cite Horadam for the Oresme-number background, not for the weighted Lucas proof.
-/

namespace MetaMathlibExt

/-- **Powers of two times Lucas numbers modulo 5.** Let $L_m$ denote the Lucas numbers. For every
natural number $n$, $2^n L_{n+1} \equiv 1 \pmod{5}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.4 (`fq-2024-cookbacon061124-cor-4.4`). -/
public theorem two_pow_mul_lucasNumber_succ_modEq_five (n : ℕ) :
    2 ^ n * lucasNumber (n + 1) ≡ 1 [MOD 5] := by
  let a (k : ℕ) := 2 ^ k * lucasNumber (k + 1)
  have step (k : ℕ) : a (k + 2) = 2 * a (k + 1) + 4 * a k := by
    dsimp only [a]
    rw [lucasNumber.eq_3 (k + 1), pow_succ 2 (k + 1), pow_succ 2 k]
    ring
  change a n ≡ 1 [MOD 5]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih₀ ih₁ =>
    rw [step]
    exact ((ih₁.mul_left 2).add (ih₀.mul_left 4)).trans (by decide)

end MetaMathlibExt
