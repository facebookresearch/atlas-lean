/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial coefficients modulo an odd prime

Multiplication by `k!` turns `(n + k).choose k` into a rising factorial in `n + 1`.
After reducing `n` modulo the prime and using binomial symmetry, negating each factor
turns the rising factorial into a signed falling factorial.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Binomial coefficients $\binom{n+k}{k}$ modulo an odd prime.** Let $l$ be an odd prime, $k$
an integer with $1 \le k < l$, $n$ a natural number, and $r$ the remainder of $n$ modulo $l$. If
$r \le l - k - 1$, then $\binom{n+k}{k} \equiv (-1)^r \binom{l-k-1}{r} \pmod l$; otherwise
$\binom{n+k}{k} \equiv 0 \pmod l$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Lemma 1 (`integers-2024-A39-lem-1`). -/
public theorem choose_add_modEq_prime (l : ℕ) (hl : l.Prime) (hodd : Odd l) (k : ℕ)
    (hk : 1 ≤ k) (hkl : k < l) (n : ℕ) :
    ((n + k).choose k : ℤ) ≡
      (if n % l ≤ l - k - 1 then (-1 : ℤ) ^ (n % l) * ((l - k - 1).choose (n % l) : ℤ)
        else 0) [ZMOD l] := by
  have : Fact l.Prime := ⟨hl⟩
  set r := n % l
  set m := l - k - 1
  rw [ite_eq_left_iff.mpr (fun h => by simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]),
    ← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hfac {b : ℕ} (hb : b < l) : (b.factorial : ZMod l) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff, hl.dvd_factorial] using hb.not_ge
  have heval (a b : ℕ) : (b.factorial : ZMod l) * ((a + b).choose b : ZMod l) =
      (ascPochhammer (ZMod l) b).eval (a + 1 : ZMod l) := by
    rw [← Nat.cast_mul, ← Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_ascFactorial,
      Nat.cast_add_one]
  calc
    ((n + k).choose k : ZMod l) = ((r + k).choose k : ZMod l) := by
      apply mul_left_cancel₀ (hfac hkl)
      rw [heval, heval, ZMod.natCast_mod]
    _ = ((k + r).choose r : ZMod l) := by rw [Nat.add_comm r k, Nat.choose_symm_add]
    _ = (-1) ^ r * (m.choose r : ZMod l) := by
      have hneg : (k : ZMod l) + 1 = -(m : ZMod l) := by
        simp [m, Nat.cast_sub (by omega : 1 ≤ l - k), Nat.cast_sub hkl.le, add_comm]
      apply mul_left_cancel₀ (hfac (Nat.mod_lt n hl.pos))
      rw [heval, hneg, ascPochhammer_eval_neg_eq_descPochhammer,
        descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
        Nat.cast_mul]
      ac_rfl

end MetaMathlibExt
