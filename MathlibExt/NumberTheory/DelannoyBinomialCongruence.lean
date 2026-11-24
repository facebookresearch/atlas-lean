/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # A reflection congruence for Delannoy binomial coefficients -/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- **Reflection congruence for binomial coefficients modulo a prime.** For a prime $p$ and
natural numbers $j$ and $k$ with $j \le k \le p - 2$,
$$\binom{p-j}{k+1} + (-1)^k \binom{k+j}{k+1} \equiv 0 \pmod{p}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 11. -/
public theorem choose_add_choose_mod (p j k : ℕ)
    (hp : p.Prime) (hjk : j ≤ k) (hk : k ≤ p - 2) :
    (Nat.choose (p - j) (k + 1) : ZMod p) +
        (-1) ^ k * (Nat.choose (k + j) (k + 1) : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hkp : k + 1 < p := by omega
  have hfac : ((k + 1).factorial : ZMod p) ≠ 0 := by
    intro h
    exact hkp.not_ge (hp.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have hcast : -(↑(p - j) : ZMod p) = (j : ZMod p) := by
    rw [Nat.cast_sub (show j ≤ p by omega), ZMod.natCast_self, zero_sub, neg_neg]
  -- Pochhammer evaluation includes the out-of-range cases, where a factor is zero.
  have hreflection := ascPochhammer_eval_neg_eq_descPochhammer (ZMod p) (↑(p - j)) (k + 1)
  rw [hcast, ascPochhammer_nat_eq_natCast_ascFactorial, descPochhammer_eval_eq_descFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose', Nat.descFactorial_eq_factorial_mul_choose,
    show j + (k + 1) - 1 = k + j by omega, Nat.cast_mul, Nat.cast_mul] at hreflection
  have hchoose : (Nat.choose (k + j) (k + 1) : ZMod p) =
      (-1) ^ (k + 1) * (Nat.choose (p - j) (k + 1) : ZMod p) := by
    apply mul_left_cancel₀ hfac
    simpa only [mul_left_comm] using hreflection
  rw [hchoose, ← mul_assoc, show (-1 : ZMod p) ^ k * (-1) ^ (k + 1) = -1 by
    rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]]
  simp

end MathlibExt.NumberTheory.DelannoyTriangleWanted
