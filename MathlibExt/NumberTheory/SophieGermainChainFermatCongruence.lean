/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fermat congruences along a Sophie Germain prime chain

Every adjacent pair of primes in the chain gives two Fermat congruences modulo their product.
-/

namespace MetaMathlibExt

/-- **Fermat-type congruences along a Sophie Germain prime chain.** Let $p$ and $j$ be natural
numbers and put $q_{i+1} = 2^i (p + 1) - 1$ for $i \ge 0$, so that $q_1 = p$ and
$q_{i+2} = 2q_{i+1} + 1$. Suppose $q_1, \dots, q_{j+2}$ are all prime, and write $q = q_{j+1}$
and $q' = q_{j+2} = 2q + 1$. Then for every integer $a$ coprime to $qq'$,
$a^{q'-1} \equiv q'\,a^{q+1} - 2q \pmod{qq'}$ and
$q'\,a^{q-1} \equiv q\,a^{q'-1} + q + 1 \pmod{qq'}$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Corollary 3.4, Congruences (3.8) (`integers-2025-A31-cor-3-4`). -/
public theorem sophieGermainChain_fermat_congruence {p j : ℕ}
    (hchain : ∀ i ≤ j + 1, (2 ^ i * (p + 1) - 1).Prime) (a : ℤ) :
    let q : ℕ := 2 ^ j * (p + 1) - 1
    let q' : ℕ := 2 ^ (j + 1) * (p + 1) - 1
    IsCoprime a ((q : ℤ) * q') →
      a ^ (q' - 1) ≡ q' * a ^ (q + 1) - 2 * q [ZMOD (q : ℤ) * q'] ∧
        q' * a ^ (q - 1) ≡ q * a ^ (q' - 1) + q + 1 [ZMOD (q : ℤ) * q'] := by
  intro q q' ha
  have hq : q.Prime := hchain j (by omega)
  have hq' : q'.Prime := hchain (j + 1) le_rfl
  have hstep : q' = 2 * q + 1 := by
    have hpos : 0 < 2 ^ j * (p + 1) := Nat.mul_pos (by positivity) (by omega)
    dsimp [q, q']
    rw [pow_succ, mul_right_comm]
    omega
  have hstepZ : (q' : ℤ) = 2 * q + 1 := by exact_mod_cast hstep
  -- Multiply each Fermat congruence by the other prime to lift it to the product.
  have hF := Int.ModEq.pow_card_sub_one_eq_one hq ha.of_mul_right_left
  have hF' := Int.ModEq.pow_card_sub_one_eq_one hq' ha.of_mul_right_right
  have hleft : q' * a ^ (q - 1) ≡ q' [ZMOD (q : ℤ) * q'] := by
    simpa only [mul_one, mul_comm (q' : ℤ) (q : ℤ)] using hF.mul_left' (c := (q' : ℤ))
  have hright : q * a ^ (q' - 1) ≡ q [ZMOD (q : ℤ) * q'] := by
    simpa only [mul_one] using hF'.mul_left' (c := (q : ℤ))
  have hexp : q' - 1 = (q - 1) + (q + 1) := by
    have := hq.pos
    omega
  constructor
  · have hpow : q' * a ^ (q' - 1) ≡ q' * a ^ (q + 1) [ZMOD (q : ℤ) * q'] := by
      rw [hexp, pow_add, ← mul_assoc]
      exact hleft.mul_right _
    calc
      a ^ (q' - 1) = q' * a ^ (q' - 1) - 2 * (q * a ^ (q' - 1)) := by
        rw [hstepZ]
        ring
      _ ≡ q' * a ^ (q + 1) - 2 * q [ZMOD (q : ℤ) * q'] := hpow.sub (hright.mul_left 2)
  · calc
      q' * a ^ (q - 1) ≡ q' [ZMOD (q : ℤ) * q'] := hleft
      _ = (q : ℤ) + q + 1 := by rw [hstepZ, two_mul]
      _ ≡ q * a ^ (q' - 1) + q + 1 [ZMOD (q : ℤ) * q'] :=
        (hright.symm.add_right _).add_right _

end MetaMathlibExt
