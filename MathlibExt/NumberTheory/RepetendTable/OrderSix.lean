/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# Small residues excluded by order six

An element of order six modulo a positive power of a prime congruent to one modulo six
differs from zero, one, minus one, two and the inverse of two.
-/

public section

namespace MetaMathlibExt

/-- **Order-six elements modulo a power of a prime congruent to $1$ mod $6$.** Let $p$ be a prime
with $p \equiv 1 \pmod 6$, let $k \ge 1$ and put $n = p^k$. If $b \in \mathbb{Z}/n\mathbb{Z}$ has
multiplicative order $6$, then $b \ne 0$, $2b \ne 1$, $b \ne 1$, $b \ne -1$ and $b \ne 2$ in
$\mathbb{Z}/n\mathbb{Z}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 16 (`integers-2025-A26-lem-16`). -/
theorem orderOf_eq_six_ne_small_residues (p k : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (b : ZMod (p ^ k))
    (hb : orderOf b = 6) :
    b ≠ 0 ∧ 2 * b ≠ 1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2 := by
  have : Fact (1 < p ^ k) := ⟨one_lt_pow₀ hp.one_lt hk.ne'⟩
  obtain ⟨hb6, hmin⟩ := (orderOf_eq_iff (by decide : 0 < 6)).mp hb
  have hb3 := hmin 3 (by decide) (by decide)
  -- Since 9 is a unit, we can cancel it from 2 ^ 6 - 1 = 9 * (2 ^ 3 - 1).
  have h9 : IsUnit (9 : ZMod (p ^ k)) :=
    (ZMod.isUnit_iff_coprime 9 _).mpr (Nat.coprime_pow_primes 2 k (by decide : Nat.Prime 3) hp
      (by omega))
  have cube_of_six (h : (2 : ZMod (p ^ k)) ^ 6 = 1) : (2 : ZMod (p ^ k)) ^ 3 = 1 := by
    apply h9.mul_left_cancel
    linear_combination h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    simp at hb
  · intro h
    have hpow (m : ℕ) : (2 : ZMod (p ^ k)) ^ m * b ^ m = 1 := by
      rw [← mul_pow, h, one_pow]
    have h2 := cube_of_six (by simpa [hb6] using hpow 6)
    exact hb3 (by simpa [h2] using hpow 3)
  · rintro rfl
    simp at hb
  · rintro rfl
    exact hmin 2 (by decide) (by decide) (by simp)
  · rintro rfl
    exact hb3 (cube_of_six hb6)

end MetaMathlibExt
