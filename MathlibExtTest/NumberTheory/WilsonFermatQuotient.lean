/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonFermatQuotient

private def fermatSum (p : ℕ) (hp : p.Prime) : ZMod (p ^ 2) :=
  ∑ k ∈ (Finset.Icc 1 (p - 1)).attach,
    (Int.fermatQuotient p hp (k.1 : ℤ) (by
      obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp k.2
      have hk : k.1 < p := Nat.lt_of_le_of_lt hk₂ (Nat.sub_lt hp.pos Nat.one_pos)
      exact Nat.isCoprime_iff_coprime.mpr
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk₁ hk)).symm)) : ZMod (p ^ 2))

private theorem factorial_eq_fermatSum (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (Nat.factorial (p - 1) : ZMod (p ^ 2)) = -1 + (p : ZMod (p ^ 2)) * fermatSum p hp :=
  MathlibExt.NumberTheory.WilsonFaulhaberWanted.wilson_mod_prime_sq (p := p) (hp := hp) (hp2 := hp2)

example : (Nat.factorial (3 - 1) : ZMod (3 ^ 2)) = 2 := by
  calc
    _ = -1 + 3 * fermatSum 3 (by decide) := factorial_eq_fermatSum 3 (by decide) (by decide)
    _ = _ := by decide

example : (Nat.factorial (5 - 1) : ZMod (5 ^ 2)) = 24 := by
  calc
    _ = -1 + 5 * fermatSum 5 (by decide) := factorial_eq_fermatSum 5 (by decide) (by decide)
    _ = _ := by decide

example : (Nat.factorial (7 - 1) : ZMod (7 ^ 2)) = 34 := by
  calc
    _ = -1 + 7 * fermatSum 7 (by decide) := factorial_eq_fermatSum 7 (by decide) (by decide)
    _ = _ := by decide

-- At `p = 2`, the same right-hand side is `-1` rather than `1` modulo `4`.
example : (Nat.factorial (2 - 1) : ZMod (2 ^ 2)) ≠ -1 + 2 * fermatSum 2 (by decide) := by
  decide
