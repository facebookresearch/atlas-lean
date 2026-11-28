/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatNumbersModPrime
import MathlibExt.NumberTheory.PseudoprimeBasesFermatNumbersDensity

open Filter MetaMathlibExt

private abbrev exceptional : Set ℕ := {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
  ¬∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)}

-- The theorem bounds the proportion below a cutoff, in the ambient set of all naturals.
example : ∀ᶠ N : ℕ in atTop, exceptional.partialDensity Set.univ N < 1 / 100 :=
  hasDensity_zero_strongPseudoprime_bases_not_subgroup.eventually_lt_const (by norm_num)

-- Wagstaff's Example 2: bases 21 and 174 pass, but their product 118 does not.
example : 221 ∈ exceptional := by
  have hn : 1 < (221 : ℕ) := by decide
  have hc : ¬Nat.Prime 221 := Nat.not_prime_mul (a := 13) (b := 17) (by decide) (by decide)
  have ho : Odd (221 : ℕ) := by decide
  refine ⟨hn, hc, ho, ?_⟩
  rintro ⟨H, hH⟩
  let a : (ZMod 221)ˣ := ZMod.unitOfCoprime 21 (by decide)
  let b : (ZMod 221)ˣ := ZMod.unitOfCoprime 174 (by decide)
  have ha : IsStrongPseudoprime 221 (a : ZMod 221) :=
    ⟨hn, hc, ho, 2, 55, rfl, by decide, Or.inr ⟨1, by decide, by decide⟩⟩
  have hb : IsStrongPseudoprime 221 (b : ZMod 221) :=
    ⟨hn, hc, ho, 2, 55, rfl, by decide, Or.inr ⟨1, by decide, by decide⟩⟩
  have hab := H.mul_mem ((hH a).mpr ha) ((hH b).mpr hb)
  obtain ⟨_, _, _, k, d, hkd, hd, hpow⟩ := (hH (a * b)).mp hab
  have hsplit : 2 ^ k * d = 2 ^ (2 : ℕ) * 55 := hkd.symm
  obtain ⟨hk', hd'⟩ := (Nat.two_pow_mul_odd_inj hd (by decide)).mp hsplit
  subst k
  subst d
  rcases hpow with h | ⟨i, hi, h⟩
  · exact (by decide : ¬((↑(a * b) : ZMod 221) ^ 55 = 1)) h
  · interval_cases i
    · exact (by decide : ¬((↑(a * b) : ZMod 221) ^ (2 ^ 0 * 55) = -1)) h
    · exact (by decide : ¬((↑(a * b) : ZMod 221) ^ (2 ^ 1 * 55) = -1)) h
