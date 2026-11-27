/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul
import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessPairwiseCoprime
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

/-- **Generalized Markov numbers divisible by $4$.** Let $k$ be a natural number. If some
$k$-generalized Markov number is divisible by $4$, then $k \equiv 2 \pmod{4}$.

Source: Only the first claim of Proposition 4.14 is stated; its "in particular" parity
consequence is omitted because its displayed fraction is garbled in the record.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.14. -/
public theorem mod_four_eq_two_of_four_dvd_genMarkovNumber {k b : ℕ}
    (hb : IsGenMarkovNumber k b) (h4 : 4 ∣ b) : k % 4 = 2 := by
  obtain ⟨a, c, ht⟩ := hb
  obtain ⟨hab, hbc, _⟩ := ht.pairwise_coprime
  have h2b : 2 ∣ b := dvd_trans (by decide : 2 ∣ 4) h4
  have ha : ¬ 2 ∣ a := by
    intro h
    simpa [hab.gcd_eq_one] using Nat.dvd_gcd h h2b
  have hc : ¬ 2 ∣ c := by
    intro h
    simpa [hbc.gcd_eq_one] using Nat.dvd_gcd h2b h
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd a (by decide : 2 ∣ 4)] at ha
    omega
  have hc4 : c % 4 = 1 ∨ c % 4 = 3 := by
    rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd c (by decide : 2 ∣ 4)] at hc
    omega
  have hb0 : (b : ZMod 4) = 0 := (ZMod.natCast_eq_zero_iff b 4).2 h4
  have he := congrArg (fun n : ℕ => (n : ZMod 4)) ht.2.2.2
  push_cast at he
  rw [hb0, ← ZMod.natCast_mod a 4, ← ZMod.natCast_mod c 4, ← ZMod.natCast_mod k 4] at he
  have hk4 : k % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases ha4 with ha4 | ha4 <;> rcases hc4 with hc4 | hc4 <;> rw [ha4, hc4] at he <;>
    interval_cases k % 4 <;> norm_num at he ⊢ <;> exact (by decide : ¬ _) he

end MetaMathlibExt
