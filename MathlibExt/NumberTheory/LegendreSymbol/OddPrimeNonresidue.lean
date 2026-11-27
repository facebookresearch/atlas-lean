/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An odd prime quadratic non-residue
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section

namespace legendreSym

/-- **An odd prime non-residue (Robinson's Lemma 5).** For every prime `p` with `p ≡ 1 (mod 4)`
there is an odd prime `q` that is a quadratic non-residue modulo `p`, that is, whose Legendre
symbol `(q / p)` is `-1` (`legendreSym p q = -1`).

Source: J. Robinson, "Definability and decision problems in arithmetic", J. Symbolic Logic 14
(1949), 98–114, Lemma 5, p. 108: "If p is a prime ≡ 1 (mod 4), there is an odd prime q such that
(q/p) = −1." It supplies the prime `q` with which her Lemma 4 is applied in the proof of her
Theorem 3.1(i), p. 109. The proof follows hers: a non-residue `s` modulo `p` with `0 ≤ s < p`, or
`s + p`, is odd, and an odd non-residue has an odd prime factor that is a non-residue. -/
public theorem exists_odd_prime_eq_neg_one (p : ℕ) [hpp : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ legendreSym p q = -1 := by
  have key : ∀ m : ℕ, Odd m → legendreSym p m = -1 →
      ∃ q : ℕ, q.Prime ∧ Odd q ∧ legendreSym p q = -1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hmo hm
      have hm1 : m ≠ 1 := by rintro rfl; simp at hm
      have hq : m.minFac.Prime := Nat.minFac_prime hm1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd m
      have hqo : Odd m.minFac := (Nat.odd_mul.mp (hk ▸ hmo)).1
      have hko : Odd k := (Nat.odd_mul.mp (hk ▸ hmo)).2
      have hmul : legendreSym p m = legendreSym p m.minFac * legendreSym p k := by
        conv_lhs => rw [hk]
        push_cast
        exact legendreSym.mul p _ _
      by_cases hqs : legendreSym p m.minFac = -1
      · exact ⟨_, hq, hqo, hqs⟩
      · have hq0 : legendreSym p m.minFac ≠ 0 := by
          intro h0; rw [hmul, h0, zero_mul] at hm; norm_num at hm
        have hq1 : legendreSym p m.minFac = 1 := by
          rcases legendreSym.eq_one_or_neg_one p (a := (m.minFac : ℤ))
            (fun h0 => hq0 ((legendreSym.eq_zero_iff p _).mpr h0)) with h | h
          · exact h
          · exact absurd h hqs
        have hk' : legendreSym p k = -1 := by rw [hmul, hq1, one_mul] at hm; exact hm
        have hklt : k < m := by
          rw [hk]
          exact lt_mul_left hko.pos hq.one_lt
        exact ih k hklt hko hk'
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have hs : legendreSym p (a.val : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using ha
  have hpodd : Odd p := hpp.out.odd_of_ne_two hp2
  rcases Nat.even_or_odd a.val with he | ho
  · refine key (a.val + p) (he.add_odd hpodd) ?_
    have : legendreSym p ((a.val + p : ℕ) : ℤ) = legendreSym p (a.val : ℤ) := by
      rw [legendreSym.mod p ((a.val + p : ℕ) : ℤ), legendreSym.mod p (a.val : ℤ)]
      push_cast; simp
    rw [this, hs]
  · exact key a.val ho hs

end legendreSym

end
