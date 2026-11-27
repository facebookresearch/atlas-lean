/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotKlNearPerfectWithTwoPowMul
namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example (k l : ℕ) (hl : 1 ≤ l) :
    ¬ KLNearPerfectWith k l 12 1 ∧ ¬ KLNearPerfectWith k l 12 3 := by
  simpa using not_klNearPerfectWith_two_pow_mul k l 3 2 hl (by decide) (by decide) (by decide)

example : ¬ KLNearPerfectWith 0 1 12 1 := by
  simpa using
    (not_klNearPerfectWith_two_pow_mul 0 1 3 2 (by decide) (by decide) (by decide) (by decide)).1

example (k l p a d : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) (ha : 1 < a)
    (h : KLNearPerfectWith k l (2 ^ a * p) d) : ¬ Odd d := by
  intro hd
  have hdp : d ∣ p :=
    ((Nat.coprime_two_right.mpr hd).pow_right a).dvd_of_dvd_mul_left h.1
  have hexcluded := not_klNearPerfectWith_two_pow_mul k l p a hl hp hpo ha
  rcases (Nat.dvd_prime hp).mp hdp with rfl | rfl
  · exact hexcluded.1 h
  · exact hexcluded.2 h

end MathlibExtTest.NumberTheory.FkPerfect
