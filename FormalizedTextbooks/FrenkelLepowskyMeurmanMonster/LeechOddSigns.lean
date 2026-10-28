/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! Actual Golay signs relating odd integral vectors with the same coordinate magnitudes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem odd_coordinate_sign (a b : ℤ) (c d : ZMod 2)
    (ha : (a : ZMod 4) = 1 + 2 * (c.val : ZMod 4))
    (hb : (b : ZMod 4) = 1 + 2 * (d.val : ZMod 4))
    (habs : a.natAbs = b.natAbs) :
    (if c + d = 0 then a else -a) = b := by
  have hcheck : ∀ c d : ZMod 2,
      ((1 + 2 * (c.val : ZMod 4) = 1 + 2 * (d.val : ZMod 4)) → c + d = 0) ∧
      ((-(1 + 2 * (d.val : ZMod 4)) = 1 + 2 * (c.val : ZMod 4)) → c + d ≠ 0) := by
    decide +kernel
  rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
  · subst b
    have hh := ha.symm.trans hb
    rw [ite_eq_left ((hcheck c d).1 hh)]
  · subst a
    rw [Int.cast_neg, hb] at ha
    rw [ite_eq_right ((hcheck c d).2 ha), neg_neg]

/-- Actual odd source residues determine a genuine Golay sign taking one vector to the other. -/
theorem leechOdd_same_magnitudes_sign (u v : leechIntegral) (c d : golayCode)
    (hu : ∀ i, (u.val i : ZMod 4) = 1 + 2 * ((c.val i).val : ZMod 4))
    (hv : ∀ i, (v.val i : ZMod 4) = 1 + 2 * ((d.val i).val : ZMod 4))
    (habs : ∀ i, (u.val i).natAbs = (v.val i).natAbs) :
    leechIntegralAction (golaySignIsometry (c + d)) u = v := by
  apply Subtype.ext
  rw [leechIntegralAction_golaySign]
  funext i
  exact odd_coordinate_sign (u.val i) (v.val i) (c.val i) (d.val i)
    (hu i) (hv i) (habs i)

/-- An odd coordinate forces the original lattice source to have odd common parity. -/
theorem leechOdd_source_code (u : leechIntegral) (ho : Odd (u.val 0)) :
    ∃ c : golayCode, ∀ i,
      (u.val i : ZMod 4) = 1 + 2 * ((c.val i).val : ZMod 4) := by
  obtain ⟨m, hm, c, hc, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hm1 : m = 1 := by
    rcases hm with hm | hm
    · obtain ⟨k, hk⟩ := ho
      obtain ⟨j, hj⟩ := leechResidue_dvd u.val m c hr 0
      omega
    · exact hm
  subst m
  exact ⟨⟨c, hc⟩, hr⟩

/-- Equal coordinate magnitudes of two actual odd vectors admit an actual Golay sign transport. -/
theorem leechOdd_same_magnitudes_transport (u v : leechIntegral)
    (hu : Odd (u.val 0)) (hv : Odd (v.val 0))
    (habs : ∀ i, (u.val i).natAbs = (v.val i).natAbs) :
    ∃ d : golayCode, leechIntegralAction (golaySignIsometry d) u = v := by
  obtain ⟨c, hc⟩ := leechOdd_source_code u hu
  obtain ⟨d, hd⟩ := leechOdd_source_code v hv
  exact ⟨c + d, leechOdd_same_magnitudes_sign u v c d hc hd habs⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
