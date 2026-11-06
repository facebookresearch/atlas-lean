/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddPairEigen

/-! Actual pair characters separate the lower eleven spin coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Equality of all actual minus-pair characters forces equal lower spin labels. -/
theorem generatedOddSpin_pair_characters_separate (t u : SpinIndex)
    (h : ∀ p : Fin 276,
      golayEncoder t (griessCoordinatePair p).1 + golayEncoder t (griessCoordinatePair p).2 =
      golayEncoder u (griessCoordinatePair p).1 + golayEncoder u (griessCoordinatePair p).2) :
    generatedOddSpinLow t = generatedOddSpinLow u := by
  have hz : ∀ a : ZMod 2, a + a = 0 := by decide +kernel
  have hp (p : Fin 276) :
      golayEncoder (t + u) (griessCoordinatePair p).1 +
        golayEncoder (t + u) (griessCoordinatePair p).2 = 0 := by
    rw [map_add]
    simp only [Pi.add_apply]
    calc
      _ = (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) +
          (golayEncoder u (griessCoordinatePair p).1 +
          golayEncoder u (griessCoordinatePair p).2) := by ring
      _ = 0 := by rw [h p]; exact hz _
  have hc (i j : Fin 24) : golayEncoder (t + u) i = golayEncoder (t + u) j := by
    by_cases hij : i = j
    · rw [hij]
    · have hh := hp (griessPairIndex i j hij)
      rw [griessPairIndex_coordinates] at hh
      split_ifs at hh
      · change golayEncoder (t + u) i + golayEncoder (t + u) j = 0 at hh
        simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hh
      · change golayEncoder (t + u) j + golayEncoder (t + u) i = 0 at hh
        symm
        simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hh
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  have hbits := hbit (golayEncoder (t + u) (0 : Fin 24))
  have hv : t + u = 0 ∨ t + u = (Pi.single (11 : Fin 12) 1 : SpinIndex) := by
    rcases hbits with hb | hb
    · left
      apply golayEncoder_injective
      rw [map_zero]
      ext i
      exact (hc i 0).trans hb
    · right
      apply golayEncoder_injective
      rw [golay_all_one]
      ext i
      exact (hc i 0).trans hb
  ext j
  have hj : t j.castSucc + u j.castSucc = 0 := by
    rcases hv with hv | hv
    · exact congrFun hv j.castSucc
    · have he := congrFun hv j.castSucc
      simpa [Pi.single_apply, Fin.ext_iff, show j.val ≠ 11 by omega] using he
  exact (show t j.castSucc = u j.castSucc from
    by simpa only [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
