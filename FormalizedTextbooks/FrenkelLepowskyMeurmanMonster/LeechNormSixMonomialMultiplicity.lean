/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairPermutationMultiplicity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairShapes

/-! Genuine monomial invariance and recognition of the odd three-coordinate norm-six family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay signs preserve every original coordinate-magnitude multiplicity. -/
theorem leechNormSix_sign_multiplicity (d : golayCode) (u : leechIntegral) :
    leechNormEightMultiplicity (leechIntegralAction (golaySignIsometry d) u).val =
      leechNormEightMultiplicity u.val := by
  have habs (i : Fin 24) :
      ((leechIntegralAction (golaySignIsometry d) u).val i).natAbs = (u.val i).natAbs := by
    rw [leechIntegralAction_golaySign]
    change (if d.val i = 0 then u.val i else -u.val i).natAbs = (u.val i).natAbs
    split_ifs <;> simp
  funext k
  simp only [leechNormEightMultiplicity, habs]

/-- Every genuine Golay monomial isometry preserves the complete original multiplicities. -/
theorem leechNormSix_monomial_multiplicity (b : leechIsomSubgroup)
    (hb : b ∈ golayMonomialSubgroup) (u : leechIntegral) :
    leechNormEightMultiplicity (leechIntegralAction b u).val =
      leechNormEightMultiplicity u.val := by
  obtain ⟨d, p, rfl⟩ := hb
  rw [map_mul, LinearEquiv.mul_apply, leechNormSix_sign_multiplicity,
    leechNormSixPair_permutation_multiplicity]

/-- A single genuine coordinate of magnitude three recognizes the original odd three-coordinate
norm-six family. -/
theorem leechNormSix_of_magnitude_three (u : leechIntegral)
    (hn : leechSquareSum u.val = 48) (i : Fin 24) (h3 : (u.val i).natAbs = 3) :
    leechNormEightMultiplicity u.val = leechNormSixShapeCounts 3 := by
  obtain ⟨s, hs⟩ := leechNormSix_catalog u hn
  have ha := leechNormSix_coordinate_allowed u.val s
    (fun x => (leechNormSix_natAbs_le _ hn x).trans (by decide)) hs i
  rw [h3] at ha
  have hcheck : ∀ s : Fin 4, leechNormSixCoordinateAllowed s 3 → s = 3 := by
    decide +kernel
  have hs3 := hcheck s ha
  subst s
  exact hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
