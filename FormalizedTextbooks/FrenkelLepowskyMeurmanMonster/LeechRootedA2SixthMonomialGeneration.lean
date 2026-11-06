/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthMonomialQuotient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationGeneration

/-! The actual fourteen source generators generate the counted Conway flag monomial subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Ten source signs and four source permutations generate the counted monomial subgroup. -/
theorem leechRootedA2SixthMonomialCo1_le_of_generators (K : Subgroup Co1)
    (hSign : ∀ j : Fin 10,
      (QuotientGroup.mk (golaySignIsometry
        (sourceGeneratedSignCode (generatedSixthMonomialSignCode j))) : Co1) ∈ K)
    (hPerm : ∀ j : Fin 3,
      (QuotientGroup.mk (golayPermutationIsometry
        (leechRootedA2SixthPermutationGenerator j)) : Co1) ∈ K)
    (hSwap : (QuotientGroup.mk (golayPermutationIsometry
      leechRootedA2SixthPermutationWordSwap) : Co1) ∈ K) :
    leechRootedA2SixthMonomialCo1Subgroup ≤ K := by
  let π : leechIsomSubgroup →* Co1 := QuotientGroup.mk' signsSubgroup
  let L := K.comap π
  have hSign' : ∀ c : leechRootedA2SixthSignSpace, golaySignIsometry c.val ∈ L := by
    intro c
    obtain ⟨a, ha⟩ := c.val.property
    have hc : golayEncoder a 17 = golayEncoder a 16 ∧
        golayEncoder a 19 = golayEncoder a 16 := by
      rw [ha]
      exact c.property
    let t : generatedSixthSignCoefficientSpace :=
      ⟨a, (generatedSixth_sign_coefficient_mem a).mpr hc⟩
    have ht := generatedSixth_sign_isometry_mem_of_generators L hSign t
    have he : generatedSixthSignCoefficientCode t = c.val := Subtype.ext ha
    rw [he] at ht
    exact ht
  have hPerm' : ∀ p : leechRootedA2SixthPermutationFlag,
      golayPermutationIsometry p.val ∈ L := by
    intro p
    exact leechRootedA2SixthPermutation_mem_of_generators
      (L.comap golayPermutationHom) hPerm hSwap p.val p.property
  rintro x ⟨g, hg, rfl⟩
  obtain ⟨c, p, rfl⟩ := hg
  exact L.mul_mem (hSign' c) (hPerm' p)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
