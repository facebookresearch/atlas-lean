/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual signed Golay monomial group projects onto its actual permutation factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryM24TwoCore
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreGeneric

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The independently proved unique codeword/permutation parametrization of actual monomial maps. -/
def monsterCo1GeometryMonomialParameters :
    golayCode × golayAutomorphismSubgroup ≃ golayMonomialSubgroup :=
  Equiv.ofBijective golayMonomialEnumeration golayMonomialEnumeration_bijective

/-- Enumeration followed by parameters recovers the supplied codeword and permutation. -/
theorem monsterCo1GeometryMonomialParameters_enumeration (a :
    golayCode × golayAutomorphismSubgroup) :
    monsterCo1GeometryMonomialParameters.symm (golayMonomialEnumeration a) = a :=
  monsterCo1GeometryMonomialParameters.symm_apply_apply a

/-- The unique monomial parameters multiply by the actual semidirect product formula. -/
theorem monsterCo1GeometryMonomialEnumeration_mul
    (d e : golayCode) (p q : golayAutomorphismSubgroup) :
    golayMonomialEnumeration (d, p) * golayMonomialEnumeration (e, q) =
      golayMonomialEnumeration (d + golayCodePermutation p e, p * q) := by
  apply Subtype.ext
  change (golaySignIsometry d * golayPermutationIsometry p) *
      (golaySignIsometry e * golayPermutationIsometry q) =
      golaySignIsometry (d + golayCodePermutation p e) * golayPermutationIsometry (p * q)
  have hsign := golaySignHom.map_mul (Multiplicative.ofAdd d)
    (Multiplicative.ofAdd (golayCodePermutation p e))
  change golaySignIsometry (d + golayCodePermutation p e) =
    golaySignIsometry d * golaySignIsometry (golayCodePermutation p e) at hsign
  have hperm := golayPermutationHom.map_mul p q
  change golayPermutationIsometry (p * q) =
    golayPermutationIsometry p * golayPermutationIsometry q at hperm
  rw [hsign, hperm]
  calc
    _ = golaySignIsometry d * (golayPermutationIsometry p * golaySignIsometry e) *
        golayPermutationIsometry q := by group
    _ = _ := by rw [golayPermutation_sign_commute]; group

/-- The actual monomial identity has zero codeword and identity permutation. -/
theorem monsterCo1GeometryMonomialEnumeration_one :
    golayMonomialEnumeration (0, 1) = 1 := by
  apply Subtype.ext
  change golaySignHom 1 * golayPermutationHom 1 = 1
  rw [map_one, map_one, mul_one]

/-- The genuine monomial group projects to its genuine physical permutation factor. -/
def monsterCo1GeometryMonomialProjection :
    golayMonomialSubgroup →* golayAutomorphismSubgroup where
  toFun g := (monsterCo1GeometryMonomialParameters.symm g).2
  map_one' := by
    rw [← monsterCo1GeometryMonomialEnumeration_one,
      monsterCo1GeometryMonomialParameters_enumeration]
  map_mul' g h := by
    obtain ⟨⟨d, p⟩, rfl⟩ := golayMonomialEnumeration_bijective.2 g
    obtain ⟨⟨e, q⟩, rfl⟩ := golayMonomialEnumeration_bijective.2 h
    rw [monsterCo1GeometryMonomialEnumeration_mul]
    simp only [monsterCo1GeometryMonomialParameters_enumeration]

/-- The actual projection retains the supplied permutation in every literal monomial map. -/
@[simp] theorem monsterCo1GeometryMonomialProjection_enumeration
    (d : golayCode) (p : golayAutomorphismSubgroup) :
    monsterCo1GeometryMonomialProjection (golayMonomialEnumeration (d, p)) = p :=
  congrArg Prod.snd (monsterCo1GeometryMonomialParameters_enumeration (d, p))

/-- Every actual Golay permutation has a genuine monomial lift. -/
theorem monsterCo1GeometryMonomialProjection_surjective :
    Function.Surjective monsterCo1GeometryMonomialProjection := by
  intro p
  exact ⟨golayMonomialEnumeration (0, p), monsterCo1GeometryMonomialProjection_enumeration 0 p⟩

/-- Actual codeword signs as elements of the actual monomial subgroup. -/
def monsterCo1GeometrySignIntoMonomial : Multiplicative golayCode →* golayMonomialSubgroup where
  toFun d := ⟨golaySignHom d, Multiplicative.toAdd d, 1, by
    change golaySignHom d = golaySignHom d * golayPermutationHom 1
    rw [map_one, mul_one]⟩
  map_one' := Subtype.ext golaySignHom.map_one
  map_mul' d e := Subtype.ext (golaySignHom.map_mul d e)

/-- The actual sign lift has exactly its supplied zero-permutation monomial parameters. -/
theorem monsterCo1GeometrySignIntoMonomial_enumeration (d : golayCode) :
    monsterCo1GeometrySignIntoMonomial (Multiplicative.ofAdd d) =
      golayMonomialEnumeration (d, 1) := by
  apply Subtype.ext
  change golaySignIsometry d = golaySignIsometry d * golayPermutationHom 1
  rw [map_one, mul_one]

/-- The exact actual monomial projection kernel is the actual codeword-sign image. -/
theorem monsterCo1GeometryMonomialProjection_kernel :
    monsterCo1GeometryMonomialProjection.ker = monsterCo1GeometrySignIntoMonomial.range := by
  ext g
  obtain ⟨⟨d, p⟩, rfl⟩ := golayMonomialEnumeration_bijective.2 g
  constructor
  · intro h
    have hp : p = 1 := by simpa only [MonoidHom.mem_ker,
      monsterCo1GeometryMonomialProjection_enumeration] using h
    subst p
    exact ⟨Multiplicative.ofAdd d, monsterCo1GeometrySignIntoMonomial_enumeration d⟩
  · rintro ⟨e, he⟩
    rw [← he]
    change monsterCo1GeometryMonomialProjection (monsterCo1GeometrySignIntoMonomial e) = 1
    have he := monsterCo1GeometrySignIntoMonomial_enumeration (Multiplicative.toAdd e)
    simp only [ofAdd_toAdd] at he
    rw [he, monsterCo1GeometryMonomialProjection_enumeration]

/-- The actual sign kernel is a two-group, by the independently proved Golay code cardinality. -/
theorem monsterCo1GeometryMonomialProjection_kernel_isTwoGroup :
    IsPGroup 2 monsterCo1GeometryMonomialProjection.ker := by
  have hc : Nat.card (Multiplicative golayCode) = 2 ^ 12 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact golayCode_card
  have hp : IsPGroup 2 (Multiplicative golayCode) := IsPGroup.of_card hc
  exact (congrArg (fun S : Subgroup golayMonomialSubgroup => IsPGroup 2 S)
    monsterCo1GeometryMonomialProjection_kernel).mpr
      (hp.of_surjective monsterCo1GeometrySignIntoMonomial.rangeRestrict
        monsterCo1GeometrySignIntoMonomial.rangeRestrict_surjective)

/-- The intrinsic normal two-core of actual Co₀ monomial maps is exactly their sign subgroup. -/
theorem monsterCo1GeometryMonomialTwoCore_eq_signs :
    monsterGeometryTwoCore golayMonomialSubgroup = monsterCo1GeometrySignIntoMonomial.range := by
  rw [← monsterCo1GeometryMonomialProjection_kernel]
  apply monsterGeometryTwoCore_eq_kernel monsterCo1GeometryMonomialProjection
    monsterCo1GeometryMonomialProjection_surjective
    monsterCo1GeometryMonomialProjection_kernel_isTwoGroup
  intro P hnormal hP
  have : P.Normal := hnormal
  exact monsterCo1GeometryM24_normal_two_eq_bot P hP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
