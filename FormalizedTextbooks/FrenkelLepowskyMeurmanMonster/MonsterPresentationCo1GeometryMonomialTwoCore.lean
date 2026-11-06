/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine Conway monomial subgroup has exactly the codeword-sign normal two-core. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryMonomialProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreQuotients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderSigns

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual Co₀ monomial subgroup maps to the actual Conway quotient. -/
def monsterCo1GeometryMonomialClassHom : golayMonomialSubgroup →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp golayMonomialSubgroup.subtype

/-- Actual monomial classes form a genuine subgroup of the actual Conway group. -/
abbrev monsterCo1GeometryMonomialClasses : Subgroup Co1 :=
  monsterCo1GeometryMonomialClassHom.range

/-- The actual class map kernel is precisely the central real signs within the monomial group. -/
theorem monsterCo1GeometryMonomialClassHom_kernel :
    monsterCo1GeometryMonomialClassHom.ker =
      signsSubgroup.comap golayMonomialSubgroup.subtype := by
  rw [monsterCo1GeometryMonomialClassHom, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- The two actual central real signs form a two-group of their independently proved cardinality. -/
theorem monsterCo1GeometryCentralSigns_isTwoGroup : IsPGroup 2 signsSubgroup :=
  IsPGroup.of_card (n := 1) (by simpa only [pow_one] using signsSubgroup_card)

/-- The actual monomial class map has a two-group kernel. -/
theorem monsterCo1GeometryMonomialClassHom_kernel_isTwoGroup :
    IsPGroup 2 monsterCo1GeometryMonomialClassHom.ker :=
  (congrArg (fun S : Subgroup golayMonomialSubgroup => IsPGroup 2 S)
    monsterCo1GeometryMonomialClassHom_kernel).mpr
      (monsterCo1GeometryCentralSigns_isTwoGroup.comap_of_injective
        golayMonomialSubgroup.subtype golayMonomialSubgroup.subtype_injective)

/-- Actual codeword signs project to genuine Conway monomial classes. -/
def monsterCo1GeometrySignClassHom : Multiplicative golayCode →* Co1 :=
  monsterCo1GeometryMonomialClassHom.comp monsterCo1GeometrySignIntoMonomial

/-- The point-stabilizer monomial quotient has exactly the image of the genuine sign two-core. -/
theorem monsterCo1GeometryMonomialClasses_twoCore :
    monsterGeometryTwoCore monsterCo1GeometryMonomialClasses =
      (monsterGeometryTwoCore golayMonomialSubgroup).map
        monsterCo1GeometryMonomialClassHom.rangeRestrict := by
  symm
  apply monsterGeometryTwoCore_map_surjective
    monsterCo1GeometryMonomialClassHom.rangeRestrict
    monsterCo1GeometryMonomialClassHom.rangeRestrict_surjective
  exact (congrArg (fun S : Subgroup golayMonomialSubgroup => IsPGroup 2 S)
    monsterCo1GeometryMonomialClassHom.ker_rangeRestrict).mpr
      monsterCo1GeometryMonomialClassHom_kernel_isTwoGroup

/-- The actual Conway monomial two-core is exactly the actual sign image. -/
theorem monsterCo1GeometryMonomialClasses_twoCore_image :
    (monsterGeometryTwoCore monsterCo1GeometryMonomialClasses).map
      monsterCo1GeometryMonomialClasses.subtype = monsterCo1GeometrySignClassHom.range := by
  rw [monsterCo1GeometryMonomialClasses_twoCore, monsterCo1GeometryMonomialTwoCore_eq_signs,
    Subgroup.map_map]
  have he : monsterCo1GeometryMonomialClasses.subtype.comp
      monsterCo1GeometryMonomialClassHom.rangeRestrict = monsterCo1GeometryMonomialClassHom := by
    ext g
    rfl
  rw [he, ← MonoidHom.range_comp]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
