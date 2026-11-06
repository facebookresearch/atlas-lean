/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A finite vector test for identity of actual local elements.
Twenty-four signed short basis vectors force the full Q action to be trivial;
one vector with a nonzero tensor constituent fixes the remaining central sign. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedQCoordinateIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An actual pure-short vector in the Griess dictionary. -/
noncomputable def monsterNortonPureShort (r : GriessShortIndex) : GriessSpace :=
  griessConwayDecode (0, (Pi.single r 1, 0))

private theorem short_unit_fixed_Q (f : localFiberSubgroup) (r : GriessShortIndex)
    (h : localShortOperator f (Pi.single r 1) = Pi.single r 1) :
    spinConjugation f.val.1 (griessShortQ r) = griessShortQ r := by
  have he := localShortOperator_image f (Pi.single r 1) r
  rw [h] at he
  simp only [Pi.single_eq_same, mul_one] at he
  have hp : griessShortPermutation f.val.2 r = r := by
    by_contra hp
    simp only [Pi.single_apply, hp, ite_false] at he
    have hs := qSign_sq (localShortPhase f r)
    nlinarith
  have hc : localShortPhase f r = 0 := by
    apply (qSign_eq_one_iff _).mp
    rw [hp, Pi.single_eq_same] at he
    exact he.symm
  rw [griessShortQ_image, hp, hc]
  change 1 * griessShortQ r = griessShortQ r
  rw [one_mul]

/-- Fixing one actual pure-short vector forces commutation with its full preferred Q lift. -/
theorem monsterNortonLocal_fix_short_commutes (h : H) (r : GriessShortIndex)
    (hr : rhoLocal h (monsterNortonPureShort r) = monsterNortonPureShort r) :
    Commute (localIntoGenerated h) (qIntoGenerated (griessShortQ r)) := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  subst h
  have hr' : localGriessRepresentation f (monsterNortonPureShort r) =
      monsterNortonPureShort r := hr
  have he := congrArg griessConwayEncode hr'
  rw [monsterNortonPureShort, localGriessRepresentation_encode,
    localConwayRawRepresentation_apply,
    griessConwayEncode_decode _ (by intro i j; rfl)] at he
  have hs : localShortOperator f (Pi.single r 1) = Pi.single r 1 :=
    congrArg (fun x : ConwayRawSpace => x.2.1) he
  have hq := short_unit_fixed_Q f r hs
  have hc := inclQ_spinConjugation f (griessShortQ r)
  rw [hq] at hc
  have hg := congrArg localIntoGenerated hc
  rw [map_mul, map_mul, map_inv] at hg
  change qIntoGenerated (griessShortQ r) =
    localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f) *
      qIntoGenerated (griessShortQ r) *
        (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f))⁻¹ at hg
  change localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f) *
    qIntoGenerated (griessShortQ r) = qIntoGenerated (griessShortQ r) *
      localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)
  calc
    _ = (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f) *
      qIntoGenerated (griessShortQ r) *
        (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f))⁻¹) *
          localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f) := by group
    _ = _ := by rw [← hg]

/-- The 24 concrete short-vector tests force commutation with every actual Q element. -/
theorem monsterNortonLocal_fix_short_basis_commutes_all_Q (h : H)
    (hb : ∀ j : Fin 24,
      rhoLocal h (monsterNortonPureShort (monsterNortonShortBasisIndex j)) =
        monsterNortonPureShort (monsterNortonShortBasisIndex j)) :
    ∀ q : Q, Commute (localIntoGenerated h) (qIntoGenerated q) := by
  let K : Subgroup Q := (Subgroup.centralizer {localIntoGenerated h}).comap qIntoGenerated
  have hK : K = ⊤ := by
    apply monsterNortonShortBasis_subgroup_eq_top
    · intro j
      rw [monsterNortonShortQ_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (monsterNortonLocal_fix_short_commutes h _ (hb j)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (localIntoGenerated_commute_central h).symm
  intro q
  have hq : q ∈ K := by rw [hK]; exact Subgroup.mem_top q
  exact (Subgroup.mem_centralizer_singleton_iff.mp hq).symm

/-- Actual local identity follows from 24 short images and one nonzero tensor image. -/
theorem monsterNortonLocal_identity_of_short_basis_and_tensor (h : H)
    (hb : ∀ j : Fin 24,
      rhoLocal h (monsterNortonPureShort (monsterNortonShortBasisIndex j)) =
        monsterNortonPureShort (monsterNortonShortBasisIndex j))
    (x : GriessSpace) (hx : rhoLocal h x = x) (ht : (griessConwayEncode x).2.2 ≠ 0) :
    localIntoGenerated h = 1 :=
  generated_commuting_all_q_identity_of_tensor_fixed (localIntoGenerated h)
    (monsterNortonLocal_fix_short_basis_commutes_all_Q h hb) x hx ht

/-- The same finite vector test applies to any actual generated element proved to lie locally. -/
theorem monsterNortonGenerated_identity_of_short_basis_and_tensor (g : ↥G)
    (hg : g ∈ localIntoGenerated.range)
    (hb : ∀ j : Fin 24,
      g.val (monsterNortonPureShort (monsterNortonShortBasisIndex j)) =
        monsterNortonPureShort (monsterNortonShortBasisIndex j))
    (x : GriessSpace) (hx : g.val x = x) (ht : (griessConwayEncode x).2.2 ≠ 0) : g = 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact monsterNortonLocal_identity_of_short_basis_and_tensor h hb x hx ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
