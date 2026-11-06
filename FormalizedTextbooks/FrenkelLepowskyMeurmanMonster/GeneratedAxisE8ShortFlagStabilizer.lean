/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlags
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ShortAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Co1StabilizerCount

/-! Exact actual Co0 and Co1 stabilizers of E8 section-short-line flags. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The constructed short permutation supplies the actual short-label action. -/
instance : MulAction leechIsomSubgroup GriessShortIndex where
  smul g r := griessShortPermutation g r
  one_smul r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  mul_smul g h r := by
    change griessShortPermutation (g * h) r =
      griessShortPermutation g (griessShortPermutation h r)
    rw [map_mul]
    rfl

/-- The full actual stabilizer of an incident coordinate section and short line. -/
def generatedAxisE8ShortFlagStabilizer (o : Fin 759) (r : GriessShortIndex) :
    Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o), r)

/-- Flag stabilizer membership fixes both genuine geometric components. -/
theorem generatedAxisE8ShortFlagStabilizer_mem (o : Fin 759) (r : GriessShortIndex)
    (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8ShortFlagStabilizer o r ↔
      generatedAxisE8ImageSection g (golayOctadWord o) =
        generatedAxisE8CoordinateSection (golayOctadWord o) ∧
      griessShortPermutation g r = r := Prod.ext_iff

/-- The group-action orbit is the already counted actual pair-image range. -/
theorem generatedAxisE8ShortFlag_action_orbit (o : Fin 759) (r : GriessShortIndex) :
    MulAction.orbit leechIsomSubgroup
        (generatedAxisE8CoordinateSection (golayOctadWord o), r) =
      generatedAxisE8ShortFlagOrbit o r := rfl

/-- An incident flag has actual Co0 stabilizer order 1,486,356,480. -/
theorem generatedAxisE8ShortFlagStabilizer_card (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8ShortFlagStabilizer o r) = 1486356480 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let x := (generatedAxisE8CoordinateSection (golayOctadWord o), r)
  let f : leechIsomSubgroup → MulAction.orbit leechIsomSubgroup x :=
    fun g => ⟨g • x, ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit leechIsomSubgroup x) := Finite.of_surjective f hf
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup x)
  let _ := Fintype.ofFinite (generatedAxisE8ShortFlagStabilizer o r)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group leechIsomSubgroup x
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (MulAction.orbit leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o), r)) *
      Nat.card (generatedAxisE8ShortFlagStabilizer o r) = Nat.card leechIsomSubgroup at h
  rw [generatedAxisE8ShortFlag_action_orbit, generatedAxisE8ShortFlagOrbit_card o r hr,
    co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5594589000)
    (h.trans (by decide : 8315553613086720000 = 5594589000 * 1486356480))

/-- Both central lattice signs preserve both components of every actual flag. -/
theorem generatedAxisE8Short_signs_le_flagStabilizer (o : Fin 759)
    (r : GriessShortIndex) : signsSubgroup ≤ generatedAxisE8ShortFlagStabilizer o r := by
  intro g hg
  rw [generatedAxisE8ShortFlagStabilizer_mem]
  refine ⟨(generatedAxisE8SectionStabilizer_mem _ g).mp
    (generatedAxisE8_signs_le_section_stabilizer _ hg), ?_⟩
  apply griessShortPermutation_binary_trivial
  change g ∈ leechBinaryAction.ker
  rwa [leechBinaryAction_ker]

/-- The actual flag stabilizer in the central-sign quotient Co1. -/
def generatedAxisE8Co1ShortFlagStabilizer (o : Fin 759) (r : GriessShortIndex) :
    Subgroup Co1 :=
  (generatedAxisE8ShortFlagStabilizer o r).map (QuotientGroup.mk' signsSubgroup)

/-- The genuine flag stabilizer index inside Co0. -/
theorem generatedAxisE8ShortFlagStabilizer_index (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    (generatedAxisE8ShortFlagStabilizer o r).index = 5594589000 := by
  have h := (generatedAxisE8ShortFlagStabilizer o r).card_mul_index
  rw [generatedAxisE8ShortFlagStabilizer_card o r hr, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1486356480)
    (h.trans (by decide : 8315553613086720000 = 1486356480 * 5594589000))

/-- Quotienting the genuine signs preserves the exact flag index. -/
theorem generatedAxisE8Co1ShortFlagStabilizer_index (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    (generatedAxisE8Co1ShortFlagStabilizer o r).index = 5594589000 := by
  change ((generatedAxisE8ShortFlagStabilizer o r).map
    (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedAxisE8ShortFlagStabilizer_index o r hr
  · rw [QuotientGroup.ker_mk']
    exact generatedAxisE8Short_signs_le_flagStabilizer o r

/-- The actual Co1 flag stabilizer has precisely 743,178,240 elements. -/
theorem generatedAxisE8Co1ShortFlagStabilizer_card (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8Co1ShortFlagStabilizer o r) = 743178240 := by
  have h := (generatedAxisE8Co1ShortFlagStabilizer o r).card_mul_index
  rw [generatedAxisE8Co1ShortFlagStabilizer_index o r hr, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 5594589000)
    (h.trans (by decide : 4157776806543360000 = 743178240 * 5594589000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
