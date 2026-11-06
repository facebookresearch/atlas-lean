/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2NeighborCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates

/-! Original sorted octad coordinates at the two standard root positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- If an original octad contains both root coordinates, they are its first two positions. -/
theorem leechRootedA2Octad_first_coordinates (d : Fin 759)
    (h0 : (golayEncodedMask (golayOctadLabel d).val).testBit 0 = true)
    (h1 : (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true) :
    golayOctadCoordinate d 0 = 0 ∧ golayOctadCoordinate d 1 = 1 := by
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)
  let e := t.orderIsoOfFin (golayOctad_support_card d)
  let q0 : t := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
  let q1 : t := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
  have hz : (e 0).val = (0 : Fin 24) := by
    have hh := e.monotone (Fin.zero_le (e.symm q0))
    rw [e.apply_symm_apply] at hh
    apply Fin.ext
    change (e 0).val.val ≤ 0 at hh
    omega
  have hn : e.symm q1 ≠ (0 : Fin 8) := by
    intro hh
    have hv := e.apply_symm_apply q1
    rw [hh] at hv
    have he := congrArg Subtype.val hv
    rw [hz] at he
    exact Fin.zero_ne_one he
  have hle : (1 : Fin 8) ≤ e.symm q1 := by
    have hv : (e.symm q1).val ≠ 0 := by
      intro hh
      exact hn (Fin.ext hh)
    change 1 ≤ (e.symm q1).val
    omega
  have ho : (e 1).val = (1 : Fin 24) := by
    have hh := e.monotone hle
    rw [e.apply_symm_apply] at hh
    have hp := e.strictMono (show (0 : Fin 8) < 1 by decide)
    change (e 0).val < (e 1).val at hp
    rw [hz] at hp
    apply Fin.ext
    change (e 1).val.val ≤ 1 at hh
    change 0 < (e 1).val.val at hp
    omega
  exact ⟨hz, ho⟩

/-- A known occupied coordinate reads exactly its original local octad sign. -/
theorem leechRootedA2Octad_sign_at_coordinate (d : Fin 759) (e : Fin 64) (k : Fin 8) :
    (griessOctadSignMask d e).testBit (golayOctadCoordinate d k).val =
      (trialityEvenMask e).testBit k.val := by
  apply Bool.eq_iff_iff.mpr
  rw [griessOctadSignMask_testBit]
  constructor
  · rintro ⟨l, hl, he⟩
    have hh := golayOctadCoordinate_injective d he
    simpa only [hh] using hl
  · intro hh
    exact ⟨k, hh, rfl⟩

/-- The original octad-family root condition includes both coordinates and equal local signs. -/
theorem leechRootedA2Octad_neighbor_iff (d : Fin 759) (e : Fin 64) :
    leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (d, e))) ↔
      ((golayEncodedMask (golayOctadLabel d).val).testBit 0 = true ∧
        (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true) ∧
      (trialityEvenMask e).testBit 0 = (trialityEvenMask e).testBit 1 := by
  have hb : ∀ (a b c f : Bool),
      ((if a then (if c then (-2 : ℤ) else 2) else 0) +
        (if b then (if f then (-2 : ℤ) else 2) else 0) = 4 ∨
       (if a then (if c then (-2 : ℤ) else 2) else 0) +
        (if b then (if f then (-2 : ℤ) else 2) else 0) = -4) ↔
        (a = true ∧ b = true) ∧ c = f := by decide +kernel
  have hr := hb ((golayEncodedMask (golayOctadLabel d).val).testBit 0)
    ((golayEncodedMask (golayOctadLabel d).val).testBit 1)
    ((griessOctadSignMask d e).testBit 0) ((griessOctadSignMask d e).testBit 1)
  change leechRootedA2NeighborPredicate (Sum.inr (Sum.inl (d, e))) ↔ _ at hr
  rw [hr]
  constructor <;> rintro ⟨⟨h0, h1⟩, hs⟩
  · have hc := leechRootedA2Octad_first_coordinates d h0 h1
    have hs0 := leechRootedA2Octad_sign_at_coordinate d e 0
    have hs1 := leechRootedA2Octad_sign_at_coordinate d e 1
    rw [hc.1] at hs0
    rw [hc.2] at hs1
    exact ⟨⟨h0, h1⟩, hs0.symm.trans (hs.trans hs1)⟩
  · have hc := leechRootedA2Octad_first_coordinates d h0 h1
    have hs0 := leechRootedA2Octad_sign_at_coordinate d e 0
    have hs1 := leechRootedA2Octad_sign_at_coordinate d e 1
    rw [hc.1] at hs0
    rw [hc.2] at hs1
    exact ⟨⟨h0, h1⟩, hs0.trans (hs.trans hs1.symm)⟩

/-- Actual increasing-catalogue octad indices containing the root coordinates. -/
abbrev leechRootedA2OctadIndex :=
  {d : Fin 759 // (golayEncodedMask (golayOctadLabel d).val).testBit 0 = true ∧
    (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true}

/-- The genuine octad-label map is injective. -/
theorem leechRootedA2Octad_label_injective : Function.Injective golayOctadLabel := by
  intro a b h
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  exact Subtype.ext h

/-- The original sorted catalogue identifies its rooted indices with the genuine Golay words. -/
noncomputable def leechRootedA2OctadIndexEquiv :
    leechRootedA2OctadIndex ≃ leechRootedA2OctadCode where
  toFun d := ⟨golayOctadLabel d.val, ⟨by
    rw [← golayMaskSupport_card]
    exact golayOctad_support_card d.val, d.property⟩⟩
  invFun d := ⟨monsterNortonOctadIndex d.val d.property.1, by
    rw [monsterNortonOctadIndex_label]
    exact d.property.2⟩
  left_inv d := by
    apply Subtype.ext
    apply leechRootedA2Octad_label_injective
    dsimp only
    apply monsterNortonOctadIndex_label
  right_inv d := by
    apply Subtype.ext
    dsimp only
    apply monsterNortonOctadIndex_label

/-- The original octad short-vector addresses meeting the actual root condition. -/
abbrev leechRootedA2OctadNeighbor :=
  {p : Fin 759 × Fin 64 // leechRootedA2NeighborPredicate (Sum.inr (Sum.inl p))}

/-- Both actual coordinate and sign criteria give the complete octad-family identification. -/
noncomputable def leechRootedA2OctadNeighborEquiv :
    leechRootedA2OctadNeighbor ≃ leechRootedA2OctadCode × leechRootedA2OctadSign :=
  ((Equiv.subtypeEquivRight (fun p : Fin 759 × Fin 64 =>
    leechRootedA2Octad_neighbor_iff p.1 p.2)).trans
      (@Equiv.subtypeProdEquivProd (Fin 759) (Fin 64)
        (fun d => (golayEncodedMask (golayOctadLabel d).val).testBit 0 = true ∧
          (golayEncodedMask (golayOctadLabel d).val).testBit 1 = true)
        (fun e => (trialityEvenMask e).testBit 0 = (trialityEvenMask e).testBit 1))).trans
    (Equiv.prodCongr leechRootedA2OctadIndexEquiv (Equiv.refl _))

/-- Exactly2464 original octad short classes meet the root condition. -/
theorem leechRootedA2OctadNeighbor_card : Fintype.card leechRootedA2OctadNeighbor = 2464 := by
  rw [Fintype.card_congr leechRootedA2OctadNeighborEquiv, Fintype.card_prod,
    leechRootedA2OctadCode_card, leechRootedA2OctadSign_card]

/-- Splitting the actual original catalogue recovers all three genuine neighbor families. -/
def leechRootedA2NeighborFamilyEquiv : leechRootedA2NeighborAddress ≃
    leechRootedA2PairNeighbor ⊕ (leechRootedA2OctadNeighbor ⊕ leechRootedA2OddNeighbor) :=
  (Equiv.subtypeSum (p := leechRootedA2NeighborPredicate)).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeSum
      (p := fun p => leechRootedA2NeighborPredicate (Sum.inr p))))

/-- Exactly4600 genuine original short classes have absolute root pairing sixteen. -/
theorem leechRootedA2NeighborAddress_card : Fintype.card leechRootedA2NeighborAddress = 4600 := by
  rw [Fintype.card_congr leechRootedA2NeighborFamilyEquiv, Fintype.card_sum,
    Fintype.card_sum, leechRootedA2PairNeighbor_card, leechRootedA2OctadNeighbor_card,
    leechRootedA2OddNeighbor_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
