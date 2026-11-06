/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Propositional bridges from finite octad coordinate tables to the original dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine increasing-enumeration index of a certified source octad code. -/
noncomputable def monsterNortonOctadIndex (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩

/-- The original dictionary's octad code is exactly the certified input code. -/
theorem monsterNortonOctadIndex_label (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) :
    golayOctadLabel (monsterNortonOctadIndex a ha) = a := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩)

/-- Eight finite membership and sorted-position certificates recover the original local ordering. -/
theorem monsterNortonOctadIndex_coordinate (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (p : Fin 8 → Fin 24)
    (hm : ∀ k, (golayEncodedMask a.val).testBit (p k).val = true)
    (hi : ∀ k, (golayMaskSupport (golayEncodedMask a.val)).sort.idxOf (p k) = k.val)
    (k : Fin 8) : golayOctadCoordinate (monsterNortonOctadIndex a ha) k = p k := by
  let d := monsterNortonOctadIndex a ha
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)
  let e := t.orderIsoOfFin (golayOctad_support_card d)
  let v : t := ⟨p k, by
    simp only [t, d, monsterNortonOctadIndex_label, golayMaskSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact hm k⟩
  have hev : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport (golayEncodedMask
      (golayOctadLabel (monsterNortonOctadIndex a ha)).val)).sort.idxOf (p k) = k.val
    rw [monsterNortonOctadIndex_label]
    exact hi k
  have hv : e k = v := by rw [← hev, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The finite physical sign mask determined by eight displayed coordinate positions. -/
def monsterNortonOctadCoordinateSignMask (p : Fin 8 → Fin 24) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then 2 ^ (p k).val else 0) ||| m) 0

/-- The displayed-coordinate sign mask is the original dictionary mask. -/
theorem monsterNortonOctadCoordinateSignMask_eq (d : Fin 759) (p : Fin 8 → Fin 24)
    (hp : ∀ k, golayOctadCoordinate d k = p k) (e : Fin 64) :
    griessOctadSignMask d e = monsterNortonOctadCoordinateSignMask p e := by
  have hf : (fun (k : Fin 8) (m : ℕ) =>
      (if (trialityEvenMask e).testBit k.val then
        2 ^ (golayOctadCoordinate d k).val else 0) ||| m) =
      (fun (k : Fin 8) (m : ℕ) =>
        (if (trialityEvenMask e).testBit k.val then 2 ^ (p k).val else 0) ||| m) := by
    funext k m
    rw [hp]
  unfold griessOctadSignMask monsterNortonOctadCoordinateSignMask
  rw [hf]

/-- Computable physical coordinates for a displayed source octad and its even local sign pattern. -/
def monsterNortonOctadIntegral (a : Fin 4096) (p : Fin 8 → Fin 24) (e : Fin 64) :
    Fin 24 → ℤ := fun i =>
  if (golayEncodedMask a.val).testBit i.val then
    if (monsterNortonOctadCoordinateSignMask p e).testBit i.val then -2 else 2 else 0

/-- The finite octad formula is the original shortest-vector coordinate dictionary. -/
theorem monsterNortonOctadIntegral_eq (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (p : Fin 8 → Fin 24)
    (hp : ∀ k, golayOctadCoordinate (monsterNortonOctadIndex a ha) k = p k)
    (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))) =
      monsterNortonOctadIntegral a p e := by
  funext i
  simp only [griessShortIntegral, monsterNortonOctadIndex_label,
    monsterNortonOctadCoordinateSignMask_eq _ p hp, monsterNortonOctadIntegral]

/-- Preferred Q labels of all 64 local sign patterns are computed without dictionary enumeration. -/
theorem monsterNortonOctadShortQ_eq (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (p : Fin 8 → Fin 24)
    (hp : ∀ k, golayOctadCoordinate (monsterNortonOctadIndex a ha) k = p k)
    (e : Fin 64) :
    monsterNortonShortQ (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))) =
      (⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
        (monsterNortonLeechCoordinates (monsterNortonOctadIntegral a p e))), 1⟩ : Q) := by
  unfold monsterNortonShortQ
  rw [monsterNortonOctadIntegral_eq a ha p hp e]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
