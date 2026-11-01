/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPropagationData

/-! Actual physical coordinates for the selected octad's 120 short-root inputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The eight original physical coordinates of code label sixteen. -/
def generatedFourthRootCoordinates : Fin 8 → Fin 24 := ![10, 11, 14, 15, 18, 19, 22, 23]

set_option maxHeartbeats 2000000 in
-- Check the finite coordinate ordering against the genuine octad mask.
/-- The displayed coordinates are exactly the original catalogue coordinates. -/
theorem generatedFourth_root_coordinates_certificate : ∀ k : Fin 8,
    golayOctadCoordinate generatedFourthOctad k = generatedFourthRootCoordinates k := by
  intro k
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel generatedFourthOctad).val)
  let e := t.orderIsoOfFin (golayOctad_support_card generatedFourthOctad)
  have hm : Nat.testBit 0xcccc00 (generatedFourthRootCoordinates k).val = true := by
    have hc : ∀ j : Fin 8,
        Nat.testBit 0xcccc00 (generatedFourthRootCoordinates j).val = true := by decide +kernel
    exact hc k
  let v : t := ⟨generatedFourthRootCoordinates k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedFourthOctad_mask]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel generatedFourthOctad).val)).sort.idxOf
        (generatedFourthRootCoordinates k) = k.val
    rw [generatedFourthOctad_mask]
    have hs : (golayMaskSupport 0xcccc00).sort =
        ([10, 11, 14, 15, 18, 19, 22, 23] : List (Fin 24)) := by
      apply (golayMaskSupport 0xcccc00).sortedLT_sort.eq_of_mem_iff (by decide +kernel)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j : Fin 24, j ∈ golayMaskSupport 0xcccc00 ↔
          j ∈ ([10, 11, 14, 15, 18, 19, 22, 23] : List (Fin 24)) := by decide +kernel
      exact hc i
    rw [hs]
    have hc : ∀ j : Fin 8, ([10, 11, 14, 15, 18, 19, 22, 23] : List (Fin 24)).idxOf
        (generatedFourthRootCoordinates j) = j.val := by decide +kernel
    exact hc k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The integer sign mask computed in the displayed physical coordinates. -/
def generatedFourthRootSignMask (e : Fin 64) : Nat :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then 2 ^ (generatedFourthRootCoordinates k).val else 0)
      ||| m) 0

/-- The displayed sign mask is the genuine preferred octad sign mask. -/
theorem generatedFourth_root_sign_mask (e : Fin 64) :
    griessOctadSignMask generatedFourthOctad e = generatedFourthRootSignMask e := by
  simp only [griessOctadSignMask, generatedFourth_root_coordinates_certificate,
    generatedFourthRootSignMask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
