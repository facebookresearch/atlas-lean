/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The eight actual adjacent pair indices supporting the first pair-short matrix packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original increasing index for the physical pair (2k,2k+1). -/
noncomputable def monsterNortonLine01AdjacentPair (k : Fin 8) : Fin 276 :=
  griessPairIndex ⟨2 * k.val, by omega⟩ ⟨2 * k.val + 1, by omega⟩
    (ne_of_lt (show (⟨2 * k.val, by omega⟩ : Fin 24) < ⟨2 * k.val + 1, by omega⟩ by
      change 2 * k.val < 2 * k.val + 1
      omega))

/-- Its genuine physical coordinates are the displayed adjacent pair. -/
theorem monsterNortonLine01AdjacentPair_coordinates (k : Fin 8) :
    griessCoordinatePair (monsterNortonLine01AdjacentPair k) =
      (⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩) := by
  rw [monsterNortonLine01AdjacentPair, griessPairIndex_coordinates]
  have h : (⟨2 * k.val, by omega⟩ : Fin 24) < ⟨2 * k.val + 1, by omega⟩ := by
    change 2 * k.val < 2 * k.val + 1
    omega
  simp only [h, ite_true]

/-- All eight original pair labels are distinct. -/
theorem monsterNortonLine01AdjacentPair_injective :
    Function.Injective monsterNortonLine01AdjacentPair := by
  intro a b h
  have hc := congrArg (fun p : Fin 276 => (griessCoordinatePair p).1.val) h
  rw [monsterNortonLine01AdjacentPair_coordinates,
    monsterNortonLine01AdjacentPair_coordinates] at hc
  apply Fin.ext
  change 2 * a.val = 2 * b.val at hc
  omega

/-- The actual adjacent-pair slot of each reached inverse-U output. -/
def monsterNortonLine01PairInversePhysicalSlot (e : Fin 64) : Fin 8 :=
  ⟨(monsterNortonLine01PairInversePairFirst e).val / 2, by revert e; decide +kernel⟩

/-- Each reached first coordinate equals twice its finite slot. -/
theorem monsterNortonLine01PairInversePhysicalSlot_first (e : Fin 64) :
    (monsterNortonLine01PairInversePairFirst e).val =
      2 * (monsterNortonLine01PairInversePhysicalSlot e).val := by
  revert e
  decide +kernel

/-- Each reached second coordinate is its genuine adjacent partner. -/
theorem monsterNortonLine01PairInversePhysicalSlot_second (e : Fin 64) :
    (monsterNortonLine01PairInversePairSecond e).val =
      2 * (monsterNortonLine01PairInversePhysicalSlot e).val + 1 := by
  revert e
  decide +kernel

/-- The actual source pair label is precisely the original adjacent label of its finite slot. -/
theorem monsterNortonLine01PairInversePhysicalPair_slot (e : Fin 64) :
    monsterNortonLine01PairInversePhysicalPair e =
      monsterNortonLine01AdjacentPair (monsterNortonLine01PairInversePhysicalSlot e) := by
  unfold monsterNortonLine01PairInversePhysicalPair monsterNortonLine01AdjacentPair
  have hf : monsterNortonLine01PairInversePairFirst e =
      (⟨2 * (monsterNortonLine01PairInversePhysicalSlot e).val, by omega⟩ : Fin 24) :=
    Fin.ext (monsterNortonLine01PairInversePhysicalSlot_first e)
  have hs : monsterNortonLine01PairInversePairSecond e =
      (⟨2 * (monsterNortonLine01PairInversePhysicalSlot e).val + 1, by omega⟩ : Fin 24) :=
    Fin.ext (monsterNortonLine01PairInversePhysicalSlot_second e)
  simp only [hf, hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
