/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! Complete spin/spatial fiber lifts of the nine original odd-family source root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original five source fibers, including the full quadratic permutation phases. -/
def generatedAxisGlobalOddSourceBaseFiber : Fin 5 → localFiberSubgroup :=
  ![xiSpinLocalFiber, generatedFifthSignFiber 16 0, generatedFifthSignFiber 32 0,
    monsterSourcePermutationFiber 0, monsterSourcePermutationFiber 1]

/-- Each complete fiber represents the identical original local source letter. -/
theorem generatedAxisGlobalOddSourceBaseFiber_local (k : Fin 5) :
    localFiberIntoH (generatedAxisGlobalOddSourceBaseFiber k) =
      generatedAxisGlobalOddSourceBaseLocal k := by
  fin_cases k
  · rfl
  · exact generatedFifth_sign_fiber_local 16 0
  · exact generatedFifth_sign_fiber_local 32 0
  · rfl
  · rfl

/-- A signed source fiber retains the genuine inverse of both spin and spatial factors. -/
def generatedAxisGlobalOddSourceFiberLetter (l : Fin 10) : localFiberSubgroup :=
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  if l.val % 2 = 1 then (generatedAxisGlobalOddSourceBaseFiber k)⁻¹
  else generatedAxisGlobalOddSourceBaseFiber k

/-- Every signed complete fiber has the exact previously checked local source image. -/
theorem generatedAxisGlobalOddSourceFiberLetter_local (l : Fin 10) :
    localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter l) =
      generatedAxisGlobalOddSourceLocalLetter l := by
  by_cases h : l.val % 2 = 1
  · simp only [generatedAxisGlobalOddSourceFiberLetter, generatedAxisGlobalOddSourceLocalLetter,
      h, ↓reduceIte, map_inv, generatedAxisGlobalOddSourceBaseFiber_local]
  · simp only [generatedAxisGlobalOddSourceFiberLetter, generatedAxisGlobalOddSourceLocalLetter,
      h, ↓reduceIte, generatedAxisGlobalOddSourceBaseFiber_local]

/-- The original product of complete fiber letters for each genuine norm-eight root. -/
def generatedAxisGlobalOddSourceRootFiber (k : Fin 9) : localFiberSubgroup :=
  ((generatedAxisGlobalOddSourceRootWords k).map generatedAxisGlobalOddSourceFiberLetter).prod

/-- The complete product lifts the identical root word, with every central phase retained. -/
theorem generatedAxisGlobalOddSourceRootFiber_local (k : Fin 9) :
    localFiberIntoH (generatedAxisGlobalOddSourceRootFiber k) =
      generatedAxisGlobalOddSourceRootLocalWord k := by
  rw [generatedAxisGlobalOddSourceRootFiber, generatedAxisGlobalOddSourceRootLocalWord,
    map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun _ _ => generatedAxisGlobalOddSourceFiberLetter_local _)

/-- The full raw-coordinate dictionary uses the same complete source fiber product. -/
theorem generatedAxisGlobalOddSourceRootFiber_encode (k : Fin 9) (x : GriessSpace) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) x) =
      localConwayRawRepresentation (generatedAxisGlobalOddSourceRootFiber k)
        (griessConwayEncode x) := by
  rw [← generatedAxisGlobalOddSourceRootFiber_local]
  exact localGriessRepresentation_encode _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
