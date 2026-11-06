/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWord
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! Phase-preserving actual local-fiber packets for the explicit fifth root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- One actual source stage in the defining spin/spatial fiber product. -/
def generatedAxisGlobalFifthShortNormalizationFiber (k : Fin 14) (j : Fin 7) :
    localFiberSubgroup :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then xiSpinLocalFiber else 1) *
    (generatedFifthSignFiber (generatedAxisGlobalFifthShortNormalizationSigns k j) 0 *
      ((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod)

/-- Every actual fiber stage maps to the identical original local word, including all phases. -/
theorem generatedAxisGlobalFifthShortNormalizationFiber_local (k : Fin 14) (j : Fin 7) :
    localFiberIntoH (generatedAxisGlobalFifthShortNormalizationFiber k j) =
      generatedAxisGlobalFifthShortNormalizationLocal k j := by
  rw [generatedAxisGlobalFifthShortNormalizationFiber, map_mul, map_mul,
    generatedFifth_sign_fiber_local, generatedAxisGlobalFifthShortNormalizationLocal]
  congr 1
  cases generatedAxisGlobalFifthShortNormalizationXi k j with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, map_one]
  | true => rfl

/-- The full chronological actual fiber word with all original source corrections retained. -/
def generatedAxisGlobalFifthShortWordFiber (k : Fin 14) : localFiberSubgroup :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationFiber k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The full fiber word is an exact lift of the explicit original local root word. -/
theorem generatedAxisGlobalFifthShortWordFiber_local (k : Fin 14) :
    localFiberIntoH (generatedAxisGlobalFifthShortWordFiber k) =
      generatedAxisGlobalFifthShortLocalWord k := by
  rw [generatedAxisGlobalFifthShortWordFiber, generatedAxisGlobalFifthShortLocalWord,
    generatedAxisGlobalWordChain_map]
  congr 1
  funext j
  exact generatedAxisGlobalFifthShortNormalizationFiber_local k _

/-- The actual full raw-coordinate action uses this identical phase-preserving fiber word. -/
theorem generatedAxisGlobalFifthShortWordFiber_encode (k : Fin 14) (x : GriessSpace) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) x) =
      localConwayRawRepresentation (generatedAxisGlobalFifthShortWordFiber k)
        (griessConwayEncode x) := by
  rw [← generatedAxisGlobalFifthShortWordFiber_local]
  exact localGriessRepresentation_encode _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
