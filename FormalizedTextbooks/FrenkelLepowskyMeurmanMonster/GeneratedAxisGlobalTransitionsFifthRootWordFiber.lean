/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootWord
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! Phase-preserving actual local-fiber packets for the explicit fifth root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- One actual source stage in the defining spin/spatial fiber product. -/
def generatedAxisGlobalFifthNormalizationFiber (k : Fin 14) (j : Fin 7) :
    localFiberSubgroup :=
  (if generatedAxisGlobalFifthNormalizationXi k j then xiSpinLocalFiber else 1) *
    (generatedFifthSignFiber (generatedAxisGlobalFifthNormalizationSigns k j) 0 *
      ((generatedAxisGlobalFifthNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod)

/-- Every actual fiber stage maps to the identical original local word, including all phases. -/
theorem generatedAxisGlobalFifthNormalizationFiber_local (k : Fin 14) (j : Fin 7) :
    localFiberIntoH (generatedAxisGlobalFifthNormalizationFiber k j) =
      generatedAxisGlobalFifthNormalizationLocal k j := by
  rw [generatedAxisGlobalFifthNormalizationFiber, map_mul, map_mul,
    generatedFifth_sign_fiber_local, generatedAxisGlobalFifthNormalizationLocal]
  congr 1
  cases generatedAxisGlobalFifthNormalizationXi k j with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, map_one]
  | true => rfl

/-- The full chronological actual fiber word with all original source corrections retained. -/
def generatedAxisGlobalFifthRootWordFiber (k : Fin 14) : localFiberSubgroup :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthNormalizationFiber k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The full fiber word is an exact lift of the explicit original local root word. -/
theorem generatedAxisGlobalFifthRootWordFiber_local (k : Fin 14) :
    localFiberIntoH (generatedAxisGlobalFifthRootWordFiber k) =
      generatedAxisGlobalFifthRootLocalWord k := by
  rw [generatedAxisGlobalFifthRootWordFiber, generatedAxisGlobalFifthRootLocalWord,
    generatedAxisGlobalWordChain_map]
  congr 1
  funext j
  exact generatedAxisGlobalFifthNormalizationFiber_local k _

/-- The actual full raw-coordinate action uses this identical phase-preserving fiber word. -/
theorem generatedAxisGlobalFifthRootWordFiber_encode (k : Fin 14) (x : GriessSpace) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalFifthRootLocalWord k) x) =
      localConwayRawRepresentation (generatedAxisGlobalFifthRootWordFiber k)
        (griessConwayEncode x) := by
  rw [← generatedAxisGlobalFifthRootWordFiber_local]
  exact localGriessRepresentation_encode _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
