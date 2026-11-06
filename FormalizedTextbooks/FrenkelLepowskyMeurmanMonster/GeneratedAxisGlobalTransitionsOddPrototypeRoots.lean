/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthRepresentative

/-! Actual phased prototype fibers and actual full odd-axis stabilizer root transports. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact frozen sixth, seventh and eighth phased local source fibers. -/
def generatedAxisGlobalOddPrototypeLocal : Fin 3 → H :=
  ![localFiberIntoH generatedSixthLocalFiber, localFiberIntoH generatedSeventhLocalFiber,
    localFiberIntoH generatedEighthLocalFiber]

/-- Every inverse source word is the entire inverse of its genuine phased prototype fiber. -/
theorem generatedAxisGlobalOddPrototype_inverse_word (k : Fin 3) :
    ((generatedAxisGlobalOddPrototypeInverseWords k).map
      generatedAxisGlobalOddSourceLocalLetter).prod =
      (generatedAxisGlobalOddPrototypeLocal k)⁻¹ := by
  fin_cases k <;>
    simp [generatedAxisGlobalOddPrototypeInverseWords, generatedAxisGlobalOddPrototypeLocal,
      generatedAxisGlobalOddSourceLocalLetter, generatedAxisGlobalOddSourceBaseLocal,
      generatedSixthLocalFiber, generatedSeventhLocalFiber, generatedEighthLocalFiber,
      mul_inv_rev]

private theorem sourceProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

/-- The actual inverse phased fibers have precisely the checked original binary root coordinates. -/
theorem generatedAxisGlobalOddPrototype_binary_root (k : Fin 3) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddPrototypeLocal k)).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddPrototypeMask k) := by
  have ho : monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 =
      toAdd (qQuotHom sourceOmegaQ) := by decide +kernel
  change co1BinaryAction (projH (generatedAxisGlobalOddPrototypeLocal k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← ho, ← generatedAxisGlobalOddPrototype_inverse_word,
    sourceProduct_binary, (generatedAxisGlobalOddPrototype_certificate k).1]

/-- Genuine full-axis-fixing local products, retaining every chosen lift's central correction. -/
def generatedAxisGlobalOddPrototypeTransport (k : Fin 3) : generatedOddLocalAxisStabilizer :=
  ((generatedAxisGlobalOddPrototypeTransportWords k).map generatedAxisGlobalOddGenerator).prod

private theorem stabilizerProduct_binary (ls : List (Fin 14)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map (fun l => (generatedAxisGlobalOddGenerator l).val)).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddBinaryRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddGenerator_projection, generatedAxisGlobalOddSpatial_binary,
      generatedAxisGlobalOddBinaryColumns_action, ← generatedAxisGlobalOddBinaryRows_action]

/-- The actual full-axis transporters send the genuine root words to the actual prototype roots. -/
theorem generatedAxisGlobalOddPrototypeTransport_actual (k : Fin 3) :
    generatedAxisGlobalBinaryAct (generatedAxisGlobalOddPrototypeTransport k).val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex k))) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddPrototypeLocal k) := by
  rw [generatedAxisGlobalOddSourceRootLocalWord_root]
  apply Subtype.ext
  change co1BinaryAction (projH (generatedAxisGlobalOddPrototypeTransport k).val)
    (generatedAxisGlobalOddRootBinary (generatedAxisGlobalOddPrototypeRootIndex k)) = _
  rw [generatedAxisGlobalOddPrototype_binary_root]
  have ht : (generatedAxisGlobalOddPrototypeTransport k).val =
      ((generatedAxisGlobalOddPrototypeTransportWords k).map
        (fun l => (generatedAxisGlobalOddGenerator l).val)).prod := by
    change (Subgroup.subtype _)
      (((generatedAxisGlobalOddPrototypeTransportWords k).map
        generatedAxisGlobalOddGenerator).prod) = _
    rw [map_list_prod, List.map_map]
    rfl
  rw [ht]
  change co1BinaryAction _ (monsterCo1GeometryBinaryMaskDecode
    (generatedAxisGlobalOddRootMask (generatedAxisGlobalOddPrototypeRootIndex k))) = _
  rw [stabilizerProduct_binary, (generatedAxisGlobalOddPrototype_certificate k).2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
