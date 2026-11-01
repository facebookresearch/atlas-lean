/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortQBitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortThetaSplitBinding

/-! Complete preferred-Q masks retain both twelve-coordinate source halves and the zero phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Place the actual translation and modulation source masks in their distinct coordinate halves. -/
def generatedSeventhXiShortQJoinMask (u m : Fin 4096) : ℕ := u.val ||| (m.val <<< 12)

/-- The joined mask decodes to both complete source-coordinate vectors. -/
theorem generatedSeventhXiShortQJoinMask_decode (u m : Fin 4096) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSeventhXiShortQJoinMask u m) =
      Fin.append (golayLabelCoefficients u) (golayLabelCoefficients m) := by
  funext k
  refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) k
  · have hn : ¬ i.val ≥ 12 := by omega
    simp only [monsterCo1GeometryBinaryMaskDecode, generatedSeventhXiShortQJoinMask,
      Fin.val_castAdd, Nat.testBit_or, Nat.testBit_shiftLeft, decide_eq_false hn,
      Bool.false_and, Bool.or_false, Fin.append_left, golayLabelCoefficients]
  · have hu : u.val.testBit (12 + i.val) = false := by
      apply Nat.testBit_eq_false_of_lt
      have hp : (2 : ℕ) ^ 12 ≤ 2 ^ (12 + i.val) := Nat.pow_le_pow_right (by decide) (by omega)
      exact lt_of_lt_of_le u.isLt hp
    have hn : 12 + i.val ≥ 12 := by omega
    simp only [monsterCo1GeometryBinaryMaskDecode, generatedSeventhXiShortQJoinMask,
      Fin.val_natAdd, Nat.testBit_or, Nat.testBit_shiftLeft, decide_eq_true hn,
      Bool.true_and, hu, Bool.false_or, Nat.add_sub_cancel_left,
      Fin.append_right, golayLabelCoefficients]

/-- Exact translation and modulation identities determine the entire preferred short lift. -/
theorem generatedSeventhXiShortQMask_preferred (r : GriessShortIndex) (u m : Fin 4096)
    (hu : spinTranslation (griessShortQ r) = golayLabelCoefficients u)
    (hm : spinModulation (griessShortQ r) = golayLabelCoefficients m) :
    griessShortQ r = generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask u m) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change leechHyperbolicCoordinates (griessShortClass r) =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSeventhXiShortQJoinMask u m)
    rw [generatedSeventhXiShortQJoinMask_decode]
    funext k
    refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      change spinTranslation (griessShortQ r) i = golayLabelCoefficients u i
      exact congrFun hu i
    · rw [Fin.append_right]
      change spinModulation (griessShortQ r) i = golayLabelCoefficients m i
      exact congrFun hm i
  · rfl

/-- A finite image-mask equality determines the actual preferred-label base image. -/
theorem generatedSeventhXiShortQMask_image_base (r s : GriessShortIndex)
    (u m v n : Fin 4096)
    (hr : griessShortQ r = generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask u m))
    (hs : griessShortQ s = generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask v n))
    (hmask : generatedSeventhXiShortQImageMask (generatedSeventhXiShortQJoinMask u m) =
      generatedSeventhXiShortQJoinMask v n) :
    (generatedSeventhXiPlaneQMatrixHom (griessShortQ r)).base = (griessShortQ s).base := by
  rw [hr, hs, generatedSeventhXiShortQMask_image]
  change ofAdd (monsterCo1GeometryBinaryMaskDecode _ ) =
    ofAdd (monsterCo1GeometryBinaryMaskDecode _)
  rw [hmask]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
