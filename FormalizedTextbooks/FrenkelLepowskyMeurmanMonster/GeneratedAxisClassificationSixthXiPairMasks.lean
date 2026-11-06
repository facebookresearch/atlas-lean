/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSyndromeMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates

/-! Complete preferred pair masks use the original coordinate characters and omega correction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Full original preferred pair-Q mask from its genuine physical coordinate pair. -/
def generatedSixthXiPairMask (s : Fin 2) (p : Fin 276) : ℕ :=
  generatedSixthXiJoinMasks (nortonUIntegerLabel (if s = 0 then 0 else Pi.single 11 1))
    (Nat.xor (generatedSixthXiSyndromeColumns (griessCoordinatePair p).1)
      (generatedSixthXiSyndromeColumns (griessCoordinatePair p).2))

/-- The complete mask is every genuine preferred pair lift, including central coefficient zero. -/
theorem generatedSixth_xi_pair_mask_Q (s : Fin 2) (p : Fin 276) :
    griessShortQ (Sum.inl (s, p)) = generatedSixthXiMaskQ (generatedSixthXiPairMask s p) := by
  rw [← monsterNortonShortQSource_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append (if s = 0 then 0 else Pi.single 11 1) (griessPairSyndrome p) =
      monsterCo1GeometryBinaryMaskDecode (generatedSixthXiPairMask s p)
    rw [generatedSixthXiPairMask, generatedSixth_xi_join_masks_decode,
      nortonUIntegerLabel_inverse, monsterCo1GeometryBinaryMaskDecode_xor]
    congr 1
    funext k
    simp only [Pi.add_apply, generatedSixth_xi_syndrome_columns, griessPairSyndrome]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
