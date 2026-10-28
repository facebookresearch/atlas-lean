/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The next literal Norton v step on the full inverse-triality source state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact reached short vector and two translated spin deltas for each source pair. -/
noncomputable def monsterNortonLine01SourcePairAfterV (t : SpinIndex) (i : Fin 24) :
    GriessSpace :=
  ((qSign (t 11) * (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val then -1
    else 1)) * qSign (monsterNortonSourceXQPhase y555NortonVQ (spinDictionaryCode t) i)) •
      trialityXYZBasis 0 (finProdFinEquiv (spinDictionaryCode t, i)) +
    qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) •
      monsterNortonTensorLift (conwaySpinColumn
        (monsterNortonSourceYQSpinImage y555NortonVQ (spinDictionaryCode t) i) i)

/-- The literal v image of each source pair uses the actual short sign and spin translations. -/
theorem monsterNortonLine01SourcePairAfterV_actual (t : SpinIndex) (i : Fin 24) :
    y555NortonV.val (monsterNortonLine01SourcePair t i) =
      monsterNortonLine01SourcePairAfterV t i := by
  rw [y555NortonV, monsterNortonLine01SourcePair, map_add, map_smul, map_smul,
    monsterNortonQ_source_X, monsterNortonQ_source_Y_explicit, smul_smul]
  rfl

/-- The complete rational source state after the next literal v in the first line-pair word. -/
noncomputable def monsterNortonLine01TensorAfterVUExtraInverseV : GriessSpace :=
  (1 / 64 : ℝ) • ∑ a : Fin 64,
    (monsterNortonLine01InitialSpinSigns a : ℝ) • ∑ i : Fin 24,
      (monsterNortonUNumerator1 i 0 : ℝ) •
        monsterNortonLine01SourcePairAfterV
          (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a)) i

/-- The fourth literal word step is an equality of complete actual Griess vectors. -/
theorem monsterNortonLine01TensorVSource_actual :
    y555NortonV.val monsterNortonLine01TensorAfterVUExtraInverse =
      monsterNortonLine01TensorAfterVUExtraInverseV := by
  rw [monsterNortonLine01TensorAfterVUExtraInverse, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonLine01SourcePairAfterV_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
