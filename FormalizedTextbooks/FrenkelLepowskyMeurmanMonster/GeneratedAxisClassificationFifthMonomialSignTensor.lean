/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorUnits

/-! Bind the source Golay sign lifts to their entire actual local tensor operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual fiber representative of the original source sign lift. -/
noncomputable def generatedFifthSignFiber (a : Fin 4096) (ε : ZMod 2 := 0) :
    localFiberSubgroup :=
  Classical.choose (QuotientGroup.mk_surjective (generatedFifthSignLocal a ε))

/-- The actual fiber maps to the chosen original source sign element. -/
theorem generatedFifth_sign_fiber_local (a : Fin 4096) (ε : ZMod 2) :
    localFiberIntoH (generatedFifthSignFiber a ε) = generatedFifthSignLocal a ε :=
  Classical.choose_spec (QuotientGroup.mk_surjective (generatedFifthSignLocal a ε))

/-- Its spatial projection is a lift of the prescribed genuine Golay sign isometry. -/
theorem generatedFifth_sign_fiber_projection (a : Fin 4096) (ε : ZMod 2) :
    (QuotientGroup.mk (generatedFifthSignFiber a ε).val.2 : Co1) =
      QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode a)) := by
  have hp := congrArg projH (generatedFifth_sign_fiber_local a ε)
  exact hp.trans (generatedFifth_sign_local_projection a ε)

/-- The whole actual local tensor operator has the proved source Y-basis action. -/
theorem generatedFifth_sign_tensor_Y (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (i : Fin 24) :
    localTensorRepresentation (generatedFifthSignFiber a ε) (trialityYTensor d i) =
      qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) • trialityYTensor e i := by
  have hh := generatedFifth_sign_Y_basis a ε d e h he i
  rw [← generatedFifth_sign_fiber_local] at hh
  have ht := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.2) hh
  rw [generatedFourth_local_tensor, griessConwayEncode_Y_basis] at ht
  rw [show griessConwayEncode
      (qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) •
        trialityXYZBasis 1 (finProdFinEquiv (e, i))) =
      qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) •
        griessConwayEncode (trialityXYZBasis 1 (finProdFinEquiv (e, i))) from
    griessConwayEncodeLinear.map_smul _ _, griessConwayEncode_Y_basis] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
