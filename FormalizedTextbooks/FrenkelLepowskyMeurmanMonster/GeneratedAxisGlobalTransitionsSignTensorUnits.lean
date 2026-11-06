/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorUnits

/-! Exact source sign action on every physical tensor coordinate unit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every physical input unit has an exact two-term actual source sign output packet. -/
theorem generatedAxisGlobalSign_tensor_unit (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (b h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (i : Fin 24) :
    Real.sqrt 2 • localTensorRepresentation (generatedFifthSignFiber a ε)
      (generatedAxisGlobalTensorUnit
        (generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex)) i) =
    ((qSign b * (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
      qSign (generatedAxisGlobalSignYPhase a ε d e)) • trialityYTensor e i +
    (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (generatedAxisGlobalSignZPhase a d i)) • trialityZTensor d i := by
  have hd := congrArg (localTensorRepresentation (generatedFifthSignFiber a ε))
    (generatedAxisGlobalTensorUnit_dictionary d b i)
  rw [map_smul, map_add, map_smul, map_smul,
    generatedAxisGlobalSign_tensor_Y_polynomial a ε d e h he i,
    generatedAxisGlobalSign_tensor_Z_polynomial] at hd
  simpa only [smul_smul] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
