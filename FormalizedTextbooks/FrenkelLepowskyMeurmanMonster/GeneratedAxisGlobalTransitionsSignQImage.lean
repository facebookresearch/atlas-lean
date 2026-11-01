/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignSpinTensor
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorQFaithful

/-! The genuine source sign has its complete explicit extraspecial image on every
preferred label. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sign_spin_intertwines (a : Fin 2048) (q : Q) (x : SpinSpace) :
    (generatedAxisGlobalSignSpin a).val (spinRepresentation q x) =
      spinRepresentation (generatedAxisGlobalSignSpinImage a q)
        ((generatedAxisGlobalSignSpin a).val x) := by
  rw [← generatedAxisGlobalSignSpin_conjugation, spinConjugation_representation,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply]

private theorem sign_tensor_intertwines (a : Fin 2048) (q : Q)
    (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0)
        (localTensorRepresentation (localFiberIncl q) T) =
      localTensorRepresentation (localFiberIncl (generatedAxisGlobalSignSpinImage a q))
        (localTensorRepresentation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0)
          T) := by
  funext t i
  rw [generatedAxisGlobalSignLow_tensor, localTensorRepresentation_q]
  have hq : (fun u => localTensorRepresentation (localFiberIncl q) T u i) =
      spinRepresentation q (fun u => T u i) := by
    funext u
    exact localTensorRepresentation_q q T u i
  have hf : (fun u =>
      localTensorRepresentation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0)
        T u i) = qSign (golayEncoder (monsterNortonYCode a) i) •
          (generatedAxisGlobalSignSpin a).val (fun u => T u i) := by
    funext u
    exact generatedAxisGlobalSignLow_tensor a T u i
  rw [hq, hf, map_smul]
  change _ = qSign (golayEncoder (monsterNortonYCode a) i) * _
  rw [sign_spin_intertwines]

/-- Every genuine low source sign has this explicit all-Q image, with its full central phase. -/
theorem generatedAxisGlobalSignLow_QImage (a : Fin 2048) (q : Q) :
    spinConjugation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0).val.1 q =
      generatedAxisGlobalSignSpinImage a q := by
  apply generatedAxisGlobalTensor_Q_injective
  intro T
  obtain ⟨U, rfl⟩ :=
    (localTensorRepresentation
      (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0)).surjective T
  exact (generatedAxisGlobalTensor_Q_intertwine
    (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) q U).symm.trans
      (sign_tensor_intertwines a q U)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
