/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSupportData

/-! Exact vanishing of the full original tensor outside its binary support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- No absent code family can contribute an original odd coefficient. -/
theorem generatedSeventhXiTensorOddCache_zero (d : Fin 2048) (i : Fin 24)
    (hd : ¬ generatedSeventhXiTensorSupported d.val) :
    generatedSeventhXiTensorOddCache d i = 0 := by
  unfold generatedSeventhXiTensorOddCache
  split_ifs with h
  · exfalso
    have he := generatedSeventhXiOdd_packed_inverse d
    rw [dite_eq_left h] at he
    apply hd
    rw [← he]
    exact generatedSeventhXiTensorSupport_odd _
  · rfl

/-- Every coordinate of the actual tensor vanishes outside the two genuine kernels. -/
theorem generatedSeventhXiPlaneTensorPacked_zero (d : Fin 4096) (i : Fin 24)
    (hd : ¬ generatedSeventhXiTensorSupported d.val) :
    generatedSeventhXiPlaneTensorPacked d i = 0 := by
  have hc : ¬ generatedSeventhXiTensorSupported (generatedSeventhXiTensorLow d).val :=
    fun h => hd ((generatedSeventhXiTensorSupport_low d).1.mp h)
  have hh : ¬ generatedSeventhXiTensorSupported
      ((generatedSeventhXiTensorLow d).val + 2048) :=
    fun h => hd ((generatedSeventhXiTensorSupport_low d).2.mp h)
  let lo : Fin 4096 := ⟨(generatedSeventhXiTensorLow d).val, by omega⟩
  let hi : Fin 4096 := ⟨(generatedSeventhXiTensorLow d).val + 2048, by omega⟩
  have hlo : generatedSeventhXiTensorSpin lo = 0 :=
    generatedSeventhXiTensorSupport_spin lo hc
  have hhi : generatedSeventhXiTensorSpin hi = 0 :=
    generatedSeventhXiTensorSupport_spin hi hh
  have ho := generatedSeventhXiTensorOddCache_zero (generatedSeventhXiTensorLow d) i hc
  change (if (generatedSeventhXiTensorMask (generatedSeventhXiTensorLow d)).testBit i.val
        then -1 else 1) *
    ((if d.val.testBit 11 then -1 else 1) * 8 *
        generatedSeventhXiTensorOddCache (generatedSeventhXiTensorLow d) i -
      generatedSeventhXiTensorKappa (generatedSeventhXiTensorLow d) *
        generatedSeventhXiTensorFrame i *
          (generatedSeventhXiTensorSpin lo - generatedSeventhXiTensorSpin hi)) = 0
  rw [ho, hlo, hhi]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
