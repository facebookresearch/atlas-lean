/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSupportData

/-! Exact exhaustive parametrization of the genuine tensor's two binary kernels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The ten original free-coordinate basis labels of the two triangle-sign kernels. -/
def generatedSeventhXiTensorSupportBasis : Fin 10 → ℕ :=
  ![1, 2, 4, 8, 96, 176, 304, 528, 1056, 2048]

/-- A tensor support label reconstructed from its ten actual free binary coordinates. -/
def generatedSeventhXiTensorSupportLabel (v : Fin 1024) : Fin 4096 :=
  ⟨((if v.val.testBit 0 then 1 else 0) ^^^
    (if v.val.testBit 1 then 2 else 0) ^^^
    (if v.val.testBit 2 then 4 else 0) ^^^
    (if v.val.testBit 3 then 8 else 0) ^^^
    (if v.val.testBit 4 then 96 else 0) ^^^
    (if v.val.testBit 5 then 176 else 0) ^^^
    (if v.val.testBit 6 then 304 else 0) ^^^
    (if v.val.testBit 7 then 528 else 0) ^^^
    (if v.val.testBit 8 then 1056 else 0) ^^^
    (if v.val.testBit 9 then 2048 else 0)) % 4096, Nat.mod_lt _ (by norm_num)⟩

/-- Projection to the ten original free coordinates of a complete spin label. -/
def generatedSeventhXiTensorSupportParameter (d : Fin 4096) : Fin 1024 :=
  ⟨((if d.val.testBit 0 then 1 else 0) +
    (if d.val.testBit 1 then 2 else 0) +
    (if d.val.testBit 2 then 4 else 0) +
    (if d.val.testBit 3 then 8 else 0) +
    (if d.val.testBit 6 then 16 else 0) +
    (if d.val.testBit 7 then 32 else 0) +
    (if d.val.testBit 8 then 64 else 0) +
    (if d.val.testBit 9 then 128 else 0) +
    (if d.val.testBit 10 then 256 else 0) +
    (if d.val.testBit 11 then 512 else 0)) % 1024, Nat.mod_lt _ (by norm_num)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Each actual support parameter is checked against both original syndrome rows.
/-- Every reconstructed parameter label satisfies both genuine support constraints. -/
theorem generatedSeventhXiTensorSupportLabel_mem : ∀ v : Fin 1024,
    generatedSeventhXiTensorSupported (generatedSeventhXiTensorSupportLabel v).val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The full 4096-label source universe is retained by this finite reconstruction certificate.
/-- Every genuine support label is recovered from its ten free coordinates. -/
theorem generatedSeventhXiTensorSupportLabel_complete : ∀ d : Fin 4096,
    generatedSeventhXiTensorSupported d.val →
      generatedSeventhXiTensorSupportLabel (generatedSeventhXiTensorSupportParameter d) = d := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
