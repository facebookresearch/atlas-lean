/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The low label with block `q` and offset `a`. -/
private def blockLabel (q : Fin 4) (a : Fin 512) : Fin 2048 :=
  ⟨q.val * 512 + a.val, by have := q.isLt; have := a.isLt; omega⟩

private theorem blocks {P : Fin 2048 → Prop} (h : ∀ q : Fin 4, ∀ a : Fin 512, P (blockLabel q a))
    (e : Fin 2048) : P e := by
  have h' := h ⟨e.val / 512, by have := e.isLt; omega⟩ ⟨e.val % 512, Nat.mod_lt _ (by decide)⟩
  have he : blockLabel ⟨e.val / 512, by have := e.isLt; omega⟩
      ⟨e.val % 512, Nat.mod_lt _ (by decide)⟩ = e := by
    apply Fin.ext
    change e.val / 512 * 512 + e.val % 512 = e.val
    omega
  rw [he] at h'
  exact h'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 are checked.
private theorem packet0 : ∀ a : Fin 512,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 2)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 2) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 2) (blockLabel
              0 a)) (blockLabel 0 a)) =
      generatedFeasibleAmbientTenthSignPhase 2 0 (blockLabel 0 a) ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 2) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 2) (blockLabel 0 a) 0) =
      generatedFeasibleAmbientTenthSignPhase 2 1 (blockLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 are checked.
private theorem packet1 : ∀ a : Fin 512,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 2)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 2) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 2) (blockLabel
              1 a)) (blockLabel 1 a)) =
      generatedFeasibleAmbientTenthSignPhase 2 0 (blockLabel 1 a) ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 2) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 2) (blockLabel 1 a) 0) =
      generatedFeasibleAmbientTenthSignPhase 2 1 (blockLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 are checked.
private theorem packet2 : ∀ a : Fin 512,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 2)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 2) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 2) (blockLabel
              2 a)) (blockLabel 2 a)) =
      generatedFeasibleAmbientTenthSignPhase 2 0 (blockLabel 2 a) ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 2) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 2) (blockLabel 2 a) 0) =
      generatedFeasibleAmbientTenthSignPhase 2 1 (blockLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 are checked.
private theorem packet3 : ∀ a : Fin 512,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 2)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 2) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 2) (blockLabel
              3 a)) (blockLabel 3 a)) =
      generatedFeasibleAmbientTenthSignPhase 2 0 (blockLabel 3 a) ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 2) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 2) (blockLabel 3 a) 0) =
      generatedFeasibleAmbientTenthSignPhase 2 1 (blockLabel 3 a) := by
  decide +kernel

/-- Every source phase of root-two code 2304 is checked. -/
theorem generatedFeasibleAmbientTenth_sign_cache_check02 : ∀ e : Fin 2048,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 2)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 2) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 2) e) e) =
      generatedFeasibleAmbientTenthSignPhase 2 0 e ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 2) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 2) e 0) =
      generatedFeasibleAmbientTenthSignPhase 2 1 e := by
  apply blocks
  intro q
  fin_cases q
  · exact packet0
  · exact packet1
  · exact packet2
  · exact packet3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
