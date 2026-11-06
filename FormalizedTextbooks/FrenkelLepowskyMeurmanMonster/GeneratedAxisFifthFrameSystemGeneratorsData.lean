/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemIntrinsic

/-! The original signs and Xi permute the fifteen genuine fifth-system frame classes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic root coordinates of the fifteen original actual frame classes. -/
def generatedFifthFrameIntrinsicClass (j : Fin 15) : Fin 8 → ZMod 2 :=
  generatedAxisE8FrameLabelBits ((![65, 54, 119, 42, 107, 28, 93, 7, 70, 49, 112, 45, 108, 27,
    90]: Fin 15 → Fin 256) j)

/-- Source indices of the twelve original signs followed by the original Xi. -/
def generatedFifthFrameSignXiIndex (k : Fin 13) : Fin 18 :=
  if h : k.val < 12 then ⟨k.val, by omega⟩ else 17

/-- Actual target classes under each original sign or Xi generator. -/
def generatedFifthFrameSignXiTarget : Fin 13 → Fin 15 → Fin 15 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14], ![0, 2, 1, 4, 3, 5, 6, 7, 8, 10, 9, 12, 11, 13, 14], ![0, 2, 1,
    3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13], ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14,
    13], ![0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 12, 11, 14, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14], ![0, 1, 2, 4, 3, 6, 5, 7, 8, 9, 10, 12, 11, 14, 13], ![0, 1, 2, 3, 4,
    5, 6, 8, 7, 10, 9, 12, 11, 14, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ![7, 1, 9, 3, 11, 5, 13, 8, 0, 10, 2, 12, 4, 14, 6]]

set_option maxRecDepth 100000 in
/-- Every intrinsic label maps to the original actual binary frame coordinates. -/
theorem generatedFifthFrameIntrinsicClass_certificate : ∀ j : Fin 15,
    generatedFifthFrameBinaryMatrix *ᵥ generatedFifthFrameIntrinsicClass j =
      generatedFifthFrameIncidentClass j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check195 original root-matrix actions on eight binary coordinates.
/-- The true original generator matrices give the displayed frame-class transitions. -/
theorem generatedFifthFrameSignXi_certificate : ∀ k : Fin 13, ∀ j : Fin 15,
    generatedFifthSectionGeneratorBinary (generatedFifthFrameSignXiIndex k) *ᵥ
        generatedFifthFrameIntrinsicClass j =
      generatedFifthFrameIntrinsicClass (generatedFifthFrameSignXiTarget k j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
