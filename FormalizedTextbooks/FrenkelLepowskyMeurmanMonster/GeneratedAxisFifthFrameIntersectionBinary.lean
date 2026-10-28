/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionSpan

/-! Actual binary rank and finite intersection certificates in the selected octad section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A literal left inverse of the selected eight-root binary matrix. -/
def generatedFifthFrameLeftInverse : Matrix (Fin 8) (Fin 24) (ZMod 2) :=
  ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The actual eight root classes are linearly independent. -/
theorem generatedFifthFrame_left_inverse :
    generatedFifthFrameLeftInverse * generatedFifthFrameBinaryMatrix = 1 := by
  decide +kernel

/-- Binary membership in the actual section root span is equivalent to exact reconstruction. -/
theorem generatedFifthFrame_binary_span_iff (v : Fin 24 → ZMod 2) :
    v ∈ generatedFifthFrameBinarySpan ↔
      generatedFifthFrameBinaryMatrix *ᵥ (generatedFifthFrameLeftInverse *ᵥ v) = v := by
  constructor
  · rintro ⟨a, rfl⟩
    change generatedFifthFrameBinaryMatrix *ᵥ
      (generatedFifthFrameLeftInverse *ᵥ (generatedFifthFrameBinaryMatrix *ᵥ a)) =
        generatedFifthFrameBinaryMatrix *ᵥ a
    have he : generatedFifthFrameLeftInverse *ᵥ (generatedFifthFrameBinaryMatrix *ᵥ a) = a := by
      rw [Matrix.mulVec_mulVec, generatedFifthFrame_left_inverse, Matrix.one_mulVec]
    rw [he]
  · intro h
    exact ⟨generatedFifthFrameLeftInverse *ᵥ v, h⟩

/-- The actual sixteen binary modulation labels from the fifth tensor equations. -/
def generatedFifthFrameModulationLabels : Fin 16 → Fin 4096 :=
  ![0, 48, 64, 112, 656, 672, 720, 736,
    1024, 1072, 1088, 1136, 1680, 1696, 1744, 1760]

/-- Binary Q classes with actual Omega translation and displayed actual modulation labels. -/
def generatedFifthFrameQClass (b : ZMod 2) (k : Fin 16) : Fin 24 → ZMod 2 :=
  Fin.append (fun i : Fin 12 => if i = 11 then b else 0)
    (golayLabelCoefficients (generatedFifthFrameModulationLabels k))

/-- The eight modulation parameters whose actual binary classes lie in the selected section. -/
def generatedFifthFrameIntersectionParameters : Fin 8 → Fin 16 := ![0, 3, 4, 7, 8, 11, 12, 15]

set_option maxHeartbeats 4000000 in
-- Check all32 actual binary classes against the verified eight-root reconstruction.
/-- Exactly sixteen displayed Q classes belong to the actual selected binary root span. -/
theorem generatedFifthFrame_intersection_certificate : ∀ (b : ZMod 2) (k : Fin 16),
    generatedFifthFrameBinaryMatrix *ᵥ
      (generatedFifthFrameLeftInverse *ᵥ generatedFifthFrameQClass b k) =
        generatedFifthFrameQClass b k ↔
          ∃ j : Fin 8, generatedFifthFrameIntersectionParameters j = k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
