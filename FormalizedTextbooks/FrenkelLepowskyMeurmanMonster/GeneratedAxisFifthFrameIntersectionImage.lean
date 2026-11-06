/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionSystem
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthBinaryImage

/-! The actual frame system is exactly the full-axis Q image intersected with its section span. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Both literal dictionaries denote the same genuine binary Q classes. -/
theorem generatedFifthFrameQClass_actual (b : ZMod 2) (k : Fin 16) :
    generatedFifthFrameQClass b k =
      Fin.append (b • (Pi.single 11 1 : SpinIndex))
        (golayLabelCoefficients (generatedFifthModulationLabels k)) := by
  unfold generatedFifthFrameQClass
  have ht : (fun i : Fin 12 => if i = 11 then b else 0) =
      b • (Pi.single 11 1 : SpinIndex) := by
    ext i
    simp [Pi.single_apply]
  rw [ht]
  rfl

set_option maxHeartbeats 4000000 in
-- Check all sixteen vectors in the four-generator span against the section parameters.
/-- Every vector in the system span has actual Q parameters lying in the section. -/
theorem generatedFifthFrameSystem_parameter_certificate : ∀ a : Fin 4 → ZMod 2,
    ∃ b : ZMod 2, ∃ k : Fin 16,
      generatedFifthFrameQClass b k = generatedFifthFrameSystemMatrix *ᵥ a ∧
        ∃ j : Fin 8, generatedFifthFrameIntersectionParameters j = k := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the32 Q parameter choices against the sixteen actual system vectors.
/-- Every Q parameter lying in the section is in the actual four-generator span. -/
theorem generatedFifthFrameSystem_span_certificate : ∀ b : ZMod 2, ∀ k : Fin 16,
    (∃ j : Fin 8, generatedFifthFrameIntersectionParameters j = k) →
      ∃ a : Fin 4 → ZMod 2,
        generatedFifthFrameSystemMatrix *ᵥ a = generatedFifthFrameQClass b k := by
  decide +kernel

/-- The actual system span is exactly the full-axis Q image inside its actual section span. -/
theorem generatedFifthFrameSystemBinary_mem (v : Fin 24 → ZMod 2) :
    v ∈ generatedFifthFrameSystemBinary ↔
      v ∈ generatedFifthAxisBinaryImage ∧ v ∈ generatedFifthFrameBinarySpan := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, k, hk, hj⟩ := generatedFifthFrameSystem_parameter_certificate a
    refine ⟨(generatedFifth_axis_binary_image_mem _).mpr ⟨b, k, ?_⟩, ?_⟩
    · exact (generatedFifthFrameQClass_actual b k).symm.trans hk
    · change generatedFifthFrameSystemMatrix *ᵥ a ∈ generatedFifthFrameBinarySpan
      rw [← hk, generatedFifthFrame_binary_span_iff,
        generatedFifthFrame_intersection_certificate]
      exact hj
  · rintro ⟨hi, hs⟩
    obtain ⟨b, k, hk⟩ := (generatedFifth_axis_binary_image_mem v).mp hi
    rw [← generatedFifthFrameQClass_actual b k] at hk
    rw [← hk, generatedFifthFrame_binary_span_iff,
      generatedFifthFrame_intersection_certificate] at hs
    obtain ⟨a, ha⟩ := generatedFifthFrameSystem_span_certificate b k hs
    exact ⟨a, ha.trans hk⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
