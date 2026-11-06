/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionNormEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSeparation

/-! Exact intersection of the displayed Q classes with genuine incident norm-eight frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check the32 actual Q classes against the15 displayed nonzero incident classes.
/-- The sixteen section parameters consist of zero and the fifteen displayed frame classes. -/
theorem generatedFifthFrame_nonzero_intersection_certificate :
    ∀ (b : ZMod 2) (k : Fin 16),
      (generatedFifthFrameQClass b k ≠ 0 ∧
        ∃ j : Fin 8, generatedFifthFrameIntersectionParameters j = k) ↔
      ∃ j : Fin 15, generatedFifthFrameIncidentClass j = generatedFifthFrameQClass b k := by
  decide +kernel

/-- A displayed Q class is an actual incident frame exactly when it is one of the fifteen. -/
theorem generatedFifthFrame_incident_iff (b : ZMod 2) (k : Fin 16) :
    leechHyperbolicCoordinates.symm (generatedFifthFrameQClass b k) ∈
      generatedAxisE8FrameClasses
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) ↔
      ∃ j : Fin 15, generatedFifthFrameIncidentClass j = generatedFifthFrameQClass b k := by
  constructor
  · intro h
    have hs := generatedFifthFrame_incident_binary_span _ h
    rw [LinearEquiv.apply_symm_apply, generatedFifthFrame_binary_span_iff,
      generatedFifthFrame_intersection_certificate] at hs
    have hn : generatedFifthFrameQClass b k ≠ 0 := by
      obtain ⟨u, _, hu, hub⟩ := h
      intro hz
      have he : leechReduction u = 0 := by
        rw [hub]
        apply leechHyperbolicCoordinates.injective
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz
      exact generatedCo1GeometryPoints_norm_eight_ne_zero u hu he
    exact (generatedFifthFrame_nonzero_intersection_certificate b k).mp ⟨hn, hs⟩
  · rintro ⟨j, hj⟩
    rw [← hj]
    exact generatedFifthFrameIncidentClass_mem j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
