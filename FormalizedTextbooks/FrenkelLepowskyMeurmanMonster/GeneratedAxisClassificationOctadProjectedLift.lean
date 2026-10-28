/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadLocalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift

/-! The actual spatial section stabilizer is covered by actual axis-fixing local lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine coordinate-section stabilizer element has a genuine local lift
fixing the actual triality octad axis, with exactly that spatial coordinate. -/
theorem generatedOctad_projected_stabilizer_lift (e : Fin 64) (c : ZMod 2)
    (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g (golayOctadWord generatedOctadBasisOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      rhoLocal (localFiberIntoH f)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)) =
        sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c) := by
  obtain ⟨f, hf⟩ := generatedCentral_localFiber_lift g
  have hfg : generatedAxisE8ImageSection f.val.2 (golayOctadWord generatedOctadBasisOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad) := by
    rw [hf]
    exact hg
  obtain ⟨q, hq⟩ := generatedOctad_local_lift_phase_correction e c f hfg
  refine ⟨localFiberIncl q * f, ?_, ?_⟩
  · change 1 * f.val.2 = g
    rw [one_mul, hf]
  · rw [map_mul]
    exact hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
