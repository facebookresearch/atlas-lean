/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseCheck

/-! Exact complete source bindings of the original root-six positive candidate sparse coefficient packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- Every successful sparse lookup identifies its genuine original source label. -/
theorem generatedAxisGlobalOddRoot06OctadSparse_sound (r : GriessShortIndex) (p : Fin 120)
    (hp : generatedAxisGlobalOddRoot06OctadSparseSource r = some p) :
    generatedAxisGlobalOddRoot06OctadSourceLabel p = r := by
  apply generatedAxisGlobalShortNumber_injective
  exact generatedAxisGlobalSparseLookup_sound _ _ generatedAxisGlobalOddRoot06OctadSparse_valid _ _ hp

/-- The entire original 120-coordinate sum equals the exact candidate sparse coefficient at every label. -/
theorem generatedAxisGlobalOddRoot06OctadSparseShortQ_sum (r : GriessShortIndex) :
    (∑ p : Fin 120, generatedAxisGlobalOddRoot06OctadSourceCoefficient p *
      (if generatedAxisGlobalOddRoot06OctadSourceLabel p = r then 1 else 0)) =
      generatedAxisGlobalOddRoot06OctadSparseShortQ r := by
  have h := generatedAxisGlobalSparseLookup_sum _ _
    generatedAxisGlobalOddRoot06OctadSparse_roundtrip generatedAxisGlobalOddRoot06OctadSparse_sound
    generatedAxisGlobalOddRoot06OctadSourceCoefficient r
  cases hg : generatedAxisGlobalOddRoot06OctadSparseSource r <;>
    simpa only [generatedAxisGlobalOddRoot06OctadSparseShortQ, hg] using h

/-- Every listed nonzero original coefficient is the value returned at its exact source label. -/
theorem generatedAxisGlobalOddRoot06OctadSparseShortQ_source (p : Fin 120) :
    generatedAxisGlobalOddRoot06OctadSparseShortQ (generatedAxisGlobalOddRoot06OctadSourceLabel p) =
      generatedAxisGlobalOddRoot06OctadSourceCoefficient p := by
  simp only [generatedAxisGlobalOddRoot06OctadSparseShortQ,
    generatedAxisGlobalOddRoot06OctadSparse_roundtrip]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
