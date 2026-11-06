/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source compatibility and both compositions of the Y444/Y555 maps. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444Images
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTerminalHom

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The C322 inclusion agrees exactly with its original Y555 source inclusion. -/
theorem y444IntoY555_comp_C322 :
    y444IntoY555.comp y444C322Hom = y322IntoY555 := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, y444C322Hom_generator, y444IntoY555_generator,
    y444C322Vertex_embed, y322IntoY555_generator]

/-- Inclusion of the independent first longest word gives the genuine original longest word. -/
theorem y444IntoY555_F1 : y444IntoY555 y444LocalF1 = y555LocalF1 := by
  have h := congrArg (fun f : Y322Presentation →* BimonsterPresentation =>
    f y322CentralInvolution) y444IntoY555_comp_C322
  simpa only [MonoidHom.comp_apply, y444LocalF1, y555LocalF1] using h

/-- The two genuine cyclic source maps commute with exact original inclusion. -/
theorem y444IntoY555_comp_cycle :
    y444IntoY555.comp y444CycleHom = y555CycleHom.comp y444IntoY555 := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y444CycleHom_generator, y444IntoY555_generator,
    y555CycleHom_generator, y444EmbedVertex_cycle]

/-- Inclusion retains the actual second corrected longest-word value. -/
theorem y444IntoY555_F2 : y444IntoY555 y444LocalF2 = y555LocalF2 := by
  have h := congrArg (fun f : Y444Presentation →* BimonsterPresentation =>
    f y444LocalF1) y444IntoY555_comp_cycle
  simpa only [MonoidHom.comp_apply, y444LocalF2, y555LocalF2, y444IntoY555_F1] using h

/-- Inclusion retains the actual third corrected longest-word value. -/
theorem y444IntoY555_F3 : y444IntoY555 y444LocalF3 = y555LocalF3 := by
  have h := congrArg (fun f : Y444Presentation →* BimonsterPresentation =>
    f y444LocalF2) y444IntoY555_comp_cycle
  simpa only [MonoidHom.comp_apply, y444LocalF3, y555LocalF3, y444IntoY555_F2] using h

/-- Every indexed longest word retains its exact original source value. -/
theorem y444IntoY555_longest (i : Fin 3) :
    y444IntoY555 (y444LocalLongest i) = y555LocalLongest i := by
  fin_cases i
  · exact y444IntoY555_F1
  · exact y444IntoY555_F2
  · exact y444IntoY555_F3

/-- Original terminal substitution fixes each of the thirteen embedded source generators. -/
theorem y555TerminalImage_embed (v : Y444Vertex) :
    y555TerminalImage (y444EmbedVertex v) = PresentedGroup.of (y444EmbedVertex v) := by
  cases v with
  | none => rfl
  | some p => rcases p with ⟨i, k⟩; fin_cases k <;> rfl

/-- The opposite composition is exactly the previously proved original terminal substitution. -/
theorem y444IntoY555_comp_reduction :
    y444IntoY555.comp y555IntoY444 = y555TerminalHom := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y555IntoY444_generator, y555TerminalHom_generator]
  rcases y444Y555_vertex_cases v with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · rw [y444Y555Image_embed, y444IntoY555_generator, y555TerminalImage_embed]
  · rw [y444Y555Image_terminal, y444IntoY555_longest]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
