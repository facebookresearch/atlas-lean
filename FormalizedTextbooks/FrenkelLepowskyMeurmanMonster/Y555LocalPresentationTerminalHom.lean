/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine idempotent terminal-substitution endomorphism of the original Y555 group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTerminalImages

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original relation holds under the literal terminal substitution, including spider10. -/
theorem y555TerminalImage_relations (r : FreeGroup Y555Vertex) (hr : r ∈ y555Relations) :
    FreeGroup.lift y555TerminalImage r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y555TerminalImage_square v
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y555TerminalImage_coxeter u v huv
  · have h := PresentedGroup.one_of_mem (rels := y555Relations)
      (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
    simpa [y555Spider, y555TerminalImage, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of] using h

/-- The actual source endomorphism replacing the three terminal generators by longest words. -/
def y555TerminalHom : BimonsterPresentation →* BimonsterPresentation :=
  PresentedGroup.toGroup y555TerminalImage_relations

/-- Each original generator has exactly the specified literal substitution image. -/
@[simp] theorem y555TerminalHom_generator (v : Y555Vertex) :
    y555TerminalHom (PresentedGroup.of v) = y555TerminalImage v :=
  PresentedGroup.toGroup.of y555TerminalImage_relations

/-- The substitution fixes the first longest word because its seven letters are nonterminal. -/
theorem y555TerminalHom_F1 : y555TerminalHom y555LocalF1 = y555LocalF1 := by
  rw [y555LocalF1_word12]
  simp [y555LocalRestrictedWord, y555LocalF1Support12, y322Vertex,
    y555TerminalImage, map_pow, map_mul]

/-- The substitution fixes the second longest word because its seven letters are nonterminal. -/
theorem y555TerminalHom_F2 : y555TerminalHom y555LocalF2 = y555LocalF2 := by
  rw [y555LocalF2_word21]
  simp [y555TerminalImage, map_pow, map_mul]

/-- The substitution fixes the third longest word's seven cyclically relabeled letters. -/
theorem y555TerminalHom_F3 : y555TerminalHom y555LocalF3 = y555LocalF3 := by
  rw [y555LocalF3, y555LocalF2_word21]
  simp [map_pow, map_mul, y555CycleHom_generator, y555VertexCycle,
    y555ArmCycle, y555TerminalImage]

/-- Every indexed actual longest word is fixed by the actual source endomorphism. -/
theorem y555TerminalHom_longest (i : Fin 3) :
    y555TerminalHom (y555LocalLongest i) = y555LocalLongest i := by
  fin_cases i
  · exact y555TerminalHom_F1
  · exact y555TerminalHom_F2
  · exact y555TerminalHom_F3

/-- Applying the literal terminal substitution twice is the same actual source homomorphism. -/
theorem y555TerminalHom_idempotent :
    y555TerminalHom.comp y555TerminalHom = y555TerminalHom := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y555TerminalHom_generator]
  cases v with
  | none => exact y555TerminalHom_generator none
  | some p =>
    rcases p with ⟨i, k⟩
    by_cases h : k = 4
    · simpa only [y555TerminalImage, h, ite_true] using y555TerminalHom_longest i
    · simpa only [y555TerminalImage, h, ite_false] using
        y555TerminalHom_generator (some (i, k))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
