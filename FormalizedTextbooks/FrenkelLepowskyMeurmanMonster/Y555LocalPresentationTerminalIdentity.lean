/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original terminal identities from the fully checked original-source coset replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetChecked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetTargets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original terminal f1 lies in the actual fixed subgroup, by literal source replay. -/
theorem y555TerminalFirst_mem_fixed :
    (PresentedGroup.of (some (0, 4)) : BimonsterPresentation) ∈ y522TerminalFixed := by
  have h := y522CosetProgram_valid_original y522CosetTerminalTarget
  change y522CosetWordValue (y522CosetProgram y522CosetTerminalTarget).1.left *
    (y522CosetWordValue (y522CosetProgram y522CosetTerminalTarget).1.right)⁻¹ ∈
      y522TerminalFixed at h
  rw [y522CosetTerminalTarget_words.1, y522CosetTerminalTarget_words.2,
    y522CosetWordValue_singleton, y522CosetGeneratorLetter_value,
    y522CosetWordValue_nil, inv_one, mul_one] at h
  exact h

/-- Original f1 is exactly the genuine longest word, without a presentation-kernel premise. -/
theorem y555TerminalFirst_eq_longest :
    (PresentedGroup.of (some (0, 4)) : BimonsterPresentation) = y555LocalF1 := by
  have h := y555TerminalFirst_mem_fixed
  change y555TerminalHom (PresentedGroup.of (some (0, 4))) =
    (PresentedGroup.of (some (0, 4)) : BimonsterPresentation) at h
  rw [y555TerminalHom_generator] at h
  exact h.symm

/-- The second original terminal identity follows under the genuine cyclic source map. -/
theorem y555TerminalSecond_eq_longest :
    (PresentedGroup.of (some (1, 4)) : BimonsterPresentation) = y555LocalF2 := by
  have h := congrArg y555CycleHom y555TerminalFirst_eq_longest
  have hv : y555VertexCycle (some (0, 4)) = some (1, 4) := by decide +kernel
  simpa only [y555CycleHom_generator, hv, y555LocalF2] using h

/-- The third original terminal identity is the second genuine cyclic image. -/
theorem y555TerminalThird_eq_longest :
    (PresentedGroup.of (some (2, 4)) : BimonsterPresentation) = y555LocalF3 := by
  have h := congrArg y555CycleHom y555TerminalSecond_eq_longest
  have hv : y555VertexCycle (some (1, 4)) = some (2, 4) := by decide +kernel
  simpa only [y555CycleHom_generator, hv, y555LocalF3] using h

/-- Each original terminal is its actual corrected longest word in the original presentation. -/
theorem y555Terminal_eq_longest (i : Fin 3) :
    (PresentedGroup.of (some (i, 4)) : BimonsterPresentation) = y555LocalLongest i := by
  fin_cases i
  · exact y555TerminalFirst_eq_longest
  · exact y555TerminalSecond_eq_longest
  · exact y555TerminalThird_eq_longest

/-- The literal terminal substitution is the identity on the entire original presentation. -/
theorem y555TerminalHom_eq_id :
    y555TerminalHom = MonoidHom.id BimonsterPresentation := by
  apply PresentedGroup.ext
  intro v
  change y555TerminalHom (PresentedGroup.of v) = PresentedGroup.of v
  rw [y555TerminalHom_generator]
  cases v with
  | none => rfl
  | some p =>
    rcases p with ⟨i, k⟩
    by_cases h : k = 4
    · simpa only [y555TerminalImage, h, ite_true] using (y555Terminal_eq_longest i).symm
    · simp only [y555TerminalImage, h, ite_false]

/-- The proved terminal-substitution endomorphism has trivial kernel in original Y555. -/
theorem y555TerminalHom_ker_eq_bot : y555TerminalHom.ker = ⊥ := by
  rw [y555TerminalHom_eq_id]
  exact MonoidHom.ker_id

/-- The three original terminal differences already vanish in the independent presentation. -/
theorem y555TerminalNormal_eq_bot : y555TerminalNormal = ⊥ := by
  rw [← y555TerminalHom_ker]
  exact y555TerminalHom_ker_eq_bot

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
