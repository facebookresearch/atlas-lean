/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-C422 interpretation of every finite source and auxiliary path symbol. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422TPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The finite letter for one of the nine actual original or redundant source symbols. -/
def y422CosetGeneratorLetter (i : Fin 9) : Fin 9042 := ⟨i.val, by omega⟩

/-- The finite letter of an exact acyclic path in the original independent C422/S/Q group. -/
def y422CosetPathLetter (i : Fin 9033) : Fin 9042 := ⟨9 + i.val, by omega⟩

/-- Every symbol is an actual original generator or its explicitly acyclic source path. -/
noncomputable def y422CosetSymbol (i : Fin 9042) : Y422Presentation :=
  if h : i.val < 9 then (PresentedGroup.of ⟨i.val, h⟩ : Y422Presentation)
  else y422TPathValue ⟨i.val - 9, by omega⟩

/-- Source letters retain their exact actual original-generator interpretations. -/
theorem y422CosetGeneratorLetter_value (i : Fin 9) :
    y422CosetSymbol (y422CosetGeneratorLetter i) = (PresentedGroup.of i : Y422Presentation) := by
  unfold y422CosetSymbol y422CosetGeneratorLetter
  dsimp only
  rw [dite_eq_left i.isLt]

/-- Path letters retain their exact actual acyclic source-word interpretations. -/
theorem y422CosetPathLetter_value (i : Fin 9033) :
    y422CosetSymbol (y422CosetPathLetter i) = y422TPathValue i := by
  have hn : ¬ (9 + i.val < 9) := by omega
  unfold y422CosetSymbol y422CosetPathLetter
  dsimp only
  rw [dite_eq_right hn]
  congr 1
  apply Fin.ext
  change 9 + i.val - 9 = i.val
  omega

/-- Actual group value of a signed finite source or auxiliary-path word. -/
noncomputable def y422CosetWordValue (word : List (Fin 9042 × Bool)) : Y422Presentation :=
  y322EquationWordValue y422CosetSymbol word

/-- The empty word is the actual group identity. -/
theorem y422CosetWordValue_nil : y422CosetWordValue [] = 1 := by
  simp [y422CosetWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- Positive singleton words have exactly their declared actual symbol values. -/
theorem y422CosetWordValue_singleton (i : Fin 9042) :
    y422CosetWordValue [(i, true)] = y422CosetSymbol i := by
  simp [y422CosetWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- Literal concatenation multiplies actual signed-word values. -/
theorem y422CosetWordValue_append (a b : List (Fin 9042 × Bool)) :
    y422CosetWordValue (a ++ b) = y422CosetWordValue a * y422CosetWordValue b :=
  y322EquationWordValue_append y422CosetSymbol a b

/-- Positive source encodings preserve their actual independent-C422/S/Q generator products. -/
theorem y422CosetWordValue_positive (word : List (Fin 9)) :
    y422CosetWordValue (word.map fun i => (y422CosetGeneratorLetter i, true)) =
      (word.map fun v => (PresentedGroup.of v : Y422Presentation)).prod := by
  unfold y422CosetWordValue y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_map, Function.comp_def, Bool.cond_true, y422CosetGeneratorLetter_value]

/-- The empty root path is elided; every other path uses its own exact finite symbol. -/
def y422CosetPathWord (i : Fin 9033) : List (Fin 9042 × Bool) :=
  if i = 0 then [] else [(y422CosetPathLetter i, true)]

/-- The literal finite path encoding is exactly its actual independent-C422/S/Q path value. -/
theorem y422CosetPathWord_value (i : Fin 9033) :
    y422CosetWordValue (y422CosetPathWord i) = y422TPathValue i := by
  by_cases hi : i = 0
  · subst i
    simp only [y422CosetPathWord, ite_true, y422CosetWordValue_nil, y422TPathValue_zero]
  · simp only [y422CosetPathWord, ite_eq_right hi, y422CosetWordValue_singleton,
      y422CosetPathLetter_value]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
