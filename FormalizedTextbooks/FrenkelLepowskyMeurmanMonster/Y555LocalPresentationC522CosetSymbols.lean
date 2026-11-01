/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-Y555 interpretation of every finite source and auxiliary path symbol. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The finite letter for one of the eleven actual original or redundant source symbols. -/
def y522CosetGeneratorLetter (i : Fin 11) : Fin 1806 := ⟨i.val, by omega⟩

/-- The finite letter of an exact acyclic path in the original independent Y555 group. -/
def y522CosetPathLetter (i : Fin 1795) : Fin 1806 := ⟨11 + i.val, by omega⟩

/-- Every symbol is an actual original generator or its explicitly acyclic source path. -/
noncomputable def y522CosetSymbol (i : Fin 1806) : BimonsterPresentation :=
  if h : i.val < 11 then y522AuxGenerator ⟨i.val, h⟩
  else y522TPathValue ⟨i.val - 11, by omega⟩

/-- Source letters retain their exact actual original-generator interpretations. -/
theorem y522CosetGeneratorLetter_value (i : Fin 11) :
    y522CosetSymbol (y522CosetGeneratorLetter i) = y522AuxGenerator i := by
  unfold y522CosetSymbol y522CosetGeneratorLetter
  dsimp only
  rw [dite_eq_left i.isLt]

/-- Path letters retain their exact actual acyclic source-word interpretations. -/
theorem y522CosetPathLetter_value (i : Fin 1795) :
    y522CosetSymbol (y522CosetPathLetter i) = y522TPathValue i := by
  have hn : ¬ (11 + i.val < 11) := by omega
  unfold y522CosetSymbol y522CosetPathLetter
  dsimp only
  rw [dite_eq_right hn]
  congr 1
  apply Fin.ext
  change 11 + i.val - 11 = i.val
  omega

/-- Actual group value of a signed finite source or auxiliary-path word. -/
noncomputable def y522CosetWordValue (word : List (Fin 1806 × Bool)) : BimonsterPresentation :=
  y322EquationWordValue y522CosetSymbol word

/-- The empty word is the actual group identity. -/
theorem y522CosetWordValue_nil : y522CosetWordValue [] = 1 := by
  simp [y522CosetWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- Positive singleton words have exactly their declared actual symbol values. -/
theorem y522CosetWordValue_singleton (i : Fin 1806) :
    y522CosetWordValue [(i, true)] = y522CosetSymbol i := by
  simp [y522CosetWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- Literal concatenation multiplies actual signed-word values. -/
theorem y522CosetWordValue_append (a b : List (Fin 1806 × Bool)) :
    y522CosetWordValue (a ++ b) = y522CosetWordValue a * y522CosetWordValue b :=
  y322EquationWordValue_append y522CosetSymbol a b

/-- Positive source encodings preserve their actual independent-Y555 generator products. -/
theorem y522CosetWordValue_positive (word : List (Fin 11)) :
    y522CosetWordValue (word.map fun i => (y522CosetGeneratorLetter i, true)) =
      y522AuxPositiveWord word := by
  unfold y522CosetWordValue y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_map, Function.comp_def, Bool.cond_true, y522CosetGeneratorLetter_value]
  rfl

/-- The empty root path is elided; every other path uses its own exact finite symbol. -/
def y522CosetPathWord (i : Fin 1795) : List (Fin 1806 × Bool) :=
  if i = 0 then [] else [(y522CosetPathLetter i, true)]

/-- The literal finite path encoding is exactly its actual independent-Y555 path value. -/
theorem y522CosetPathWord_value (i : Fin 1795) :
    y522CosetWordValue (y522CosetPathWord i) = y522TPathValue i := by
  by_cases hi : i = 0
  · subst i
    simp only [y522CosetPathWord, ite_true, y522CosetWordValue_nil, y522TPathValue_zero]
  · simp only [y522CosetPathWord, ite_eq_right hi, y522CosetWordValue_singleton,
      y522CosetPathLetter_value]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
