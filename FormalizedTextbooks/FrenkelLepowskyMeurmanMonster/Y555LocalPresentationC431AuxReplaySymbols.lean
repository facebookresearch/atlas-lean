/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual-group interpretation of the original-source replay's finite symbol alphabet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- Comparing literal word assignments requires the recursive auxiliary tables to unfold.
set_option maxRecDepth 100000

/-- The finite replay letter for each of the ten proved original-source generator values. -/
def y431AuxReplayGeneratorSymbol (i : Fin 10) : Fin 810 := ⟨i.val, by omega⟩

/-- The finite replay letter for an explicitly spelled H auxiliary word. -/
def y431AuxReplayHSymbol (i : Fin 620) : Fin 810 := ⟨10 + i.val, by omega⟩

/-- The finite replay letter for an explicitly spelled T auxiliary path. -/
def y431AuxReplayTSymbol (i : Fin 180) : Fin 810 := ⟨630 + i.val, by omega⟩

/-- Each initial symbol has exactly its proved original-generator interpretation. -/
theorem y431AuxReplayGeneratorSymbol_value (i : Fin 10) :
    y431AuxReplaySymbol (y431AuxReplayGeneratorSymbol i) = y431AuxGenerator i :=
  y431AuxReplaySymbol_generator i

/-- Each H symbol is its literal original C431 word, independently of any proposed trace. -/
theorem y431AuxReplayHSymbol_value (i : Fin 620) :
    y431AuxReplaySymbol (y431AuxReplayHSymbol i) = y431PositiveWord (y431AuxReplayHWord i) := by
  have h0 : ¬ (10 + i.val < 10) := by omega
  have h1 : 10 + i.val < 630 := by omega
  unfold y431AuxReplaySymbol y431AuxReplayHSymbol
  dsimp only
  rw [dite_eq_right h0, dite_eq_left h1]
  congr 2
  apply Fin.ext
  change 10 + i.val - 10 = i.val
  omega

/-- Each T symbol is its literal path evaluated inside the original C431 group. -/
theorem y431AuxReplayTSymbol_value (i : Fin 180) :
    y431AuxReplaySymbol (y431AuxReplayTSymbol i) =
      y431AuxPositiveWord (y431AuxReplayTWord i) := by
  have h0 : ¬ (630 + i.val < 10) := by omega
  have h1 : ¬ (630 + i.val < 630) := by omega
  unfold y431AuxReplaySymbol y431AuxReplayTSymbol
  dsimp only
  rw [dite_eq_right h0, dite_eq_right h1]
  congr 2
  apply Fin.ext
  change 630 + i.val - 630 = i.val
  omega

/-- Evaluate a signed replay word at its concrete original-group word assignments. -/
def y431AuxReplayWordValue (word : List (Fin 810 × Bool)) : Y431RPresentation :=
  y322EquationWordValue y431AuxReplaySymbol word

/-- The empty replay word has the actual group identity as its value. -/
theorem y431AuxReplayWordValue_nil : y431AuxReplayWordValue [] = 1 := by
  simp [y431AuxReplayWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- A positive singleton has exactly its declared actual symbol value. -/
theorem y431AuxReplayWordValue_singleton (i : Fin 810) :
    y431AuxReplayWordValue [(i, true)] = y431AuxReplaySymbol i := by
  simp [y431AuxReplayWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- A negative singleton has the actual inverse of its declared word value. -/
theorem y431AuxReplayWordValue_inverse_singleton (i : Fin 810) :
    y431AuxReplayWordValue [(i, false)] = (y431AuxReplaySymbol i)⁻¹ := by
  simp [y431AuxReplayWordValue, y322EquationWordValue, FreeGroup.lift_mk]

/-- Positive replay encodings preserve literal original-source word products. -/
theorem y431AuxReplayWordValue_positive (word : List (Fin 10)) :
    y431AuxReplayWordValue (word.map fun i => (y431AuxReplayGeneratorSymbol i, true)) =
      y431AuxPositiveWord word := by
  unfold y431AuxReplayWordValue y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_map, Function.comp_def, Bool.cond_true,
    y431AuxReplayGeneratorSymbol_value]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
