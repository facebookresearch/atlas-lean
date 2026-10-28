/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A proved redundant F21 symbol for the original C431/R source presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431CoxeterChains

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original nine generators together with the literal, already proved F21 involution. -/
def y431AuxGenerator (i : Fin 10) : Y431RPresentation :=
  if h : i.val < 9 then PresentedGroup.of ⟨i.val, h⟩
  else PresentedGroup.mk y431Relations y431F21

/-- Embed each original letter into the alphabet with the redundant tenth symbol. -/
def y431AuxOriginalLetter (i : Fin 9) : Fin 10 := ⟨i.val, by omega⟩

/-- Original letters retain exactly their actual presentation-generator values. -/
theorem y431AuxGenerator_original (i : Fin 9) :
    y431AuxGenerator (y431AuxOriginalLetter i) =
      (PresentedGroup.of i : Y431RPresentation) := by
  unfold y431AuxGenerator y431AuxOriginalLetter
  dsimp only
  rw [dite_eq_left i.isLt]

/-- The redundant symbol is exactly the original F21 word, with no extra group assumption. -/
theorem y431AuxGenerator_nine :
    y431AuxGenerator 9 = PresentedGroup.mk y431Relations y431F21 := rfl

/-- All ten interpreted symbols square to one by proved original-source consequences. -/
theorem y431AuxGenerator_square (i : Fin 10) :
    y431AuxGenerator i * y431AuxGenerator i = 1 := by
  by_cases h : i.val < 9
  · simpa only [y431AuxGenerator, dite_eq_left h] using
      y431_generator_square ⟨i.val, h⟩
  · have hi : i = 9 := by apply Fin.ext; change i.val = 9; omega
    subst i
    simpa only [y431AuxGenerator_nine, pow_two] using y431F21_square

/-- Evaluate a positive word in the redundant alphabet inside the original C431 group. -/
def y431AuxPositiveWord (word : List (Fin 10)) : Y431RPresentation :=
  (word.map y431AuxGenerator).prod

/-- Literal concatenation multiplies its actual original-source values. -/
theorem y431AuxPositiveWord_append (a b : List (Fin 10)) :
    y431AuxPositiveWord (a ++ b) = y431AuxPositiveWord a * y431AuxPositiveWord b := by
  simp [y431AuxPositiveWord]

/-- Repeating a literal redundant-alphabet word gives its actual group power. -/
theorem y431AuxPositiveWord_replicate (word : List (Fin 10)) (n : ℕ) :
    y431AuxPositiveWord (List.replicate n word).flatten = y431AuxPositiveWord word ^ n := by
  induction n with
  | zero => simp [y431AuxPositiveWord]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, y431AuxPositiveWord_append, ih]
    exact (pow_succ' _ n).symm

/-- Re-encoding an original word leaves its literal original-group value unchanged. -/
theorem y431AuxPositiveWord_original (word : List (Fin 9)) :
    y431AuxPositiveWord (word.map y431AuxOriginalLetter) = y431PositiveWord word := by
  simp only [y431AuxPositiveWord, y431PositiveWord, List.map_map, Function.comp_def,
    y431AuxGenerator_original]

/-- The redundant tenth symbol commutes with every original symbol by actual F21 centrality. -/
theorem y431AuxGenerator_nine_commute (i : Fin 9) :
    Commute (y431AuxGenerator 9) (y431AuxGenerator (y431AuxOriginalLetter i)) := by
  rw [y431AuxGenerator_nine, y431AuxGenerator_original]
  exact y431F21_generator_central i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
