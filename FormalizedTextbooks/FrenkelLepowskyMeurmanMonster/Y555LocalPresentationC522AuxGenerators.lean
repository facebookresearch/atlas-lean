/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual original C522 generators and its already proved redundant longest-word symbol. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522WordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original C522 generators followed by the genuine already proved F1 involution. -/
def y522AuxGenerator (i : Fin 11) : BimonsterPresentation :=
  if h : i.val < 10 then PresentedGroup.of (y522Vertex ⟨i.val, h⟩)
  else y555LocalF1

/-- Embed an original source letter into the alphabet with the redundant longest symbol. -/
def y522AuxOriginalLetter (i : Fin 10) : Fin 11 := ⟨i.val, by omega⟩

/-- An embedded original letter retains its exact original Y555 generator value. -/
theorem y522AuxGenerator_original (i : Fin 10) :
    y522AuxGenerator (y522AuxOriginalLetter i) =
      (PresentedGroup.of (y522Vertex i) : BimonsterPresentation) := by
  unfold y522AuxGenerator y522AuxOriginalLetter
  dsimp only
  rw [dite_eq_left i.isLt]

/-- The redundant eleventh symbol is exactly the genuine original first longest word. -/
theorem y522AuxGenerator_ten : y522AuxGenerator 10 = y555LocalF1 := rfl

/-- Every actual source or redundant generator is an involution by proved Y555 relations. -/
theorem y522AuxGenerator_square (i : Fin 11) : y522AuxGenerator i * y522AuxGenerator i = 1 := by
  by_cases h : i.val < 10
  · simpa only [y522AuxGenerator, dite_eq_left h, pow_two] using
      y555_generator_sq (y522Vertex ⟨i.val, h⟩)
  · have hi : i = 10 := by apply Fin.ext; change i.val = 10; omega
    subst i
    exact y555LocalF1_square

/-- Literal positive source words are evaluated in the actual independent Y555 group. -/
def y522AuxPositiveWord (word : List (Fin 11)) : BimonsterPresentation :=
  (word.map y522AuxGenerator).prod

/-- Concatenating literal source words multiplies their exact actual group values. -/
theorem y522AuxPositiveWord_append (a b : List (Fin 11)) :
    y522AuxPositiveWord (a ++ b) = y522AuxPositiveWord a * y522AuxPositiveWord b := by
  simp [y522AuxPositiveWord]

/-- Repeating a literal source word gives its exact actual group power. -/
theorem y522AuxPositiveWord_replicate (word : List (Fin 11)) (n : ℕ) :
    y522AuxPositiveWord (List.replicate n word).flatten = y522AuxPositiveWord word ^ n := by
  induction n with
  | zero => simp [y522AuxPositiveWord]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, y522AuxPositiveWord_append, ih]
    exact (pow_succ' _ n).symm

/-- Prepending one literal letter multiplies its actual generator by the remaining word. -/
theorem y522AuxPositiveWord_cons (g : Fin 11) (word : List (Fin 11)) :
    y522AuxPositiveWord (g :: word) = y522AuxGenerator g * y522AuxPositiveWord word := rfl

/-- A literal singleton word has exactly its actual source-generator value. -/
theorem y522AuxPositiveWord_singleton (g : Fin 11) :
    y522AuxPositiveWord [g] = y522AuxGenerator g := by simp [y522AuxPositiveWord]

/-- Reversing a positive involutory source word gives the inverse of its actual value. -/
theorem y522AuxPositiveWord_reverse (word : List (Fin 11)) :
    y522AuxPositiveWord word.reverse = (y522AuxPositiveWord word)⁻¹ := by
  induction word with
  | nil => simp [y522AuxPositiveWord]
  | cons g word ih =>
    have hi : (y522AuxGenerator g)⁻¹ = y522AuxGenerator g :=
      inv_eq_of_mul_eq_one_right (y522AuxGenerator_square g)
    rw [List.reverse_cons, y522AuxPositiveWord_append, ih, y522AuxPositiveWord_singleton,
      y522AuxPositiveWord_cons, mul_inv_rev, hi]


/-- Exact source support of the first corrected longest word in this redundant alphabet. -/
def y522AuxF12Word : List (Fin 11) := (List.replicate 9 [0, 1, 5, 7, 2, 6, 3]).flatten

/-- Exact alternative corrected support of the same genuine longest word. -/
def y522AuxF13Word : List (Fin 11) := (List.replicate 9 [0, 1, 5, 7, 2, 8, 3]).flatten

/-- The literal first redundant-symbol defining word is the actual original F1. -/
theorem y522AuxF12Word_value : y522AuxPositiveWord y522AuxF12Word = y555LocalF1 := by
  rw [y522AuxF12Word, y522AuxPositiveWord_replicate, y555LocalF1_word12]
  simp [y522AuxPositiveWord, y522AuxGenerator, y522Vertex, y555LocalRestrictedWord,
    y555LocalF1Support12, y322Vertex]

/-- The literal alternative defining word is the same actual F1 by proved local equality. -/
theorem y522AuxF13Word_value : y522AuxPositiveWord y522AuxF13Word = y555LocalF1 := by
  rw [y522AuxF13Word, y522AuxPositiveWord_replicate, y555LocalF1_word13]
  simp [y522AuxPositiveWord, y522AuxGenerator, y522Vertex, y555LocalRestrictedWord,
    y555LocalF1Support13, y322Vertex]

/-- The nine original source vertices other than e1 used in proved F1 commutations. -/
def y522AuxNonE1 : Fin 9 → Fin 10 := ![0, 1, 2, 3, 5, 6, 7, 8, 9]

/-- All nine indexed vertices differ from the only possible exceptional e1 vertex. -/
theorem y522AuxNonE1_valid (i : Fin 9) : y522Vertex (y522AuxNonE1 i) ≠ some (0, 3) := by
  revert i
  decide +kernel

/-- Every numbered redundant-symbol commutation follows from the proved actual longest word. -/
theorem y522AuxGenerator_ten_commute (i : Fin 9) :
    Commute (y522AuxGenerator 10)
      (y522AuxGenerator (y522AuxOriginalLetter (y522AuxNonE1 i))) := by
  rw [y522AuxGenerator_ten, y522AuxGenerator_original]
  exact y555LocalF1_commute _ (y522AuxNonE1_valid i)

/-- The actual subgroup fixed by the proved terminal-substitution source endomorphism. -/
def y522TerminalFixed : Subgroup BimonsterPresentation :=
  y555TerminalHom.eqLocus (MonoidHom.id BimonsterPresentation)

/-- Ten fixed source symbols: the nine nonterminal original generators and redundant F1. -/
def y522AuxFixedSource : Fin 10 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10]

/-- Every indexed fixed source lies in the actual fixed subgroup, with original f1 excluded. -/
theorem y522AuxFixedSource_mem (i : Fin 10) :
    y522AuxGenerator (y522AuxFixedSource i) ∈ y522TerminalFixed := by
  change y555TerminalHom (y522AuxGenerator (y522AuxFixedSource i)) =
    y522AuxGenerator (y522AuxFixedSource i)
  fin_cases i
  · exact y522Nonterminal_fixed 0
  · exact y522Nonterminal_fixed 1
  · exact y522Nonterminal_fixed 2
  · exact y522Nonterminal_fixed 3
  · exact y522Nonterminal_fixed 4
  · exact y522Nonterminal_fixed 5
  · exact y522Nonterminal_fixed 6
  · exact y522Nonterminal_fixed 7
  · exact y522Nonterminal_fixed 8
  · exact y555TerminalHom_F1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
