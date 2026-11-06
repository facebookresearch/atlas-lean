/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source words at every boundary of the checked C431 E7 reductions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7ProofChecks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The seven actual C431 letters in the E7 subsystem centered on the second arm. -/
def y431E7Vertex : Fin 7 → Fin 9 := ![0, 5, 6, 7, 1, 2, 8]

/-- The literal positive word for the exact F21 ninth power. -/
def y431E7Positive21 : List (Fin 9) :=
  (List.replicate 9 ([0, 5, 1, 8, 6, 2, 7] : List (Fin 9))).flatten

/-- Interpret a positive original C431 generator word. -/
def y431PositiveWord (word : List (Fin 9)) : Y431RPresentation :=
  (word.map fun i => (PresentedGroup.of i : Y431RPresentation)).prod

/-- Positive signed evaluation is exactly the product of the actual original generators. -/
theorem y431PositiveWord_signed (word : List (Fin 9)) :
    y322EquationWordValue (fun i => (PresentedGroup.of i : Y431RPresentation))
      (word.map fun i => (i, true)) = y431PositiveWord word := by
  unfold y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_map, Function.comp_def, Bool.cond_true]
  rfl

/-- Positive concatenation multiplies its actual source values. -/
theorem y431PositiveWord_append (a b : List (Fin 9)) :
    y431PositiveWord (a ++ b) = y431PositiveWord a * y431PositiveWord b := by
  simp [y431PositiveWord]

/-- Repeating a literal positive word has its corresponding actual group power. -/
theorem y431PositiveWord_replicate (word : List (Fin 9)) (n : ℕ) :
    y431PositiveWord (List.replicate n word).flatten = y431PositiveWord word ^ n := by
  induction n with
  | zero => simp [y431PositiveWord]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, y431PositiveWord_append, ih]
    exact (pow_succ' _ n).symm

/-- The literal positive power is the original free-group F21 word in its presented quotient. -/
theorem y431E7Positive21_value :
    y431PositiveWord y431E7Positive21 = PresentedGroup.mk y431Relations y431F21 := by
  rw [y431E7Positive21, y431PositiveWord_replicate]
  simp [y431PositiveWord, y431F21, map_pow, map_mul, PresentedGroup.of, mul_assoc]

/-- Positive reversal inverts its value because each original generator is involutive. -/
theorem y431PositiveWord_reverse (word : List (Fin 9)) :
    y431PositiveWord word.reverse = (y431PositiveWord word)⁻¹ := by
  induction word with
  | nil => simp [y431PositiveWord]
  | cons i tail ih =>
    have hi : (PresentedGroup.of i : Y431RPresentation)⁻¹ = PresentedGroup.of i :=
      inv_eq_of_mul_eq_one_right (y431_generator_square i)
    simp only [List.reverse_cons, y431PositiveWord_append, ih]
    simp [y431PositiveWord, mul_inv_rev, hi]

/-- The exact thirty-nine boundary words of the original F21 square derivation. -/
def y431E7SquareSignedWord (i : Fin 39) : List (Fin 9 × Bool) :=
  if h : i.val < 38 then (y431E7ProofData ⟨i.val, by omega⟩).1.left
  else (y431E7ProofData 37).1.right

/-- The exact twenty-two boundary words for each original E7-generator commutator. -/
def y431E7CentralSignedWord (g : Fin 7) (i : Fin 22) : List (Fin 9 × Bool) :=
  if h : i.val < 21 then (y431E7ProofData ⟨38 + 21 * g.val + i.val, by omega⟩).1.left
  else (y431E7ProofData ⟨38 + 21 * g.val + 20, by omega⟩).1.right

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
