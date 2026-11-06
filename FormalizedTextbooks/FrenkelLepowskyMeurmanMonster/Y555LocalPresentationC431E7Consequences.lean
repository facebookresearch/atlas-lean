/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual square and E7 centrality consequences of the checked original C431 Coxeter equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7Boundaries

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Interpret a signed word in the actual original C431 presentation. -/
def y431SignedWordValue (word : List (Fin 9 × Bool)) : Y431RPresentation :=
  y322EquationWordValue (fun i => (PresentedGroup.of i : Y431RPresentation)) word

/-- Positive signed words have their literal original-generator product. -/
theorem y431SignedWordValue_positive (word : List (Fin 9)) :
    y431SignedWordValue (word.map fun i => (i, true)) = y431PositiveWord word :=
  y431PositiveWord_signed word

/-- The empty signed word is the actual group identity. -/
theorem y431SignedWordValue_nil : y431SignedWordValue [] = 1 := by
  simp [y431SignedWordValue, y322EquationWordValue, FreeGroup.lift_mk]

set_option maxRecDepth 100000 in
/-- Each literal E7 rewrite row is valid in the original nine-generator presentation. -/
theorem y431E7ProofData_valid (row : Fin 185) :
    y431SignedWordValue (y431E7ProofData row).1.left =
      y431SignedWordValue (y431E7ProofData row).1.right := by
  have h := y431E7ProofProgram_valid (⟨171 + row.val, by omega⟩ : Fin 356)
  have hi : ¬ (171 + row.val < 171) := by omega
  have hr : (⟨171 + row.val - 171, by omega⟩ : Fin 185) = row := by
    apply Fin.ext
    change 171 + row.val - 171 = row.val
    omega
  change Y322WordEquation.Valid (fun v => (PresentedGroup.of v : Y431RPresentation))
    (y431E7ProofData row).1
  simpa only [y431E7ProofProgram, dite_eq_right hi, hr] using h

set_option maxRecDepth 100000 in
/-- The actual original F21 longest word is an involution, by the fully checked square chain. -/
theorem y431F21_square : (PresentedGroup.mk y431Relations y431F21) ^ 2 = 1 := by
  have hchain (i : Fin 39) :
      y431SignedWordValue (y431E7SquareSignedWord i) =
        y431SignedWordValue (y431E7SquareSignedWord 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have h := y431E7ProofData_valid (⟨i.val, by omega⟩ : Fin 185)
      rw [(y431E7Square_boundaries i).1, (y431E7Square_boundaries i).2] at h
      exact h.symm.trans ih
  have h := (hchain (Fin.last 38)).symm
  rw [y431E7Square_start, y431E7Square_end, y431SignedWordValue_positive,
    y431SignedWordValue_nil, y431PositiveWord_append, y431E7Positive21_value] at h
  simpa only [pow_two] using h

set_option maxRecDepth 100000 in
/-- The actual F21 commutes with every original generator of its E7 subsystem. -/
theorem y431F21_E7_central (g : Fin 7) :
    (PresentedGroup.of (y431E7Vertex g) : Y431RPresentation) *
        PresentedGroup.mk y431Relations y431F21 =
      PresentedGroup.mk y431Relations y431F21 * PresentedGroup.of (y431E7Vertex g) := by
  have hchain (i : Fin 22) :
      y431SignedWordValue (y431E7CentralSignedWord g i) =
        y431SignedWordValue (y431E7CentralSignedWord g 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have h := y431E7ProofData_valid (⟨38 + 21 * g.val + i.val, by omega⟩ : Fin 185)
      rw [(y431E7Central_boundaries g i).1, (y431E7Central_boundaries g i).2] at h
      exact h.symm.trans ih
  have h := (hchain (Fin.last 21)).symm
  rw [y431E7Central_start, y431E7Central_end, y431SignedWordValue_positive,
    y431SignedWordValue_nil, y431PositiveWord_append, y431PositiveWord_append,
    y431PositiveWord_append, y431PositiveWord_reverse, y431E7Positive21_value] at h
  have hg : y431PositiveWord [y431E7Vertex g] =
      (PresentedGroup.of (y431E7Vertex g) : Y431RPresentation) := by simp [y431PositiveWord]
  rw [hg] at h
  have he := congrArg (fun x => x * (PresentedGroup.of (y431E7Vertex g) : Y431RPresentation))
    (eq_of_mul_inv_eq_one h)
  simpa only [mul_assoc, y431_generator_square, mul_one] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
