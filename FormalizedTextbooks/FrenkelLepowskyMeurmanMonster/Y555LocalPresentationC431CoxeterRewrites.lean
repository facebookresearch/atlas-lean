/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal square, commutation and braid checking in the original C431 source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431Centrality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A checked original Coxeter move at a zero-based word position. -/
inductive Y431CoxeterMove
  | square (position : ℕ)
  | commute (position : ℕ)
  | braid (position : ℕ)
  deriving DecidableEq

/-- Apply one move only when its literal square, commutation, or braid conditions hold. -/
def y431CoxeterStep (move : Y431CoxeterMove) (w : List (Fin 9)) : Option (List (Fin 9)) :=
  match move with
  | .square n => match w.drop n with
    | a :: b :: t => if a = b then some (w.take n ++ t) else none
    | _ => none
  | .commute n => match w.drop n with
    | a :: b :: t =>
      if a ≠ b ∧ ¬ y555Adjacent (y431Vertex a) (y431Vertex b) then
        some (w.take n ++ b :: a :: t) else none
    | _ => none
  | .braid n => match w.drop n with
    | a :: b :: c :: t =>
      if a = c ∧ y555Adjacent (y431Vertex a) (y431Vertex b) then
        some (w.take n ++ b :: a :: b :: t) else none
    | _ => none

/-- Every successful finite move preserves the exact original C431 group element. -/
theorem y431CoxeterStep_valid (move : Y431CoxeterMove) (w w' : List (Fin 9))
    (h : y431CoxeterStep move w = some w') :
    y431PositiveWord w = y431PositiveWord w' := by
  have he (n : ℕ) : w = w.take n ++ w.drop n := (List.take_append_drop n w).symm
  cases move with
  | square n =>
    simp only [y431CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    subst b
    rw [y431PositiveWord_append, y431PositiveWord_append]
    simp only [y431PositiveWord, List.map_cons, List.prod_cons]
    simp only [← mul_assoc, y431_generator_square, one_mul]
  | commute n =>
    simp only [y431CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    rw [y431PositiveWord_append, y431PositiveWord_append]
    simp only [y431PositiveWord, List.map_cons, List.prod_cons]
    rw [← mul_assoc (PresentedGroup.of a),
      y431_generator_commute a b hab.2, mul_assoc]
  | braid n =>
    simp only [y431CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b c t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    have hac := hab.1
    subst c
    rw [y431PositiveWord_append, y431PositiveWord_append]
    simp only [y431PositiveWord, List.map_cons, List.prod_cons]
    simpa only [mul_assoc] using congrArg
      (fun x => (w.take n |>.map fun v => (PresentedGroup.of v : Y431RPresentation)).prod *
        (x * (t.map fun v => (PresentedGroup.of v : Y431RPresentation)).prod))
      (y431_generator_braid a b hab.2)

/-- Execute a finite sequence of checked original Coxeter moves. -/
def y431CoxeterRun : List Y431CoxeterMove → List (Fin 9) → Option (List (Fin 9))
  | [], w => some w
  | move :: rest, w => (y431CoxeterStep move w).bind (y431CoxeterRun rest)

/-- A successfully replayed finite certificate proves an exact original word equality. -/
theorem y431CoxeterRun_valid (moves : List Y431CoxeterMove) (w w' : List (Fin 9))
    (h : y431CoxeterRun moves w = some w') :
    y431PositiveWord w = y431PositiveWord w' := by
  induction moves generalizing w with
  | nil => cases h; rfl
  | cons move rest ih =>
    simp only [y431CoxeterRun] at h
    cases hs : y431CoxeterStep move w with
    | none => simp only [hs, Option.bind_none] at h; contradiction
    | some v =>
      simp only [hs, Option.bind_some] at h
      exact (y431CoxeterStep_valid move w v hs).trans (ih v h)


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
