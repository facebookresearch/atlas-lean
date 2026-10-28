/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit square, commutation, and braid rewrite certificates for the source local group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCertificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Evaluation of a positive local generator word in the independent C322 presentation. -/
def y322PositiveWord (w : List (Fin 8)) : Y322Presentation :=
  (w.map fun v => (PresentedGroup.of v : Y322Presentation)).prod

/-- Concatenation of literal words evaluates as multiplication. -/
@[simp] theorem y322PositiveWord_append (u v : List (Fin 8)) :
    y322PositiveWord (u ++ v) = y322PositiveWord u * y322PositiveWord v := by
  simp [y322PositiveWord]

/-- Each actual local generator is an involution, directly from its defining square. -/
theorem y322Positive_generator_square (v : Fin 8) :
    (PresentedGroup.of v : Y322Presentation) * PresentedGroup.of v = 1 := by
  have h := y322IndexedRelator_valid (.inl v)
  simpa only [y322IndexedRelator, map_pow, pow_two, map_mul, PresentedGroup.of] using h

/-- Nonadjacent distinct local generators commute by their defining Coxeter relation. -/
theorem y322Positive_generator_commute (u v : Fin 8)
    (ha : ¬ y555Adjacent (y322Vertex u) (y322Vertex v)) :
    (PresentedGroup.of u : Y322Presentation) * PresentedGroup.of v =
      PresentedGroup.of v * PresentedGroup.of u := by
  have hu := y322Positive_generator_square u
  have hv := y322Positive_generator_square v
  have hui : (PresentedGroup.of u : Y322Presentation)⁻¹ = PresentedGroup.of u :=
    inv_eq_of_mul_eq_one_right hu
  have hvi : (PresentedGroup.of v : Y322Presentation)⁻¹ = PresentedGroup.of v :=
    inv_eq_of_mul_eq_one_right hv
  have h := y322IndexedRelator_valid (.inr (.inl (u, v)))
  have h2 : ((PresentedGroup.of u : Y322Presentation) * PresentedGroup.of v) *
      (PresentedGroup.of u * PresentedGroup.of v) = 1 := by
    simpa [y322IndexedRelator, ha, pow_two, PresentedGroup.of] using h
  have hi := eq_inv_of_mul_eq_one_left h2
  simpa only [mul_inv_rev, hui, hvi] using hi

/-- Adjacent local generators obey the literal three-letter braid relation. -/
theorem y322Positive_generator_braid (u v : Fin 8)
    (ha : y555Adjacent (y322Vertex u) (y322Vertex v)) :
    (PresentedGroup.of u : Y322Presentation) * PresentedGroup.of v * PresentedGroup.of u =
      PresentedGroup.of v * PresentedGroup.of u * PresentedGroup.of v := by
  have hu := y322Positive_generator_square u
  have hv := y322Positive_generator_square v
  have hui : (PresentedGroup.of u : Y322Presentation)⁻¹ = PresentedGroup.of u :=
    inv_eq_of_mul_eq_one_right hu
  have hvi : (PresentedGroup.of v : Y322Presentation)⁻¹ = PresentedGroup.of v :=
    inv_eq_of_mul_eq_one_right hv
  have h := y322IndexedRelator_valid (.inr (.inl (u, v)))
  have h3 : (((PresentedGroup.of u : Y322Presentation) * PresentedGroup.of v) *
      (PresentedGroup.of u * PresentedGroup.of v)) *
        (PresentedGroup.of u * PresentedGroup.of v) = 1 := by
    simpa [y322IndexedRelator, ha, pow_succ, pow_two, PresentedGroup.of] using h
  have hi := congrArg (fun x => x * (PresentedGroup.of v : Y322Presentation))
    (eq_inv_of_mul_eq_one_left h3)
  simpa only [mul_inv_rev, hui, hvi, mul_assoc, hv, mul_one] using hi

/-- A checked local Coxeter move at a zero-based word position. -/
inductive Y322CoxeterMove
  | square (position : ℕ)
  | commute (position : ℕ)
  | braid (position : ℕ)
  deriving DecidableEq

/-- Apply one move only when its literal square, commutation, or braid conditions hold. -/
def y322CoxeterStep (move : Y322CoxeterMove) (w : List (Fin 8)) : Option (List (Fin 8)) :=
  match move with
  | .square n => match w.drop n with
    | a :: b :: t => if a = b then some (w.take n ++ t) else none
    | _ => none
  | .commute n => match w.drop n with
    | a :: b :: t =>
      if a ≠ b ∧ ¬ y555Adjacent (y322Vertex a) (y322Vertex b) then
        some (w.take n ++ b :: a :: t) else none
    | _ => none
  | .braid n => match w.drop n with
    | a :: b :: c :: t =>
      if a = c ∧ y555Adjacent (y322Vertex a) (y322Vertex b) then
        some (w.take n ++ b :: a :: b :: t) else none
    | _ => none

/-- Every successful finite move preserves the exact source local group element. -/
theorem y322CoxeterStep_valid (move : Y322CoxeterMove) (w w' : List (Fin 8))
    (h : y322CoxeterStep move w = some w') :
    y322PositiveWord w = y322PositiveWord w' := by
  have he (n : ℕ) : w = w.take n ++ w.drop n := (List.take_append_drop n w).symm
  cases move with
  | square n =>
    simp only [y322CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    subst b
    rw [y322PositiveWord_append, y322PositiveWord_append]
    simp only [y322PositiveWord, List.map_cons, List.prod_cons]
    simp only [← mul_assoc, y322Positive_generator_square, one_mul]
  | commute n =>
    simp only [y322CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    rw [y322PositiveWord_append, y322PositiveWord_append]
    simp only [y322PositiveWord, List.map_cons, List.prod_cons]
    rw [← mul_assoc (PresentedGroup.of a),
      y322Positive_generator_commute a b hab.2, mul_assoc]
  | braid n =>
    simp only [y322CoxeterStep] at h
    split at h <;> try contradiction
    rename_i a b c t hd
    split at h <;> try contradiction
    rename_i hab
    cases h
    conv_lhs => rw [he n, hd]
    have hac := hab.1
    subst c
    rw [y322PositiveWord_append, y322PositiveWord_append]
    simp only [y322PositiveWord, List.map_cons, List.prod_cons]
    simpa only [mul_assoc] using congrArg
      (fun x => (w.take n |>.map fun v => (PresentedGroup.of v : Y322Presentation)).prod *
        (x * (t.map fun v => (PresentedGroup.of v : Y322Presentation)).prod))
      (y322Positive_generator_braid a b hab.2)

/-- Execute a finite sequence of checked local Coxeter moves. -/
def y322CoxeterRun : List Y322CoxeterMove → List (Fin 8) → Option (List (Fin 8))
  | [], w => some w
  | move :: rest, w => (y322CoxeterStep move w).bind (y322CoxeterRun rest)

/-- A successfully replayed finite certificate proves an exact local word equality. -/
theorem y322CoxeterRun_valid (moves : List Y322CoxeterMove) (w w' : List (Fin 8))
    (h : y322CoxeterRun moves w = some w') :
    y322PositiveWord w = y322PositiveWord w' := by
  induction moves generalizing w with
  | nil => cases h; rfl
  | cons move rest ih =>
    simp only [y322CoxeterRun] at h
    cases hs : y322CoxeterStep move w with
    | none => simp only [hs, Option.bind_none] at h; contradiction
    | some v =>
      simp only [hs, Option.bind_some] at h
      exact (y322CoxeterStep_valid move w v hs).trans (ih v h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
