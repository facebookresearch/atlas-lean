/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Elementary equations from the exact nine-generator C431 Coxeter source relators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original C431 generator squares to one by its defining source relation. -/
theorem y431_generator_square (i : Fin 9) :
    (PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of i = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y431Relations)
    (show FreeGroup.of i ^ 2 ∈ y431Relations from Or.inl ⟨i, rfl⟩)
  simpa only [map_pow, PresentedGroup.of, pow_two, map_mul] using h

/-- Every distinct original C431 generator pair satisfies its exact source Coxeter power. -/
theorem y431_generator_pair (i j : Fin 9) (hij : i ≠ j) :
    ((PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of j) ^
      (if y555Adjacent (y431Vertex i) (y431Vertex j) then 3 else 2 : ℕ) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y431Relations)
    (show (FreeGroup.of i * FreeGroup.of j) ^
        (if y555Adjacent (y431Vertex i) (y431Vertex j) then 3 else 2 : ℕ) ∈ y431Relations
      from Or.inr (Or.inl ⟨i, j, hij, rfl⟩))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

/-- Original nonadjacent C431 generators commute by the actual source pair relation. -/
theorem y431_generator_commute (i j : Fin 9)
    (ha : ¬ y555Adjacent (y431Vertex i) (y431Vertex j)) :
    (PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of j =
      PresentedGroup.of j * PresentedGroup.of i := by
  by_cases hij : i = j
  · subst j
    rfl
  have hi : (PresentedGroup.of i : Y431RPresentation)⁻¹ = PresentedGroup.of i :=
    inv_eq_of_mul_eq_one_right (y431_generator_square i)
  have hj : (PresentedGroup.of j : Y431RPresentation)⁻¹ = PresentedGroup.of j :=
    inv_eq_of_mul_eq_one_right (y431_generator_square j)
  have hp : ((PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of j) *
      (PresentedGroup.of i * PresentedGroup.of j) = 1 := by
    simpa only [ite_eq_right ha, pow_two] using y431_generator_pair i j hij
  simpa only [mul_inv_rev, hi, hj] using eq_inv_of_mul_eq_one_left hp

/-- Original adjacent C431 generators satisfy the actual three-letter Coxeter braid equation. -/
theorem y431_generator_braid (i j : Fin 9)
    (ha : y555Adjacent (y431Vertex i) (y431Vertex j)) :
    (PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of j * PresentedGroup.of i =
      PresentedGroup.of j * PresentedGroup.of i * PresentedGroup.of j := by
  have hij : i ≠ j := by
    intro heq
    subst j
    exact y555Adjacent_irrefl (y431Vertex i) ha
  have hi : (PresentedGroup.of i : Y431RPresentation)⁻¹ = PresentedGroup.of i :=
    inv_eq_of_mul_eq_one_right (y431_generator_square i)
  have hj : (PresentedGroup.of j : Y431RPresentation)⁻¹ = PresentedGroup.of j :=
    inv_eq_of_mul_eq_one_right (y431_generator_square j)
  have hp : (((PresentedGroup.of i : Y431RPresentation) * PresentedGroup.of j) *
      (PresentedGroup.of i * PresentedGroup.of j)) *
        (PresentedGroup.of i * PresentedGroup.of j) = 1 := by
    simpa only [ite_eq_left ha, pow_succ, pow_two, pow_one, pow_zero, one_mul] using
      y431_generator_pair i j hij
  have h := congrArg (fun x => x * (PresentedGroup.of j : Y431RPresentation))
    (eq_inv_of_mul_eq_one_left hp)
  simpa only [mul_inv_rev, hi, hj, mul_assoc, y431_generator_square, mul_one] using h

/-- Numbered source equations: nine squares, eighty-one commutations and eighty-one braids. -/
def y431CoxeterEquation (s : Fin 171) : Y322WordEquation (Fin 9) :=
  if h : s.val < 9 then ⟨[(⟨s.val, h⟩, true), (⟨s.val, h⟩, true)], []⟩
  else if h : s.val < 90 then
    let i : Fin 9 := ⟨(s.val - 9) / 9, by omega⟩
    let j : Fin 9 := ⟨(s.val - 9) % 9, Nat.mod_lt _ (by decide)⟩
    if ¬ y555Adjacent (y431Vertex i) (y431Vertex j) then
      ⟨[(i, true), (j, true)], [(j, true), (i, true)]⟩ else ⟨[], []⟩
  else
    let i : Fin 9 := ⟨(s.val - 90) / 9, by omega⟩
    let j : Fin 9 := ⟨(s.val - 90) % 9, Nat.mod_lt _ (by decide)⟩
    if y555Adjacent (y431Vertex i) (y431Vertex j) then
      ⟨[(i, true), (j, true), (i, true)], [(j, true), (i, true), (j, true)]⟩ else ⟨[], []⟩

/-- Every numbered equation is proved from the literal original C431 defining relations. -/
theorem y431CoxeterEquation_valid (s : Fin 171) :
    (y431CoxeterEquation s).Valid (fun i => (PresentedGroup.of i : Y431RPresentation)) := by
  unfold y431CoxeterEquation
  split
  · simpa [Y322WordEquation.Valid, y322EquationWordValue, FreeGroup.lift_mk, mul_assoc] using
      y431_generator_square ⟨s.val, ‹s.val < 9›⟩
  · split
    · dsimp only
      split
      · simpa [Y322WordEquation.Valid, y322EquationWordValue, FreeGroup.lift_mk, mul_assoc] using
          y431_generator_commute _ _ ‹_›
      · rfl
    · dsimp only
      split
      · simpa [Y322WordEquation.Valid, y322EquationWordValue, FreeGroup.lift_mk, mul_assoc] using
          y431_generator_braid _ _ ‹_›
      · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
