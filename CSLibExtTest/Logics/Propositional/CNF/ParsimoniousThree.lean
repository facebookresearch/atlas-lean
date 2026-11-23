/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Logics.Propositional.CNF.ParsimoniousThree
public import CSLibExt.Computability.Complexity.Karp.ThreeSatCorrect

/-! # Tests for the parsimonious reduction to clauses of width three -/

@[expose] public section

namespace Cslib.Logic.PL.CNF

private def fourPositive : CNF :=
  [[(0, true), (1, true), (2, true), (3, true)]]

private def fourPositiveReduced : CNF :=
  [[(4, false), (0, true), (1, true)],
    [(4, true), (0, false)],
    [(4, true), (1, false)],
    [(4, true), (2, true), (3, true)]]

#eval fourPositive.to3Parsimonious 4
#eval (fourPositive.to3Parsimonious 4).modelCount
#eval fourPositive.numFreshParsimonious3

example : fourPositive.numFreshParsimonious3 = 1 := by decide

example : fourPositive.to3Parsimonious 4 = fourPositiveReduced := by decide

example : (fourPositive.to3Parsimonious 4).length = 4 := by decide

example : ∀ clause ∈ fourPositive.to3Parsimonious 4, clause.length ≤ 3 := by decide

example : (fourPositive.to3Parsimonious 4).Nodup := by decide

example : fourPositive.modelCount = 15 := by decide

example : (fourPositive.to3Parsimonious 4).modelCount = 15 := by decide

example : (fourPositive.to3Parsimonious 0).modelCount = 11 := by decide

example : (fourPositive.to3Parsimonious 0).modelCount ≠ fourPositive.modelCount := by decide

example :
    ¬ ((fourPositive.to3Parsimonious 4).Satisfies (fun _ => true) ∧
      (fourPositive.to3Parsimonious 4).Satisfies (fun x => x != 4)) := by
  rw [show fourPositive.to3Parsimonious 4 = fourPositiveReduced by decide]
  simp [fourPositiveReduced, CNF.Satisfies, CNFClause.Satisfies,
    CNFLiteral.Satisfies]

example :
    to3Parsimonious [[(0, true), (0, true), (1, true), (2, true)]] 3 =
      [[(3, false), (0, true), (0, true)],
        [(3, true), (0, false)],
        [(3, true), (1, true), (2, true)]] := by decide

example :
    modelCount (to3Parsimonious [[(0, true), (0, true), (1, true), (2, true)]] 3) =
      7 := by decide

example : numFreshParsimonious3 [] = 0 := by decide

example : to3Parsimonious [] 7 = [] := by decide

example : modelCount [] = 1 := by decide

example : modelCount [[]] = 0 := by decide

example : to3Parsimonious [[(9, false), (2, true), (9, false)]] 20 =
    [[(9, false), (2, true), (9, false)]] := by decide

example : to3Parsimonious [[(0, true)], [(0, true)]] 5 = [[(0, true)]] := by decide

example :
    numFreshParsimonious3 [[(0, true), (1, false), (2, true), (3, false), (4, true)]] =
      2 := by decide

example :
    to3Parsimonious [[(0, true), (1, false), (2, true), (3, false), (4, true)]] 8 =
        [[(8, false), (0, true), (1, false)],
          [(8, true), (0, false)],
          [(8, true), (1, true)],
          [(9, false), (8, true), (2, true)],
          [(9, true), (8, false)],
          [(9, true), (2, false)],
          [(9, true), (3, false), (4, true)]] := by decide

example (assignment : Nat → Bool)
    (h : fourPositive.Satisfies assignment) :
    ∃! extension : Nat → Bool,
      (fourPositive.to3Parsimonious 4).Satisfies extension ∧
        ∀ x, x < 4 ∨ 4 + fourPositive.numFreshParsimonious3 ≤ x →
          extension x = assignment x :=
  existsUnique_satisfies_to3Parsimonious (by simp [fourPositive]) h

example : (fourPositive.to3Parsimonious 4).modelCount = fourPositive.modelCount :=
  modelCount_to3Parsimonious fourPositive 4 (by simp [fourPositive])

private def oldTo3Extension (freshValue : Bool) (x : Nat) : Bool :=
  if x = 3 then freshValue else decide (x = 0 ∨ x = 2)

example :
    Cslib.Complexity.Karp.to3 ([[(0, true), (1, true)]] : CNF) =
      [[(0, true), (3, true)], [(3, false), (2, true)]] := by decide

example : modelCount ([[(0, true), (1, true)]] : CNF) = 3 := by decide

example :
    (Cslib.Complexity.Karp.to3 ([[(0, true), (1, true)]] : CNF)).modelCount = 4 := by
  decide

example :
    (Cslib.Complexity.Karp.to3 ([[(0, true), (1, true)]] : CNF)).Satisfies
      (oldTo3Extension false) := by
  change CNF.Satisfies (oldTo3Extension false)
    [[(0, true), (3, true)], [(3, false), (2, true)]]
  intro clause hclause
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl
  · exact ⟨(0, true), by simp, by simp [oldTo3Extension]⟩
  · exact ⟨(3, false), by simp, by simp [oldTo3Extension]⟩

example :
    (Cslib.Complexity.Karp.to3 ([[(0, true), (1, true)]] : CNF)).Satisfies
      (oldTo3Extension true) := by
  change CNF.Satisfies (oldTo3Extension true)
    [[(0, true), (3, true)], [(3, false), (2, true)]]
  intro clause hclause
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl
  · exact ⟨(3, true), by simp, by simp [oldTo3Extension]⟩
  · exact ⟨(2, true), by simp, by simp [oldTo3Extension]⟩

example : oldTo3Extension false 3 ≠ oldTo3Extension true 3 := by decide

end Cslib.Logic.PL.CNF
