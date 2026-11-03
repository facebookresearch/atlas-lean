/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ParityProduct

open Finset ParityProduct

namespace ParityProductTest

private def rows : Fin 2 → Finset (Fin 2) := fun _ => univ
private def tuples : Finset (Fin 2 → Finset (Fin 2)) :=
  Fintype.piFinset fun j => (rows j).powerset
private def term (S : Fin 2 → Finset (Fin 2)) : ℤ :=
  ∏ j, parityCoeff #(S j)

example : #tuples = 16 := by decide
example : #(tuples.filter fun S => ∑ j, #(S j) ≤ 3) = 15 := by decide
example : (∏ j, evenIndicator #(rows j)) = 1 := by decide
example : (∑ S ∈ tuples, term S) = 1 := by decide
example : (∑ S ∈ tuples.filter (fun S => ∑ j, #(S j) ≤ 3), term S) = -3 := by decide
example : (∑ S ∈ tuples.filter (fun S => ¬ ∑ j, #(S j) ≤ 3), term S) = 4 := by decide

example :
    (∏ j ∈ (univ : Finset (Fin 2)), evenIndicator #(rows j)) *
      ∏ j ∈ (∅ : Finset (Fin 2)), (-1 : ℤ) ^ #(rows j) ≡
    ∑ S ∈ (Fintype.piFinset fun j : Fin 2 =>
      if j ∈ (univ ∪ ∅ : Finset (Fin 2)) then (rows j).powerset else {∅}).filter
      (fun S => ∑ j, #(S j) ≤ 3),
      (∏ j ∈ (univ : Finset (Fin 2)), parityCoeff #(S j)) *
        ∏ j ∈ (∅ : Finset (Fin 2)), (-2 : ℤ) ^ #(S j)
    [ZMOD 2 ^ 2] :=
  prod_evenIndicator_mul_prod_neg_one_pow_modEq (ν := 2) (M := 3)
    (by simp) rows (by decide) (by simp)

-- The audit's mixed coefficient case uses row sizes two and one.
private def mixedRows (j : Fin 2) : Finset (Fin 2) := if j = 0 then univ else {0}
private def mixedTuples : Finset (Fin 2 → Finset (Fin 2)) :=
  Fintype.piFinset fun j => (mixedRows j).powerset
private def mixedTerm (S : Fin 2 → Finset (Fin 2)) : ℤ :=
  parityCoeff #(S 0) * (-2 : ℤ) ^ #(S 1)

example : #mixedTuples = 8 := by decide
example : #(mixedTuples.filter fun S => ∑ j, #(S j) ≤ 2) = 7 := by decide
example : evenIndicator #(mixedRows 0) * (-1 : ℤ) ^ #(mixedRows 1) = -1 := by decide
example : (∑ S ∈ mixedTuples.filter (fun S => ∑ j, #(S j) ≤ 2), mixedTerm S) = 3 := by
  decide
example : (∑ S ∈ mixedTuples.filter (fun S => ¬ ∑ j, #(S j) ≤ 2), mixedTerm S) = -4 := by
  decide

example :
    (∏ j ∈ ({0} : Finset (Fin 2)), evenIndicator #(mixedRows j)) *
      ∏ j ∈ ({1} : Finset (Fin 2)), (-1 : ℤ) ^ #(mixedRows j) ≡
    ∑ S ∈ (Fintype.piFinset fun j : Fin 2 =>
      if j ∈ ({0} ∪ {1} : Finset (Fin 2)) then (mixedRows j).powerset else {∅}).filter
      (fun S => ∑ j, #(S j) ≤ 2),
      (∏ j ∈ ({0} : Finset (Fin 2)), parityCoeff #(S j)) *
        ∏ j ∈ ({1} : Finset (Fin 2)), (-2 : ℤ) ^ #(S j)
    [ZMOD 2 ^ 2] :=
  prod_evenIndicator_mul_prod_neg_one_pow_modEq (ν := 2) (M := 2)
    (by decide) mixedRows (by decide) (by decide)

-- The empty index type still has one tuple of degree zero and weight one.
example : #(Fintype.piFinset fun _ : Fin 0 => (∅ : Finset ℕ).powerset) = 1 := by decide
example : (∑ S ∈ (Fintype.piFinset fun _ : Fin 0 => (∅ : Finset ℕ).powerset).filter
    (fun S => ∑ j, #(S j) ≤ 0), (∏ j, parityCoeff #(S j))) = 1 := by decide

-- The empty index type still has one tuple, whose empty products have weight one.
example :
    (∏ _j ∈ (∅ : Finset (Fin 0)), evenIndicator #((∅ : Finset ℕ))) *
      ∏ _j ∈ (∅ : Finset (Fin 0)), (-1 : ℤ) ^ #((∅ : Finset ℕ)) ≡
    ∑ S ∈ (Fintype.piFinset fun j : Fin 0 =>
      if j ∈ (∅ ∪ ∅ : Finset (Fin 0)) then (∅ : Finset ℕ).powerset else {∅}).filter
      (fun S => ∑ j, #(S j) ≤ 0),
      (∏ j ∈ (∅ : Finset (Fin 0)), parityCoeff #(S j)) *
        ∏ j ∈ (∅ : Finset (Fin 0)), (-2 : ℤ) ^ #(S j)
    [ZMOD 2 ^ 1] :=
  prod_evenIndicator_mul_prod_neg_one_pow_modEq (ν := 1) (M := 0)
    (by simp) (fun _ => ∅) (by decide) (by simp)

-- Lowering the cutoff without its required bound can break the congruence.
private def smallTuples : Finset (Fin 2 → Finset (Fin 1)) :=
  Fintype.piFinset fun _ => (univ : Finset (Fin 1)).powerset

example : #smallTuples = 4 := by decide
example : #(smallTuples.filter fun S => ∑ j, #(S j) ≤ 1) = 3 := by decide
example : (∑ S ∈ smallTuples.filter (fun S => ∑ j, #(S j) ≤ 1),
    ∏ j, parityCoeff #(S j)) = -1 := by decide

example : ¬ (0 : ℤ) ≡
    ∑ S ∈ smallTuples.filter (fun S => ∑ j, #(S j) ≤ 1),
      ∏ j, parityCoeff #(S j) [ZMOD 2 ^ 2] := by
  decide

-- At ν = 1 the source bound is M ≥ 2; decreasing it to 1 also fails.
example : ¬ (0 : ℤ) ≡
    ∑ S ∈ smallTuples.filter (fun S => ∑ j, #(S j) ≤ 1),
      ∏ j, parityCoeff #(S j) [ZMOD 2 ^ 1] := by
  decide

-- Nonempty rows outside both index sets still select only empty subsets.
private def inactiveTuples : Finset (Fin 2 → Finset (Fin 2)) :=
  Fintype.piFinset fun j : Fin 2 =>
    if j ∈ (∅ ∪ ∅ : Finset (Fin 2)) then (rows j).powerset else {∅}

example : #inactiveTuples = 1 := by decide
example : ∀ S ∈ inactiveTuples, ∀ j, S j = ∅ := by decide

example :
    (∏ j ∈ (∅ : Finset (Fin 2)), evenIndicator #(rows j)) *
      ∏ j ∈ (∅ : Finset (Fin 2)), (-1 : ℤ) ^ #(rows j) ≡
    ∑ S ∈ inactiveTuples.filter (fun S => ∑ j, #(S j) ≤ 0),
      (∏ j ∈ (∅ : Finset (Fin 2)), parityCoeff #(S j)) *
        ∏ j ∈ (∅ : Finset (Fin 2)), (-2 : ℤ) ^ #(S j) [ZMOD 2 ^ 1] :=
  prod_evenIndicator_mul_prod_neg_one_pow_modEq (ν := 1) (M := 0)
    (by simp) rows (by decide) (by simp)

example : evenIndicator 0 = 1 := by decide
example : evenIndicator 1 = 0 := by decide
example : parityCoeff 0 = 1 := by decide
example : parityCoeff 1 = -1 := by decide
example : parityCoeff 2 = 2 := by decide
example : parityCoeff 3 = -4 := by decide

#print axioms ParityProduct.evenIndicator
#print axioms ParityProduct.parityCoeff
#print axioms ParityProduct.two_mul_evenIndicator
#print axioms ParityProduct.two_mul_parityCoeff
#print axioms ParityProduct.sum_powerset_parityCoeff
#print axioms ParityProduct.prod_evenIndicator_mul_prod_neg_one_pow_modEq

end ParityProductTest
