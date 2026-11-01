/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedParity
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Ring.List

/-! The complete selected scalar phase is its original ordered quadratic polynomial. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Selecting a characteristic-two factor is exactly multiplication by its coefficient. -/
theorem generatedSixth_xi_select_mul (x y : ZMod 2) :
    (if x = 0 then 0 else y) = x * y := by
  fin_cases x <;> simp

/-- The original ordered finite coordinate list has exactly its displayed twenty-four entries. -/
theorem generatedSixth_xi_coordinate_list : List.finRange 24 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] := by
  decide +kernel

/-- The ordered quadratic list keeps precisely the original central and pair contributions. -/
def generatedSixthXiQuadraticList (c : Fin 24 → ZMod 2)
    (p : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2) :
    List (Fin 24) → ZMod 2
  | [] => 0
  | i :: l => generatedSixthXiQuadraticList c p v l + v i * c i +
      v i * (l.map (fun j => v j * p i j)).sum

/-- Multiplication by the literal binary coordinate removes only the selection notation. -/
theorem generatedSixth_xi_selected_quadratic_list (c : Fin 24 → ZMod 2)
    (p : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2)
    (l : List (Fin 24)) :
    generatedSixthQSelectedPhase c p v l = generatedSixthXiQuadraticList c p v l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [generatedSixthQSelectedPhase, generatedSixthXiQuadraticList, ih,
      generatedSixth_xi_select_mul]
    ring

/-- An ordered list sums exactly its linear terms and strictly later cocycle pairs. -/
theorem generatedSixth_xi_quadratic_list_sum (c : Fin 24 → ZMod 2)
    (p : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2)
    (l : List (Fin 24)) (hl : l.Pairwise (· < ·)) :
    generatedSixthXiQuadraticList c p v l =
      (l.map (fun i => v i * c i)).sum +
      (l.map (fun i => (l.map (fun j => if i < j then v i * v j * p i j else 0)).sum)).sum := by
  induction l with
  | nil => simp [generatedSixthXiQuadraticList]
  | cons a l ih =>
    rcases List.pairwise_cons.mp hl with ⟨ha, hl⟩
    have hh : (l.map (fun j => if a < j then v a * v j * p a j else 0)).sum =
        v a * (l.map (fun j => v j * p a j)).sum := by
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      simp only [ha j hj, ite_true]
      ring
    have ht : (l.map (fun i => ((a :: l).map
          (fun j => if i < j then v i * v j * p i j else 0)).sum)).sum =
        (l.map (fun i => (l.map
          (fun j => if i < j then v i * v j * p i j else 0)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      simp only [List.map_cons, List.sum_cons,
        ite_eq_right (not_lt_of_gt (ha i hi)), zero_add]
    simp only [List.map_cons, List.sum_cons] at ht
    simp only [generatedSixthXiQuadraticList, List.map_cons, List.sum_cons,
      lt_self_iff_false, ite_false, zero_add, hh, ih hl]
    rw [ht]
    ring

/-- The complete original selected phase retains every linear bit and ordered cocycle pair. -/
theorem generatedSixth_xi_selected_quadratic (c : Fin 24 → ZMod 2)
    (p : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2) :
    generatedSixthQSelectedPhase c p v (List.finRange 24) =
      (∑ i : Fin 24, v i * c i) +
      ∑ i : Fin 24, ∑ j : Fin 24, if i < j then v i * v j * p i j else 0 := by
  rw [generatedSixth_xi_selected_quadratic_list]
  have h := generatedSixth_xi_quadratic_list_sum c p v (List.finRange 24)
    (List.sortedLT_finRange 24).pairwise
  simpa only [← List.ofFn_eq_map, List.sum_ofFn] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
