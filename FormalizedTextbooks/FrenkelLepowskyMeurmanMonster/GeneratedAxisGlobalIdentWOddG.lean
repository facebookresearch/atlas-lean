/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory: the odd part of the pairing in groups of target terms, without predicted values

The odd part `oddWZ` of the pairing of a triality image `L` with a target `W` (given by a raw
term list, `W.sh = ShortData.ofList T`) is compared with the odd self part of `W` group by group:
if the odd labels of `W` are distinct (r8f's `labDistinct`), the self part is the sum of squares
(`selfOddZ_of_distinct`), and both sides split along any grouping of `T` (r8f's
`oddSumF_append`).  Each group check is a consequence of the identification (coordinatewise
equality of the odd coordinates), so no values have to be predicted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The odd terms of a raw term list. -/
def oddsOf (T : List (ℕ × ℤ)) : List (ℕ × ℤ) := T.filter (fun p => decide (49128 ≤ p.1))

/-- The odd part against a target given by a raw term list. -/
theorem oddWZ_eq_oddSumF (w : ℕ) (fwd : Bool) (X : List SVec) (W : IdentVec) (T : List (ℕ × ℤ))
    (hW : W.sh = ShortData.ofList T) : oddWZ w fwd X W = oddSumF w fwd X T := by
  unfold oddWZ oddSumF
  rw [hW]
  rfl

theorem oddSumF_flatten (w : ℕ) (fwd : Bool) (X : List SVec) :
    ∀ Ts : List (List (ℕ × ℤ)), oddSumF w fwd X Ts.flatten = (Ts.map (oddSumF w fwd X)).sum
  | [] => by simp [oddSumF]
  | t :: Ts => by
    rw [List.flatten_cons, oddSumF_append, oddSumF_flatten w fwd X Ts, List.map_cons, List.sum_cons]

theorem sqSumZ_append (A B : List (ℕ × ℤ)) : sqSumZ (A ++ B) = sqSumZ A + sqSumZ B := by
  simp [sqSumZ]

theorem oddsOf_flatten_sq :
    ∀ Ts : List (List (ℕ × ℤ)),
      sqSumZ (oddsOf Ts.flatten) = (Ts.map (fun t => sqSumZ (oddsOf t))).sum
  | [] => by simp [oddsOf, sqSumZ]
  | t :: Ts => by
    rw [List.flatten_cons, List.map_cons, List.sum_cons, ← oddsOf_flatten_sq Ts, ← sqSumZ_append]
    simp only [oddsOf, List.filter_append]

theorem sum_div_eq_of_forall {α : Type} (Ts : List α) (a b : α → ℚ) (c s : ℚ)
    (h : ∀ t ∈ Ts, a t / c = s * b t) : (Ts.map a).sum / c = s * (Ts.map b).sum := by
  induction Ts with
  | nil => simp
  | cons t Ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [add_div, mul_add, h t (by simp), ih (fun u hu => h u (by simp [hu]))]

/-- The odd part of the pairing from group checks against the odd self part of the target. -/
theorem oddPart_of_groups (w : ℕ) (fwd : Bool) (X : List SVec) (W : IdentVec)
    (Ts : List (List (ℕ × ℤ))) (hW : W.sh = ShortData.ofList Ts.flatten)
    (hd : labDistinct W.sh.odd 0 = true) (D : ℚ)
    (hg : ∀ t ∈ Ts, (oddSumF w fwd X t : ℚ) / (2 * D) = W.sden * (sqSumZ (oddsOf t) : ℚ)) :
    (oddWZ w fwd X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ) := by
  rw [oddWZ_eq_oddSumF w fwd X W _ hW, selfOddP_eq, selfOddZ_of_distinct W hd]
  have hodd : W.sh.odd = oddsOf Ts.flatten := by rw [hW]; rfl
  rw [hodd, oddSumF_flatten, oddsOf_flatten_sq]
  push_cast
  rw [List.map_map, List.map_map]
  exact sum_div_eq_of_forall Ts _ _ _ _ hg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
