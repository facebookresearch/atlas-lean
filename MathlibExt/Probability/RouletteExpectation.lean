/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathLaw
public import MathlibExt.Probability.RouletteScore
import Mathlib.Tactic

@[expose] public section

namespace RussianRoulette

/-- Accumulated score of a completed path: emission at each visited state,
weighted by the accumulated likelihood ratio `T / Q` along the traversed
edges, summed over all visits including the final stopped state. Zero on
the empty list. -/
noncomputable def pathScore {S : Type*} (T Q : S → S → ℝ) (E : S → ℝ) :
    List S → ℝ
  | [] => 0
  | [x] => E x
  | x :: y :: t => E x + (T x y / Q x y) * pathScore T Q E (y :: t)

/-- The score is dominated by the score of the absolute emission when the
target and sampling kernels are nonnegative. -/
theorem abs_pathScore_le {S : Type*} (T Q : S → S → ℝ)
    (hT : ∀ a b : S, 0 ≤ T a b) (hQ : ∀ a b : S, 0 ≤ Q a b) (E : S → ℝ)
    (l : List S) :
    |pathScore T Q E l| ≤ pathScore T Q (fun a => |E a|) l := by
  induction l with
  | nil => simp [pathScore]
  | cons x t ih =>
      cases t with
      | nil => simp [pathScore]
      | cons y t =>
          simp only [pathScore]
          have hw : 0 ≤ T x y / Q x y := div_nonneg (hT x y) (hQ x y)
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hw]
          exact add_le_add_right (mul_le_mul_of_nonneg_left ih hw) _

/-- The absolute-emission score is nonnegative under nonnegative kernels. -/
theorem pathScore_abs_nonneg {S : Type*} (T Q : S → S → ℝ)
    (hT : ∀ a b : S, 0 ≤ T a b) (hQ : ∀ a b : S, 0 ≤ Q a b) (E : S → ℝ)
    (l : List S) :
    0 ≤ pathScore T Q (fun a => |E a|) l := by
  induction l with
  | nil => simp [pathScore]
  | cons x t ih =>
      cases t with
      | nil => simp [pathScore]
      | cons y t =>
          simp only [pathScore]
          exact add_nonneg (abs_nonneg _)
            (mul_nonneg (div_nonneg (hT x y) (hQ x y)) ih)

/-- The weight of a length-one prefix is one. -/
private theorem ratioWeight_prefix_one {S : Type*} (T Q : S → S → ℝ)
    {m : ℕ} (y : Fin (m + 1) → S) :
    ratioWeight T Q
        (fun j : Fin ((0 : Fin (m + 1)).val + 1) =>
          y ⟨j.val, Nat.lt_of_lt_of_le j.2
            (Nat.succ_le_of_lt (0 : Fin (m + 1)).2)⟩) = 1 := by
  unfold ratioWeight
  exact Fin.prod_univ_zero _

/-- A successor prefix weight splits off the first edge. -/
private theorem ratioWeight_prefix_succ {S : Type*} (T Q : S → S → ℝ)
    {m : ℕ} (y : Fin (m + 1 + 1) → S) (k : Fin (m + 1)) :
    ratioWeight T Q
        (fun j : Fin ((k.succ).val + 1) =>
          y ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.succ.2)⟩)
      = (T (y 0) (y (Fin.succ 0)) / Q (y 0) (y (Fin.succ 0)))
        * ratioWeight T Q
          (fun j : Fin (k.val + 1) =>
            (fun i : Fin (m + 1) => y i.succ)
              ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.2)⟩) := by
  unfold ratioWeight
  simp only [Fin.val_succ]
  rw [Fin.prod_univ_succ]
  congr 1

/-- The score of a fixed-length path, expanded as the sum over visits of
prefix likelihood ratios times emissions. -/
theorem pathScore_ofFn {S : Type*} (T Q : S → S → ℝ) (E : S → ℝ) {n : ℕ}
    (x : Fin (n + 1) → S) :
    pathScore T Q E (List.ofFn x)
      = ∑ k : Fin (n + 1),
          ratioWeight T Q
              (fun j : Fin (k.val + 1) =>
                x ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.2)⟩)
            * E (x k) := by
  have key : ∀ (m : ℕ) (y : Fin (m + 1) → S),
      pathScore T Q E (List.ofFn y)
        = ∑ k : Fin (m + 1),
            ratioWeight T Q
                (fun j : Fin (k.val + 1) =>
                  y ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.2)⟩)
              * E (y k) := by
    intro m
    induction m with
    | zero =>
        intro y
        have hofn : List.ofFn y = [y 0] := by
          rw [List.ofFn_succ, List.ofFn_zero]
        rw [hofn]
        simp only [pathScore]
        rw [Fin.sum_univ_one, ratioWeight_prefix_one T Q y, one_mul]
    | succ m ih =>
        intro y
        rw [Fin.sum_univ_succ]
        have hcons : List.ofFn y
            = y 0 :: List.ofFn (fun k : Fin (m + 1) => y k.succ) :=
          List.ofFn_succ
        have htail : List.ofFn (fun k : Fin (m + 1) => y k.succ)
            = y (Fin.succ 0) :: List.ofFn (fun k : Fin m => y k.succ.succ) :=
          List.ofFn_succ
        rw [hcons, htail]
        simp only [pathScore]
        have hfold : (y (Fin.succ 0)
            :: List.ofFn (fun k : Fin m => y k.succ.succ))
            = List.ofFn (fun k : Fin (m + 1) => y k.succ) :=
          (List.ofFn_succ (f := fun k : Fin (m + 1) => y k.succ)).symm
        rw [hfold, ih]
        rw [ratioWeight_prefix_one T Q y, one_mul, Finset.mul_sum]
        have hterm : ∀ k : Fin (m + 1),
            (T (y 0) (y (Fin.succ 0)) / Q (y 0) (y (Fin.succ 0)))
              * (ratioWeight T Q
                (fun j : Fin (k.val + 1) =>
                  (fun i : Fin (m + 1) => y i.succ)
                    ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.2)⟩)
                * E (y k.succ))
            = ratioWeight T Q
                (fun j : Fin ((k.succ).val + 1) =>
                  y ⟨j.val, Nat.lt_of_lt_of_le j.2
                    (Nat.succ_le_of_lt k.succ.2)⟩)
                * E (y k.succ) := by
          intro k
          have hW := ratioWeight_prefix_succ T Q y k
          rw [hW]
          ring
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact hterm k
  exact key n x

end RussianRoulette

end
public section
