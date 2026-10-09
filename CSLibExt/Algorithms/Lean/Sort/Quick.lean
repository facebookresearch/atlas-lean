/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Partition
import Mathlib.Data.Nat.Choose.Basic

/-!
# Deterministic list quicksort

This module adapts quicksort from Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, 4th ed., Section 7.1, to immutable lists. The first element
is the deterministic pivot, and `partition3` groups duplicate pivots in one recursive step.

Each element comparison costs one tick; dispatch, list construction, and recursion are free.
The proved bound is worst-case; there is no randomized or expected-time claim.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [LinearOrder α]

/-- Deterministic head-pivot quicksort with a stable three-way partition. -/
def quickSort (xs : List α) : TimeM Nat (List α) :=
  let rec loop : Nat → List α → TimeM Nat (List α)
    | 0, _ => pure []
    | _ + 1, [] => pure []
    | fuel + 1, pivot :: tail => do
        let parts ← partition3 pivot tail
        let below ← loop fuel parts.below
        let above ← loop fuel parts.above
        return below ++ (pivot :: (parts.equal ++ above))
  loop xs.length xs

private theorem pairwise_partition_append (pivot : α)
    {below equal above : List α}
    (hbelowSorted : List.Pairwise (fun x y => x ≤ y) below)
    (haboveSorted : List.Pairwise (fun x y => x ≤ y) above)
    (hbelow : ∀ x ∈ below, x < pivot)
    (hequal : ∀ x ∈ equal, x = pivot)
    (habove : ∀ x ∈ above, pivot < x) :
    List.Pairwise (fun x y => x ≤ y) (below ++ (pivot :: (equal ++ above))) := by
  have hequalSorted : List.Pairwise (fun x y : α => x ≤ y) equal :=
    List.pairwise_of_forall_mem_list fun x hx y hy => by
      rw [hequal x hx, hequal y hy]
  have hequalAbove : List.Pairwise (fun x y : α => x ≤ y) (equal ++ above) :=
    List.pairwise_append.2 ⟨hequalSorted, haboveSorted, fun x hx y hy => by
      rw [hequal x hx]
      exact (habove y hy).le⟩
  have hpivotRest : ∀ x ∈ equal ++ above, pivot ≤ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hequal x hx).ge
    · exact (habove x hx).le
  have hrest : List.Pairwise (fun x y : α => x ≤ y) (pivot :: (equal ++ above)) :=
    List.pairwise_cons.2 ⟨hpivotRest, hequalAbove⟩
  refine List.pairwise_append.2 ⟨hbelowSorted, hrest, ?_⟩
  intro x hx y hy
  have hpivotLe : pivot ≤ y := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_rfl
    · exact hpivotRest y hy
  exact (hbelow x hx).le.trans hpivotLe

/-- Quicksort returns a nondecreasing permutation, preserving duplicate occurrences. -/
theorem quickSort_correct (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (quickSort xs).ret ∧
      List.Perm (quickSort xs).ret xs := by
  unfold quickSort
  have loop_correct : ∀ (fuel : Nat) (ys : List α), ys.length ≤ fuel →
      List.Pairwise (fun x y => x ≤ y) (quickSort.loop fuel ys).ret ∧
        List.Perm (quickSort.loop fuel ys).ret ys := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys hlen
        cases ys with
        | nil => simp [quickSort.loop]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys hlen
        cases ys with
        | nil => simp [quickSort.loop]
        | cons pivot tail =>
            have htail : tail.length ≤ fuel := by
              simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
            generalize hparts : (partition3 pivot tail).ret = parts
            have hpartsCorrect := partition3_correct pivot tail
            rw [hparts] at hpartsCorrect
            obtain ⟨hpartsPerm, hbelow, hequal, habove⟩ := hpartsCorrect
            have hpartsLength := partition3_length pivot tail
            rw [hparts] at hpartsLength
            have hbelowFuel : parts.below.length ≤ fuel := by omega
            have haboveFuel : parts.above.length ≤ fuel := by omega
            obtain ⟨hbelowSorted, hbelowPerm⟩ := ih parts.below hbelowFuel
            obtain ⟨haboveSorted, habovePerm⟩ := ih parts.above haboveFuel
            have hbelowOutput :
                ∀ x ∈ (quickSort.loop fuel parts.below).ret, x < pivot := by
              intro x hx
              exact hbelow x (hbelowPerm.mem_iff.mp hx)
            have haboveOutput :
                ∀ x ∈ (quickSort.loop fuel parts.above).ret, pivot < x := by
              intro x hx
              exact habove x (habovePerm.mem_iff.mp hx)
            have hsorted := pairwise_partition_append pivot hbelowSorted haboveSorted
              hbelowOutput hequal haboveOutput
            have hrecursivePerm :
                List.Perm
                  ((quickSort.loop fuel parts.below).ret ++
                    (pivot :: (parts.equal ++ (quickSort.loop fuel parts.above).ret)))
                  (parts.below ++ (pivot :: (parts.equal ++ parts.above))) :=
              hbelowPerm.append ((habovePerm.append_left parts.equal).cons pivot)
            have hpartsPerm' :
                (parts.below ++ (parts.equal ++ parts.above)).Perm tail := by
              simpa only [List.append_assoc] using hpartsPerm
            have hresultPerm :
                List.Perm
                  ((quickSort.loop fuel parts.below).ret ++
                    (pivot :: (parts.equal ++ (quickSort.loop fuel parts.above).ret)))
                  (pivot :: tail) :=
              hrecursivePerm.trans (List.perm_middle.trans (hpartsPerm'.cons pivot))
            simpa [quickSort.loop, hparts] using And.intro hsorted hresultPerm
  exact loop_correct xs.length xs (Nat.le_refl _)

private theorem choose_two_add_le (a b : Nat) :
    a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        a.succ.choose 2 + b.choose 2 =
            (a + a.choose 2) + b.choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
        _ ≤ a + (a + b).choose 2 := by omega
        _ ≤ a + b + (a + b).choose 2 := by omega
        _ = (a + b).succ.choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
        _ = (a.succ + b).choose 2 := by
          rw [show a.succ + b = (a + b).succ by omega]

private theorem choose_two_add_self (n : Nat) :
    n.choose 2 + n = (n + 1).choose 2 := by
  simpa [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using
    (Nat.choose_succ_succ n 1).symm

private theorem recursive_cost_le_choose (a b n : Nat) (h : a + b ≤ n) :
    a.choose 2 + b.choose 2 + n ≤ (n + 1).choose 2 := by
  have hadd := choose_two_add_le a b
  have hmono : (a + b).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 h
  have hsum := choose_two_add_self n
  omega

/-- Quicksort uses at most `n * (n - 1) / 2` comparisons on a list of length `n`. -/
theorem quickSort_time (xs : List α) :
    (quickSort xs).time ≤ xs.length * (xs.length - 1) / 2 := by
  unfold quickSort
  have loop_time : ∀ (fuel : Nat) (ys : List α), ys.length ≤ fuel →
      (quickSort.loop fuel ys).time ≤ ys.length.choose 2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys hlen
        cases ys with
        | nil => simp [quickSort.loop]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys hlen
        cases ys with
        | nil => simp [quickSort.loop]
        | cons pivot tail =>
            have htail : tail.length ≤ fuel := by
              simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
            generalize hparts : (partition3 pivot tail).ret = parts
            have hpartsLength := partition3_length pivot tail
            rw [hparts] at hpartsLength
            have hbelowFuel : parts.below.length ≤ fuel := by omega
            have haboveFuel : parts.above.length ≤ fuel := by omega
            have hbelowTime := ih parts.below hbelowFuel
            have haboveTime := ih parts.above haboveFuel
            have hrecursive := recursive_cost_le_choose parts.below.length
              parts.above.length tail.length (by omega)
            simp only [quickSort.loop, time_bind, time_pure, hparts,
              partition3_time, List.length_cons]
            omega
  rw [← Nat.choose_two_right]
  exact loop_time xs.length xs (Nat.le_refl _)

end Cslib.Algorithms.Lean.TimeM
