/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Compare

/-!
# Stable three-way list partition

This module adapts the partition step from Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, 4th ed., Section 7.1, to immutable lists. It uses a stable
three-way partition and makes no in-place-memory claim.

Each input occurrence incurs one tick for one call to `cmp`; pattern matching, list
construction, and recursion are free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [LinearOrder α]

/-- **Three-way partition record.** A three-way partition over a type $\alpha$ consists of three
lists over $\alpha$, called below, equal and above. They are meant to hold the elements strictly
below, equal to, and strictly above a pivot; the record itself imposes no condition on them. -/
@[ext]
structure ThreeWayPartition (α : Type u) where
  /-- Elements strictly below the pivot. -/
  below : List α
  /-- Elements equal to the pivot. -/
  equal : List α
  /-- Elements strictly above the pivot. -/
  above : List α
deriving DecidableEq

/-- **Stable three-way partition.** Let $p$ be an element of a linearly ordered type $\alpha$. The
three-way partition of a list over $\alpha$ around $p$, together with the time it is charged, is
defined by recursion on the list. The empty list gives three empty lists at no cost. For a list
with head $x$ and tail $xs$, one unit of time is charged for comparing $x$ with $p$, the tail $xs$
is partitioned, and $x$ is put at the front of its below list if $x < p$, of its equal list if
$x = p$, and of its above list if $p < x$. -/
def partition3 (pivot : α) : List α → TimeM Nat (ThreeWayPartition α)
  | [] => pure { below := [], equal := [], above := [] }
  | x :: xs => do
      ✓
      let parts ← partition3 pivot xs
      match cmp x pivot with
      | .lt => return { parts with below := x :: parts.below }
      | .eq => return { parts with equal := x :: parts.equal }
      | .gt => return { parts with above := x :: parts.above }

/-- **Cost of the stable three-way partition.** For every element $p$ of a linearly ordered type
$\alpha$ and every list $xs$ over $\alpha$, the time charged by the stable three-way partition of
$xs$ around $p$ equals the length of $xs$: one unit for each comparison, one comparison per
element. -/
@[simp]
theorem partition3_time (pivot : α) (xs : List α) :
    (partition3 pivot xs).time = xs.length := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
      cases hcmp : cmp x pivot <;> simp [partition3, hcmp, ih, Nat.add_comm]

/-- **Correctness of the stable three-way partition.** Let $p$ be an element of a linearly ordered
type $\alpha$, let $xs$ be a list over $\alpha$, and let $B$, $E$ and $A$ be the below, equal and
above lists of the stable three-way partition of $xs$ around $p$. Then the concatenation $B$, $E$,
$A$ is a permutation of $xs$, every element $x$ of $B$ satisfies $x < p$, every element of $E$
equals $p$, and every element $x$ of $A$ satisfies $p < x$. -/
theorem partition3_correct (pivot : α) (xs : List α) :
    List.Perm
        ((partition3 pivot xs).ret.below ++
          (partition3 pivot xs).ret.equal ++
          (partition3 pivot xs).ret.above)
        xs ∧
      (∀ x ∈ (partition3 pivot xs).ret.below, x < pivot) ∧
      (∀ x ∈ (partition3 pivot xs).ret.equal, x = pivot) ∧
      ∀ x ∈ (partition3 pivot xs).ret.above, pivot < x := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
      obtain ⟨hperm, hbelow, hequal, habove⟩ := ih
      cases hcmp : cmp x pivot with
      | lt =>
          simp only [partition3, ret_bind, ret_pure, hcmp]
          have hx : x < pivot := (cmp_eq_lt_iff x pivot).mp hcmp
          refine ⟨hperm.cons x, ?_, hequal, habove⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact hbelow y hy
      | eq =>
          simp only [partition3, ret_bind, ret_pure, hcmp]
          have hx : x = pivot := (cmp_eq_eq_iff x pivot).mp hcmp
          refine ⟨?_, hbelow, ?_, habove⟩
          · have hperm' :
                List.Perm
                  ((partition3 pivot xs).ret.below ++
                    ((partition3 pivot xs).ret.equal ++
                      (partition3 pivot xs).ret.above)) xs := by
                simpa only [List.append_assoc] using hperm
            simpa only [List.cons_append, List.append_assoc] using
              (List.perm_middle (a := x) (l₁ := (partition3 pivot xs).ret.below)
                (l₂ := (partition3 pivot xs).ret.equal ++
                  (partition3 pivot xs).ret.above)).trans (hperm'.cons x)
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact hequal y hy
      | gt =>
          simp only [partition3, ret_bind, ret_pure, hcmp]
          have hx : pivot < x := (cmp_eq_gt_iff x pivot).mp hcmp
          refine ⟨?_, hbelow, hequal, ?_⟩
          · simpa only [List.append_assoc] using
              List.perm_middle.trans (hperm.cons x)
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact habove y hy

private theorem partition3_eq_filters (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.below = xs.filter (fun x => x < pivot) ∧
    (partition3 pivot xs).ret.equal = xs.filter (fun x => x = pivot) ∧
    (partition3 pivot xs).ret.above = xs.filter (fun x => pivot < x) := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
      rcases ih with ⟨ihBelow, ihEqual, ihAbove⟩
      cases hcmp : cmp x pivot with
      | lt =>
          have hlt : x < pivot := (cmp_eq_lt_iff x pivot).mp hcmp
          have hne : x ≠ pivot := ne_of_lt hlt
          have hnabove : ¬pivot < x := not_lt_of_ge hlt.le
          simp [partition3, hcmp, ihBelow, ihEqual, ihAbove, hlt, hne, hnabove]
      | eq =>
          have heq : x = pivot := (cmp_eq_eq_iff x pivot).mp hcmp
          simp [partition3, ihBelow, ihEqual, ihAbove, heq]
      | gt =>
          have hgt : pivot < x := (cmp_eq_gt_iff x pivot).mp hcmp
          have hnbelow : ¬x < pivot := not_lt_of_ge hgt.le
          have hne : x ≠ pivot := hgt.ne'
          simp [partition3, hcmp, ihBelow, ihEqual, ihAbove, hgt, hnbelow, hne]

/-- **The below list of a three-way partition is a filter.** For every element $p$ of a linearly
ordered type $\alpha$ and every list $xs$ over $\alpha$, the below list of the stable three-way
partition of $xs$ around $p$ is the list of the elements $x$ of $xs$ with $x < p$, in their order
in $xs$ and with their multiplicities. -/
theorem partition3_below_eq_filter (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.below = xs.filter (fun x => x < pivot) :=
  (partition3_eq_filters pivot xs).1

/-- **The equal list of a three-way partition is a filter.** For every element $p$ of a linearly
ordered type $\alpha$ and every list $xs$ over $\alpha$, the equal list of the stable three-way
partition of $xs$ around $p$ is the list of the elements $x$ of $xs$ with $x = p$, in their order
in $xs$ and with their multiplicities. -/
theorem partition3_equal_eq_filter (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.equal = xs.filter (fun x => x = pivot) :=
  (partition3_eq_filters pivot xs).2.1

/-- **The above list of a three-way partition is a filter.** For every element $p$ of a linearly
ordered type $\alpha$ and every list $xs$ over $\alpha$, the above list of the stable three-way
partition of $xs$ around $p$ is the list of the elements $x$ of $xs$ with $p < x$, in their order
in $xs$ and with their multiplicities. -/
theorem partition3_above_eq_filter (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.above = xs.filter (fun x => pivot < x) :=
  (partition3_eq_filters pivot xs).2.2

/-- **Sizes of the three parts of a three-way partition.** For every element $p$ of a linearly
ordered type $\alpha$ and every list $xs$ over $\alpha$, the lengths of the below, equal and above
lists of the stable three-way partition of $xs$ around $p$ add up to the length of $xs$. -/
theorem partition3_length (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length +
        (partition3 pivot xs).ret.above.length = xs.length := by
  simpa only [List.length_append, Nat.add_assoc] using
    (partition3_correct pivot xs).1.length_eq

end Cslib.Algorithms.Lean.TimeM
