/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Persistent union-find with parent-path costs

This module models a finite parent forest. A `Forest n` stores one parent and a
natural-number depth certificate for every `Fin n`; every non-root parent edge
strictly decreases that certificate. `find` follows parent pointers to a root.

`union` is persistent: it links the root of the first class to the root of the
second class. It deliberately models neither union-by-rank nor path compression.
The explicit `TimeM Nat` model charges one unit per vertex visited by `find` and
one additional unit for a root link only when the two representatives are
distinct (no link is performed, or charged, when they already coincide). Thus
`find` is bounded by certified forest depth, and `union` by the two searches
plus at most one. These are abstract operation counts, not compiler or
wall-clock costs.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

/-- A finite parent forest with a strictly decreasing certificate on non-root edges. -/
public structure Forest (n : Nat) where
  /-- Parent pointer for every vertex; roots point to themselves. -/
  parent : Fin n → Fin n
  /-- A certificate bounding the remaining parent-path length. -/
  depth : Fin n → Nat
  /-- Every non-root edge strictly decreases the depth certificate. -/
  parent_lt : ∀ x, parent x ≠ x → depth (parent x) < depth x

/-- Follow parent pointers to the unique root reached from `x`. -/
public def find {n : Nat} (forest : Forest n) (x : Fin n) : Fin n :=
  if _h : forest.parent x = x then x else find forest (forest.parent x)
termination_by forest.depth x
decreasing_by exact forest.parent_lt x _h

/-- The number of non-root parent edges traversed by `find`. -/
public def pathLength {n : Nat} (forest : Forest n) (x : Fin n) : Nat :=
  if h : forest.parent x = x then 0 else pathLength forest (forest.parent x) + 1
termination_by forest.depth x
decreasing_by exact forest.parent_lt x h

/-- Run `find`, charging one unit for every visited vertex, including the root. -/
public def findWithCost {n : Nat} (forest : Forest n) (x : Fin n) : TimeM Nat (Fin n) :=
  ⟨find forest x, pathLength forest x + 1⟩

/-- Two vertices are equivalent when `find` returns the same representative. -/
public def Equivalent {n : Nat} (forest : Forest n) (x y : Fin n) : Prop :=
  find forest x = find forest y

public instance equivalentDecidable {n : Nat} (forest : Forest n) (x y : Fin n) :
    Decidable (Equivalent forest x y) := by
  unfold Equivalent
  infer_instance

@[simp]
private theorem find_eq_self_of_parent_eq {n : Nat} (forest : Forest n) (x : Fin n)
    (h : forest.parent x = x) : find forest x = x := by
  rw [find]
  simp [h]

@[simp]
private theorem pathLength_eq_zero_of_parent_eq {n : Nat} (forest : Forest n) (x : Fin n)
    (h : forest.parent x = x) : pathLength forest x = 0 := by
  rw [pathLength]
  simp [h]

/-- The result of `find` is a root. -/
public theorem find_isRoot {n : Nat} (forest : Forest n) (x : Fin n) :
    forest.parent (find forest x) = find forest x := by
  rw [find.eq_1 forest x]
  split
  · assumption
  · exact find_isRoot forest (forest.parent x)
termination_by forest.depth x
decreasing_by exact forest.parent_lt x ‹forest.parent x ≠ x›

/-- Starting from a parent pointer reaches the same root. -/
public theorem find_parent {n : Nat} (forest : Forest n) (x : Fin n) :
    find forest (forest.parent x) = find forest x := by
  by_cases h : forest.parent x = x
  · rw [h]
  · rw [find.eq_1 forest x]
    simp only [h, ↓reduceDIte]

@[simp]
private theorem find_find {n : Nat} (forest : Forest n) (x : Fin n) :
    find forest (find forest x) = find forest x :=
  find_eq_self_of_parent_eq forest _ (find_isRoot forest x)

/-- Every queried vertex is equivalent to its representative. -/
public theorem find_in_class {n : Nat} (forest : Forest n) (x : Fin n) :
    Equivalent forest x (find forest x) := by
  simp [Equivalent]

private theorem pathLength_le_depth {n : Nat} (forest : Forest n) (x : Fin n) :
    pathLength forest x ≤ forest.depth x := by
  rw [pathLength.eq_1 forest x]
  split
  · omega
  · have hrec := pathLength_le_depth forest (forest.parent x)
    have hlt := forest.parent_lt x ‹forest.parent x ≠ x›
    omega
termination_by forest.depth x
decreasing_by exact forest.parent_lt x ‹forest.parent x ≠ x›

/-- The cost annotation is exactly the traversed edge count plus the root visit. -/
public theorem findWithCost_time {n : Nat} (forest : Forest n) (x : Fin n) :
    (findWithCost forest x).time = pathLength forest x + 1 := rfl

/-- One `find` costs at most the certified input depth plus one root visit. -/
public theorem findWithCost_time_le_depth {n : Nat} (forest : Forest n) (x : Fin n) :
  (findWithCost forest x).time ≤ forest.depth x + 1 := by
  rw [findWithCost_time]
  have h := pathLength_le_depth forest x
  omega

/-- Parent map obtained by redirecting `fromRoot` to `toRoot`. -/
public def linkParent {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n) :
    Fin n → Fin n := fun z => if z = fromRoot then toRoot else forest.parent z

/-- Depth certificate used after redirecting `fromRoot` to `toRoot`. -/
public def linkDepth {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n) :
    Fin n → Nat := fun z =>
      if Equivalent forest z fromRoot
      then forest.depth z + forest.depth toRoot + 1
      else forest.depth z

/-- Link two distinct certified roots, preserving the parent-forest invariant. -/
public def link {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n)
    (hFrom : forest.parent fromRoot = fromRoot)
    (hTo : forest.parent toRoot = toRoot) (hne : fromRoot ≠ toRoot) : Forest n where
  parent := linkParent forest fromRoot toRoot
  depth := linkDepth forest fromRoot toRoot
  parent_lt z hz := by
    by_cases hzr : z = fromRoot
    · subst z
      have hFromEq : Equivalent forest fromRoot fromRoot := by
        simp [Equivalent]
      have hToNe : ¬Equivalent forest toRoot fromRoot := by
        intro h
        have : toRoot = fromRoot := by
          simpa [Equivalent, find_eq_self_of_parent_eq forest _ hTo,
            find_eq_self_of_parent_eq forest _ hFrom] using h
        exact hne this.symm
      simp [linkParent, linkDepth, hFromEq, hToNe]
      omega
    · have hparent : forest.parent z ≠ z := by
        intro h
        apply hz
        simp [linkParent, hzr, h]
      have hlt := forest.parent_lt z hparent
      have heq : Equivalent forest (forest.parent z) fromRoot ↔
          Equivalent forest z fromRoot := by
        simp only [Equivalent, find_parent]
      by_cases hzClass : Equivalent forest z fromRoot
      · have hpClass : Equivalent forest (forest.parent z) fromRoot := heq.mpr hzClass
        simp [linkParent, linkDepth, hzr, hzClass, hpClass]
        omega
      · have hpClass : ¬Equivalent forest (forest.parent z) fromRoot :=
          fun h => hzClass (heq.mp h)
        simpa [linkParent, linkDepth, hzr, hzClass, hpClass] using hlt

/-- Persistently merge the classes of `x` and `y` by linking the first root to the second. -/
public def union {n : Nat} (forest : Forest n) (x y : Fin n) : Forest n :=
  let fromRoot := find forest x
  let toRoot := find forest y
  if h : fromRoot = toRoot then forest
  else link forest fromRoot toRoot (find_isRoot forest x) (find_isRoot forest y) h

private theorem find_link {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n)
    (hFrom : forest.parent fromRoot = fromRoot)
    (hTo : forest.parent toRoot = toRoot) (hne : fromRoot ≠ toRoot) (z : Fin n) :
    find (link forest fromRoot toRoot hFrom hTo hne) z =
      if find forest z = fromRoot then toRoot else find forest z := by
  by_cases hzr : z = fromRoot
  · subst z
    have hne' : toRoot ≠ fromRoot := Ne.symm hne
    have hLinkFrom : (link forest fromRoot toRoot hFrom hTo hne).parent fromRoot =
        toRoot := by
      simp [link, linkParent]
    have hLinkTo : (link forest fromRoot toRoot hFrom hTo hne).parent toRoot =
        toRoot := by
      simp [link, linkParent, hne', hTo]
    rw [find.eq_1]
    simp only [hLinkFrom, hne', ↓reduceDIte]
    rw [find_eq_self_of_parent_eq _ _ hLinkTo]
    simp [find_eq_self_of_parent_eq forest _ hFrom]
  · by_cases hzRoot : forest.parent z = z
    · have hLinkRoot : (link forest fromRoot toRoot hFrom hTo hne).parent z = z := by
        simp [link, linkParent, hzr, hzRoot]
      rw [find_eq_self_of_parent_eq _ _ hLinkRoot]
      have hFind : find forest z = z := find_eq_self_of_parent_eq forest z hzRoot
      simp [hFind, hzr]
    · have hLinkParent :
          (link forest fromRoot toRoot hFrom hTo hne).parent z = forest.parent z := by
        simp [link, linkParent, hzr]
      have hLinkNe :
          (link forest fromRoot toRoot hFrom hTo hne).parent z ≠ z := by
        simpa [hLinkParent] using hzRoot
      rw [find.eq_1]
      simp only [hLinkNe, ↓reduceDIte]
      rw [hLinkParent]
      rw [find_link forest fromRoot toRoot hFrom hTo hne (forest.parent z)]
      rw [find_parent]
termination_by forest.depth z
decreasing_by exact forest.parent_lt z hzRoot

/-- `union` redirects exactly the first selected representative to the second one. -/
public theorem find_union {n : Nat} (forest : Forest n) (x y z : Fin n) :
    find (union forest x y) z =
      if Equivalent forest z x then find forest y else find forest z := by
  by_cases hxy : find forest x = find forest y
  · simp only [union, hxy, ↓reduceDIte]
    by_cases hzx : Equivalent forest z x
    · have : find forest z = find forest y := by
        rw [Equivalent] at hzx
        exact hzx.trans hxy
      simp [hzx, this]
    · simp [hzx]
  · rw [union]
    simp only [hxy, ↓reduceDIte]
    rw [find_link]
    simp [Equivalent]

/-- `union` makes its two selected vertices equivalent. -/
public theorem union_equivalent {n : Nat} (forest : Forest n) (x y : Fin n) :
    Equivalent (union forest x y) x y := by
  by_cases hxy : find forest x = find forest y <;>
    simp [Equivalent, find_union, hxy, eq_comm]

/-- Unioning two already equivalent vertices leaves the persistent forest unchanged. -/
public theorem union_eq_self_of_equivalent {n : Nat} {forest : Forest n} {x y : Fin n}
    (h : Equivalent forest x y) : union forest x y = forest := by
  unfold Equivalent at h
  rw [union]
  simp only [h, ↓reduceDIte]

/-- Exact partition semantics: only the two selected old classes are merged. -/
public theorem equivalent_union_iff {n : Nat} (forest : Forest n) (x y a b : Fin n) :
    Equivalent (union forest x y) a b ↔
      Equivalent forest a b ∨
        (Equivalent forest a x ∧ Equivalent forest b y) ∨
        (Equivalent forest a y ∧ Equivalent forest b x) := by
  simp only [Equivalent, find_union]
  by_cases hxy : find forest x = find forest y
  · constructor
    · intro h
      left
      by_cases hax : find forest a = find forest x <;>
        by_cases hbx : find forest b = find forest x <;> simp_all
    · rintro (hab | hclasses)
      · by_cases hax : find forest a = find forest x <;>
          by_cases hbx : find forest b = find forest x <;> simp_all
      · rcases hclasses with hclasses | hclasses <;> rcases hclasses with ⟨ha, hb⟩
        all_goals
          by_cases hax : find forest a = find forest x <;>
            by_cases hbx : find forest b = find forest x <;> simp_all
  · by_cases hax : find forest a = find forest x <;>
      by_cases hbx : find forest b = find forest x <;> simp_all [eq_comm]

/-- Every class outside the first selected class keeps its representative:
if `z` is not equivalent to `x`, then `union` with any `y` preserves the
representative of `z` (no hypothesis on `y` is needed). -/
public theorem find_union_of_unrelated {n : Nat} (forest : Forest n) (x y z : Fin n)
    (hx : ¬Equivalent forest z x) :
    find (union forest x y) z = find forest z := by
  simp [find_union, hx]

/-- Run `union`, charging its two root searches and, only when the two
representatives are distinct, one root-link operation; when they already
coincide, `union` performs no link and none is charged. -/
public def unionWithCost {n : Nat} (forest : Forest n) (x y : Fin n) :
    TimeM Nat (Forest n) :=
  ⟨union forest x y,
    (findWithCost forest x).time + (findWithCost forest y).time +
      (if find forest x = find forest y then 0 else 1)⟩

/-- One `union` costs at most the two certified input depths plus three visits/links. -/
public theorem unionWithCost_time_le_depth {n : Nat} (forest : Forest n) (x y : Fin n) :
    (unionWithCost forest x y).time ≤ forest.depth x + forest.depth y + 3 := by
  have hx := findWithCost_time_le_depth forest x
  have hy := findWithCost_time_le_depth forest y
  simp only [unionWithCost]
  split_ifs <;> omega

end Cslib.Algorithms.Lean.UnionFind
