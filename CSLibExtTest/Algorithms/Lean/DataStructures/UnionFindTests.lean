/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind

import Mathlib.Tactic

/-! Importing tests for persistent union-find and its explicit cost model. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFindTests

open UnionFind

private def empty : Forest 0 where
  parent i := Fin.elim0 i
  depth i := Fin.elim0 i
  parent_lt i := Fin.elim0 i

private def singleton : Forest 1 where
  parent i := i
  depth _ := 0
  parent_lt _i h := False.elim (h rfl)

private def twoSingletons : Forest 2 where
  parent i := i
  depth _ := 0
  parent_lt _i h := False.elim (h rfl)

private def chain : Forest 4 where
  parent i := if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 1 else 2
  depth i := if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else 3
  parent_lt i h := by fin_cases i <;> simp_all

private def twoTrees : Forest 5 where
  parent i := if i = 1 then 0 else if i = 3 then 2 else i
  depth i := if i = 1 ∨ i = 3 then 1 else 0
  parent_lt i h := by fin_cases i <;> simp_all

example : Nonempty (Forest 0) := ⟨empty⟩
example : find singleton 0 = 0 := by simp [find, singleton]
example : pathLength singleton 0 = 0 := by simp [pathLength, singleton]
example : (findWithCost singleton 0).time = 1 := by
  simp [findWithCost, pathLength, singleton]

example : ¬Equivalent twoSingletons 0 1 := by
  simp [Equivalent, find, twoSingletons]
example : Equivalent (union twoSingletons 0 1) 0 1 :=
  union_equivalent twoSingletons 0 1
example : union (union twoSingletons 0 1) 0 1 = union twoSingletons 0 1 :=
  union_eq_self_of_equivalent (union_equivalent twoSingletons 0 1)

example : find chain 3 = 0 := by simp [find, chain]
example : pathLength chain 3 = 3 := by simp [pathLength, chain]
example : (findWithCost chain 3).ret = 0 := by simp [findWithCost, find, chain]
example : (findWithCost chain 3).time = 4 := by
  simp [findWithCost, pathLength, chain]

private def joined : Forest 5 := union twoTrees 1 3

example : find joined 0 = 2 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : find joined 1 = 2 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : find joined 3 = 2 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : find joined 4 = 4 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : joined.parent 0 = 2 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : joined.parent 1 = 0 := by
  simp [joined, union, find, link, linkParent, twoTrees]
example : (unionWithCost twoTrees 1 3).time = 5 := by
  simp [unionWithCost, findWithCost, pathLength, find, twoTrees]

/-- A no-op `union` of already-equivalent elements charges no root link. -/
example : (unionWithCost singleton 0 0).time = 2 := by
  simp [unionWithCost, findWithCost, pathLength, find, singleton]

example (n : Nat) (forest : Forest n) (x : Fin n) :
    forest.parent (find forest x) = find forest x :=
  find_isRoot forest x

example (n : Nat) (forest : Forest n) (x : Fin n) :
    Equivalent forest x (find forest x) :=
  find_in_class forest x

example (n : Nat) (forest : Forest n) (x : Fin n) :
    (findWithCost forest x).time = pathLength forest x + 1 :=
  findWithCost_time forest x

example (n : Nat) (forest : Forest n) (x : Fin n) :
    (findWithCost forest x).time ≤ forest.depth x + 1 :=
  findWithCost_time_le_depth forest x

example (n : Nat) (forest : Forest n) (x y z : Fin n) :
    find (union forest x y) z =
      if Equivalent forest z x then find forest y else find forest z :=
  find_union forest x y z

example (n : Nat) (forest : Forest n) (x y a b : Fin n) :
    Equivalent (union forest x y) a b ↔
      Equivalent forest a b ∨
        (Equivalent forest a x ∧ Equivalent forest b y) ∨
        (Equivalent forest a y ∧ Equivalent forest b x) :=
  equivalent_union_iff forest x y a b

example (n : Nat) (forest : Forest n) (x y z : Fin n)
    (hx : ¬Equivalent forest z x) :
    find (union forest x y) z = find forest z :=
  find_union_of_unrelated forest x y z hx

example (n : Nat) (forest : Forest n) (x y : Fin n) :
    (unionWithCost forest x y).time ≤ forest.depth x + forest.depth y + 3 :=
  unionWithCost_time_le_depth forest x y

/-- Importing modules can apply the certified `find` cost bound. -/
public theorem imported_find_cost_bound (n : Nat) (forest : Forest n) (x : Fin n) :
    (findWithCost forest x).time ≤ forest.depth x + 1 :=
  findWithCost_time_le_depth forest x

#check Forest
#check find
#check pathLength
#check findWithCost
#check Equivalent
#check union
#check unionWithCost
#check find_isRoot
#check find_in_class
#check findWithCost_time
#check findWithCost_time_le_depth
#check find_union
#check equivalent_union_iff
#check union_equivalent
#check union_eq_self_of_equivalent
#check find_union_of_unrelated
#check unionWithCost_time_le_depth
#check imported_find_cost_bound

#print axioms find_isRoot
#print axioms find_in_class
#print axioms findWithCost_time
#print axioms findWithCost_time_le_depth
#print axioms find_union
#print axioms equivalent_union_iff
#print axioms union_equivalent
#print axioms union_eq_self_of_equivalent
#print axioms find_union_of_unrelated
#print axioms unionWithCost_time_le_depth
#print axioms imported_find_cost_bound

end Cslib.Algorithms.Lean.UnionFindTests
