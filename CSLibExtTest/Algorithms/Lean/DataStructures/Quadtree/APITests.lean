/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree

/-!
# Combined quadtree public API tests

Importing only the facade exposes both graded theorem names, the shared
carrier and selector, and distinct lookup functions. In particular these
tests prevent accidentally identifying the two zero-scale semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.QuadtreeAPITests

open QTree

private def allTrue : QTree Bool := .Q (.L true) (.L true) (.L true) (.L true)

example : Boolean.get 0 allTrue 99 42 = false := rfl
example : QTree.get 0 allTrue 99 42 = true := by simp [QTree.get, allTrue]
example : Boolean.get 0 allTrue 99 42 ≠ QTree.get 0 allTrue 99 42 := by
  simp [Boolean.get, QTree.get, allTrue]
example : Boolean.get 1 allTrue 0 0 = QTree.get 1 allTrue 0 0 := by
  simp [Boolean.get, QTree.get, allTrue, selectTree]
example :
    Boolean.get 1 (.Q allTrue (.L false) (.L false) (.L false)) 0 0 = false :=
  by decide
example :
    QTree.get 1 (.Q allTrue (.L false) (.L false) (.L false)) 0 0 = true := by
  simp [QTree.get, allTrue, selectTree]

-- A single carrier and selector support both Boolean and non-Boolean data.
example {α : Type} (t0 t1 t2 t3 : QTree α) :
    selectTree true true t0 t1 t2 t3 = t0 := rfl
example {α : Type} (t0 t1 t2 t3 : QTree α) :
    selectTree true false t0 t1 t2 t3 = t1 := rfl
example {α : Type} (t0 t1 t2 t3 : QTree α) :
    selectTree false true t0 t1 t2 t3 = t2 := rfl
example {α : Type} (t0 t1 t2 t3 : QTree α) :
    selectTree false false t0 t1 t2 t3 = t3 := rfl
example {α : Type} {t0 t1 t2 t3 : QTree α} {n : Nat}
    (h : height (.Q t0 t1 t2 t3) ≤ n + 1) :
    height t0 ≤ n ∧ height t1 ≤ n ∧ height t2 ≤ n ∧ height t3 ≤ n :=
  height_children_le h

-- Check the complete original Boolean theorem type through the facade.
example :
    (∀ n t1 t2 i j, height t1 ≤ n ∧ height t2 ≤ n →
      Boolean.get n (Boolean.qtUnion t1 t2) i j =
        (Boolean.get n t1 i j || Boolean.get n t2 i j)) ∧
    (∀ n t1 t2 i j, height t1 ≤ n ∧ height t2 ≤ n →
      Boolean.get n (Boolean.qtDiff t1 t2) i j =
        (Boolean.get n t1 i j && !Boolean.get n t2 i j)) ∧
    (∀ t1 t2, height (Boolean.qtUnion t1 t2) ≤ max (height t1) (height t2)) ∧
    (∀ t1 t2, height (Boolean.qtDiff t1 t2) ≤ max (height t1) (height t2)) ∧
    (∀ t1 t2, compressed t1 ∧ compressed t2 →
      compressed (Boolean.qtUnion t1 t2)) ∧
    (∀ t1 t2, compressed t1 ∧ compressed t2 →
      compressed (Boolean.qtDiff t1 t2)) :=
  Boolean.fdsa_chap13_ex01

-- Reconstruction has no extra compression or equality assumptions.
example {α : Type} (f : Nat → Nat → α) (n i j : Nat) :
    (i, j) ∈ sqReg n → QTree.get n (qt_of_fun f n) i j = f i j :=
  fdsa_chap13_ex02 f n i j

/--
info: 'Cslib.Algorithms.Lean.QTree.Boolean.fdsa_chap13_ex01' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.QTree.Boolean.fdsa_chap13_ex01

/--
info: 'Cslib.Algorithms.Lean.QTree.fdsa_chap13_ex02' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Algorithms.Lean.QTree.fdsa_chap13_ex02

end Cslib.Algorithms.Lean.QuadtreeAPITests
