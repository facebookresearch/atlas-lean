/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.OfFunction

/-!
# Function-reconstruction quadtree regression tests

Tests cover zero scale, polymorphic leaves, first-child descent on oversized
trees, all four quadrant boundaries, interior cells requiring multiple
coordinate offsets, full uncompressed construction, and the exact domain
restriction in the original theorem. Concrete lookups use the recursion
equations, not the reconstruction theorem, to check the implementation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.QTree.Tests

private def grid (i j : Nat) : Nat := 10 * i + j
private def sampled : QTree Nat := qt_of_fun grid 2

example : qt_of_fun grid 0 = .L 0 := rfl
example : get 0 (qt_of_fun grid 0) 0 0 = 0 := by
  simp [get, qt_of_fun, grid]
example : qt_of_fun grid 1 = .Q (.L 0) (.L 1) (.L 10) (.L 11) := rfl

-- Distinct values, rather than symmetric data, detect quadrant transposition.
example : (get 2 sampled 0 0, get 2 sampled 0 2,
    get 2 sampled 2 0, get 2 sampled 2 2) = (0, 2, 20, 22) := by
  simp [sampled, get, qt_of_fun, selectTree, grid]
example : (get 2 sampled 1 1, get 2 sampled 1 3,
    get 2 sampled 3 1, get 2 sampled 3 3) = (11, 13, 31, 33) := by
  simp [sampled, get, qt_of_fun, selectTree, grid]
example : get 3 (qt_of_fun grid 3) 5 6 = 56 := by
  simp [get, qt_of_fun, selectTree, grid]

-- The polymorphic zero-scale fallback follows the first child recursively.
private def raw : QTree String :=
  .Q (.Q (.L "first") (.L "second") (.L "third") (.L "fourth"))
    (.L "east") (.L "south") (.L "corner")
example : get 0 raw 99 42 = "first" := by simp [get, raw]
example : get 0 (.L "constant") 99 42 = "constant" := by simp [get]
example : get 1 raw 0 0 = "first" := by simp [get, raw, selectTree]
example : get 1 raw 0 1 = "east" := by simp [get, raw, selectTree]
example : get 1 raw 1 0 = "south" := by simp [get, raw, selectTree]
example : get 1 raw 1 1 = "corner" := by simp [get, raw, selectTree]

-- Constant functions still yield full trees, not automatically compressed ones.
example : qt_of_fun (fun _ _ => true) 1 =
    .Q (.L true) (.L true) (.L true) (.L true) := rfl
example : ¬compressed (qt_of_fun (fun _ _ => true) 1) := by
  simp [qt_of_fun, compressed]
example : height sampled = 2 := height_qt_of_fun grid 2
example : height (qt_of_fun (fun _ _ => "constant") 3) = 3 :=
  height_qt_of_fun _ _

-- The original name and reusable theorem both support arbitrary result types.
example {α : Type} (f : Nat → Nat → α) :
    get 0 (qt_of_fun f 0) 0 0 = f 0 0 :=
  fdsa_chap13_ex02 f 0 0 0 (by simp)
example {α : Type} (f : Nat → Nat → α) (n i j : Nat)
    (h : (i, j) ∈ sqReg n) : get n (qt_of_fun f n) i j = f i j :=
  fdsa_chap13_ex02 f n i j h
example {α : Type} (f : Nat → Nat → α) (n i j : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    get n (qt_of_fun f n) i j = f i j := get_qt_of_fun f n i j ⟨hi, hj⟩
example : get 2 (qt_of_fun (fun i j => (i, j)) 2) 3 1 = (3, 1) :=
  fdsa_chap13_ex02 _ _ _ _ (by simp)
example : get 2 (qt_of_fun (fun i j => decide (i = j)) 2) 3 3 = true :=
  fdsa_chap13_ex02 _ _ _ _ (by simp)

-- The square is half-open; outside it reconstruction is not promised.
example : (0, 0) ∈ sqReg 0 := by simp
example : (1, 0) ∉ sqReg 0 := by simp
example : (3, 3) ∈ sqReg 2 := by simp
example : (4, 3) ∉ sqReg 2 := by simp
example : (3, 4) ∉ sqReg 2 := by simp
example : get 2 sampled 4 0 = 20 := by
  simp [sampled, get, qt_of_fun, selectTree, grid]
example : get 2 sampled 4 0 ≠ grid 4 0 := by
  simp [sampled, get, qt_of_fun, selectTree, grid]

end Cslib.Algorithms.Lean.QTree.Tests
