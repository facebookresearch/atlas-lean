/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.Boolean

/-!
# Boolean quadtree regression tests

Concrete cells distinguish all four quadrant positions, split boundaries,
nested modular descent, constant-region shortcuts, ordered difference,
compression, and the zero-scale default. The symbolic tests consume the
complete original six-part theorem and every supporting correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.QTree.Boolean.Tests

private def q0 : QTree Bool := .Q (.L true) (.L false) (.L false) (.L false)
private def q1 : QTree Bool := .Q (.L false) (.L true) (.L false) (.L false)
private def q2 : QTree Bool := .Q (.L false) (.L false) (.L true) (.L false)
private def q3 : QTree Bool := .Q (.L false) (.L false) (.L false) (.L true)

-- Each singleton occupies a distinct quadrant at the split coordinates.
example : (get 2 q0 0 0, get 2 q0 0 2, get 2 q0 2 0, get 2 q0 2 2) =
    (true, false, false, false) := by decide
example : (get 2 q1 0 0, get 2 q1 0 2, get 2 q1 2 0, get 2 q1 2 2) =
    (false, true, false, false) := by decide
example : (get 2 q2 0 0, get 2 q2 0 2, get 2 q2 2 0, get 2 q2 2 2) =
    (false, false, true, false) := by decide
example : (get 2 q3 0 0, get 2 q3 0 2, get 2 q3 2 0, get 2 q3 2 2) =
    (false, false, false, true) := by decide

-- Just below and just above the split, and the far corner of a quadrant.
example : get 2 q0 1 1 = true := by decide
example : get 2 q0 1 2 = false := by decide
example : get 2 q3 3 3 = true := by decide

-- Two levels require modular reduction before selecting the second branch.
private def nested : QTree Bool := .Q q3 q2 q1 q0
example : (get 2 nested 1 1, get 2 nested 1 2,
    get 2 nested 2 1, get 2 nested 2 2) =
    (true, true, true, true) := by decide
example : get 2 nested 3 3 = false := by decide

-- Boolean zero scale is a default on any branch, but not on leaves.
example : get 0 q0 0 0 = false := rfl
example : get 0 nested 99 42 = false := rfl
example : get 0 (.L true) 99 42 = true := rfl
example : get 0 (.L false) 99 42 = false := rfl

-- Local compression changes zero-scale branch defaults but not positive scale.
example : Qc (.L true) (.L true) (.L true) (.L true) = .L true := by decide
example : Qc (.L false) (.L false) (.L false) (.L false) = .L false := by decide
example : Qc (.L true) (.L false) (.L false) (.L false) = q0 := by decide
example : get 0 (Qc (.L true) (.L true) (.L true) (.L true)) 0 0 = true :=
  by decide
example : get 0 (.Q (.L true) (.L true) (.L true) (.L true)) 0 0 = false := rfl
example : ¬compressed (.Q (.L true) (.L true) (.L true) (.L true)) := by
  simp [compressed]
example : compressed q0 := by simp [q0, compressed]
example : compressed (.Q q0 q0 q0 q0) := by simp [q0, compressed]
example : Qc q0 q0 q0 q0 = .Q q0 q0 q0 q0 := rfl

-- Complement and union/difference can recursively collapse a whole branch.
example : neg (neg q0) = q0 := by decide
example : neg (.Q (.L true) (.L true) (.L true) (.L true)) = .L false :=
  by decide
example : qtUnion q0 (neg q0) = .L true := by decide
example : qtDiff q0 q0 = .L false := by decide
example : (get 2 (qtUnion q0 q3) 0 0, get 2 (qtUnion q0 q3) 0 2,
    get 2 (qtUnion q0 q3) 2 0, get 2 (qtUnion q0 q3) 2 2) =
    (true, false, false, true) := by decide
example : qtDiff (qtUnion q0 q3) q0 = q3 := by decide
example : (get 2 (qtDiff (qtUnion q0 q3) q0) 0 0,
    get 2 (qtDiff (qtUnion q0 q3) q0) 0 2,
    get 2 (qtDiff (qtUnion q0 q3) q0) 2 0,
    get 2 (qtDiff (qtUnion q0 q3) q0) 2 2) =
    (false, false, false, true) := by decide
example : qtDiff (qtUnion q0 q3) q3 = q0 := by decide
example : qtDiff q0 q3 = q0 ∧ qtDiff q3 q0 = q3 := by decide

-- Every constant/branch shortcut, including non-normalized inputs.
example (a b : Bool) : qtUnion (.L a) (.L b) = .L (a || b) := by
  cases a <;> cases b <;> rfl
example (a b : Bool) : qtDiff (.L a) (.L b) = .L (a && !b) := by
  cases a <;> cases b <;> rfl
example (a b : Bool) :
    get 0 (qtUnion (.L a) (.L b)) 99 42 = (a || b) := by
  cases a <;> cases b <;> rfl
example (a b : Bool) :
    get 0 (qtDiff (.L a) (.L b)) 99 42 = (a && !b) := by
  cases a <;> cases b <;> rfl
example (t : QTree Bool) : qtUnion (.L true) t = .L true := rfl
example (t : QTree Bool) : qtUnion (.L false) t = t := rfl
example : qtUnion q0 (.L true) = .L true := rfl
example : qtUnion q0 (.L false) = q0 := rfl
example (t : QTree Bool) : qtDiff (.L false) t = .L false := rfl
example (t : QTree Bool) : qtDiff (.L true) t = neg t := rfl
example : qtDiff q0 (.L true) = .L false := rfl
example : qtDiff q0 (.L false) = q0 := rfl
example : qtUnion (.L false) (.Q (.L true) (.L true) (.L true) (.L true)) =
    .Q (.L true) (.L true) (.L true) (.L true) := rfl

-- Check all six original conjuncts separately, not just the semantic pair.
example (n : Nat) (s t : QTree Bool) (i j : Nat)
    (h : height s ≤ n ∧ height t ≤ n) :
    get n (qtUnion s t) i j = (get n s i j || get n t i j) :=
  fdsa_chap13_ex01.1 n s t i j h
example (n : Nat) (s t : QTree Bool) (i j : Nat)
    (h : height s ≤ n ∧ height t ≤ n) :
    get n (qtDiff s t) i j = (get n s i j && !get n t i j) :=
  fdsa_chap13_ex01.2.1 n s t i j h
example (s t : QTree Bool) : height (qtUnion s t) ≤ max (height s) (height t) :=
  fdsa_chap13_ex01.2.2.1 s t
example (s t : QTree Bool) : height (qtDiff s t) ≤ max (height s) (height t) :=
  fdsa_chap13_ex01.2.2.2.1 s t
example (s t : QTree Bool) (h : compressed s ∧ compressed t) :
    compressed (qtUnion s t) := fdsa_chap13_ex01.2.2.2.2.1 s t h
example (s t : QTree Bool) (h : compressed s ∧ compressed t) :
    compressed (qtDiff s t) := fdsa_chap13_ex01.2.2.2.2.2 s t h

-- The source theorem permits arbitrary natural coordinates, including outside.
example : get 2 (qtUnion q0 q3) 7 6 = (get 2 q0 7 6 || get 2 q3 7 6) :=
  get_qtUnion_correct _ _ _ _ _ (by decide)
example : get 2 (qtDiff nested q0) 7 6 = (get 2 nested 7 6 && !get 2 q0 7 6) :=
  get_qtDiff_correct _ _ _ _ _ (by decide)
example : get 2 (neg nested) 7 6 = !get 2 nested 7 6 :=
  get_neg_correct _ _ _ _ (by decide)
example : height (neg nested) ≤ height nested := height_neg_le _
example : compressed (neg q0) := compressed_neg _ (by simp [q0, compressed])
example : compressed (Qc q0 q1 q2 q3) :=
  compressed_Qc _ _ _ _ (by simp [q0, compressed]) (by simp [q1, compressed])
    (by simp [q2, compressed]) (by simp [q3, compressed])
example : height (Qc q0 q1 q2 q3) ≤
    Nat.succ (max (max (height q0) (height q1))
      (max (height q2) (height q3))) :=
  height_Qc_le _ _ _ _
example : get 2 (Qc q0 q1 q2 q3) 1 2 = get 2 (.Q q0 q1 q2 q3) 1 2 :=
  get_Qc_succ 1 _ _ _ _ _ _

end Cslib.Algorithms.Lean.QTree.Boolean.Tests
