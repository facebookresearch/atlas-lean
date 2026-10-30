/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.Basic
public import Mathlib.Data.Set.Defs

/-!
# Function reconstruction by quadtrees

`qt_of_fun f n` samples a curried function on the square of side `2 ^ n`
and builds a full, uncompressed tree of height `n`. `get` reads polymorphic
leaves. At scale zero it follows the first child to a leaf, resetting both
coordinates to zero at each branch; it does not use the Boolean lookup's
`false` default. At positive scales both lookup variants use the shared
low/low, low/high, high/low, high/high quadrant order and modular coordinates.

Adapted from `auto-fdsa-13-02/solution/Solution.lean` and its specification
`auto-fdsa-13-02/environment/Task.lean` in `codimango/sw-verification-zhih`
at pinned commit
`16412d086eb5af2e74da78731bde50da0667bc79`.

`fdsa_chap13_ex02` preserves the original graded reconstruction statement:
lookup equals `f i j` for `(i, j) ∈ sqReg n`, including `n = 0`. The theorem
does not extend to coordinates outside this square, claim compression, or
provide a complexity bound. The additional height theorem makes explicit
that reconstruction always builds exactly `n` levels, even for a constant.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.QTree

universe u

/-- The represented square: both natural coordinates are below `2 ^ n`. -/
def sqReg (n : Nat) : Set (Nat × Nat) :=
  { p | p.1 < 2 ^ n ∧ p.2 < 2 ^ n }

/-- Membership in the represented square is a pair of strict bounds. -/
@[simp]
theorem mem_sqReg (n : Nat) (p : Nat × Nat) :
    p ∈ sqReg n ↔ p.1 < 2 ^ n ∧ p.2 < 2 ^ n :=
  Iff.rfl

/-- Polymorphic lookup. A leaf is constant; at zero scale a branch follows
its first child at `(0, 0)`. Positive scales select quadrants by the split. -/
def get {α : Type u} : Nat → QTree α → Nat → Nat → α
  | _, .L b, _, _ => b
  | 0, .Q t0 _ _ _, _, _ => get 0 t0 0 0
  | Nat.succ n, .Q t0 t1 t2 t3, i, j =>
      get n (selectTree (decide (i < 2 ^ n)) (decide (j < 2 ^ n))
        t0 t1 t2 t3) (i % 2 ^ n) (j % 2 ^ n)

/-- Samples `f` into a full tree. Every branch splits its coordinate square
into four equal quadrants, without compressing equal leaves. -/
def qt_of_fun {α : Type u} (f : Nat → Nat → α) : Nat → QTree α
  | 0 => .L (f 0 0)
  | Nat.succ n =>
      let t0 := qt_of_fun (fun i j => f i j) n
      let t1 := qt_of_fun (fun i j => f i (j + 2 ^ n)) n
      let t2 := qt_of_fun (fun i j => f (i + 2 ^ n) j) n
      let t3 := qt_of_fun (fun i j => f (i + 2 ^ n) (j + 2 ^ n)) n
      .Q t0 t1 t2 t3

/-- Reconstruction builds exactly the requested number of branch levels. -/
@[simp]
theorem height_qt_of_fun {α : Type u} (f : Nat → Nat → α) (n : Nat) :
    height (qt_of_fun f n) = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [qt_of_fun, height, ih]

private theorem mod_eq_sub_of_upper_half (a p : Nat)
    (hlo : p ≤ a) (hhi : a < p * 2) : a % p = a - p := by
  have ha : a = p + (a - p) := by omega
  have hlt : a - p < p := by omega
  calc
    a % p = (p + (a - p)) % p := by rw [← ha]
    _ = a - p := by simp [Nat.mod_eq_of_lt hlt]

/-- Reading a sampled function recovers its value within the represented
square. -/
theorem get_qt_of_fun {α : Type u} (f : Nat → Nat → α) (n i j : Nat)
    (h : (i, j) ∈ sqReg n) : get n (qt_of_fun f n) i j = f i j := by
  induction n generalizing f i j with
  | zero =>
      change i < 1 ∧ j < 1 at h
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst i; subst j
      simp [qt_of_fun, get]
  | succ n ih =>
      change i < 2 ^ (n + 1) ∧ j < 2 ^ (n + 1) at h
      have hi : i < 2 ^ n * 2 := by simpa only [Nat.pow_succ] using h.1
      have hj : j < 2 ^ n * 2 := by simpa only [Nat.pow_succ] using h.2
      rw [qt_of_fun, get]
      by_cases hi' : i < 2 ^ n
      · by_cases hj' : j < 2 ^ n
        · simp only [selectTree, decide_eq_true hi', decide_eq_true hj',
            ite_true]
          rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj']
          exact ih f i j ⟨hi', hj'⟩
        · simp only [selectTree, decide_eq_true hi', decide_eq_false hj',
            Bool.false_eq_true, ite_true, ite_false]
          rw [Nat.mod_eq_of_lt hi',
            mod_eq_sub_of_upper_half j (2 ^ n) (by omega) hj]
          have hm : (i, j - 2 ^ n) ∈ sqReg n := ⟨hi', by omega⟩
          have hr := ih (fun a b => f a (b + 2 ^ n)) i (j - 2 ^ n) hm
          have heq : j - 2 ^ n + 2 ^ n = j := by omega
          simpa only [heq] using hr
      · by_cases hj' : j < 2 ^ n
        · simp only [selectTree, decide_eq_false hi', decide_eq_true hj',
            Bool.false_eq_true, ite_false, ite_true]
          rw [mod_eq_sub_of_upper_half i (2 ^ n) (by omega) hi,
            Nat.mod_eq_of_lt hj']
          have hm : (i - 2 ^ n, j) ∈ sqReg n := ⟨by omega, hj'⟩
          have hr := ih (fun a b => f (a + 2 ^ n) b) (i - 2 ^ n) j hm
          have heq : i - 2 ^ n + 2 ^ n = i := by omega
          simpa only [heq] using hr
        · simp only [selectTree, decide_eq_false hi', decide_eq_false hj',
            Bool.false_eq_true, ite_false]
          rw [mod_eq_sub_of_upper_half i (2 ^ n) (by omega) hi,
            mod_eq_sub_of_upper_half j (2 ^ n) (by omega) hj]
          have hm : (i - 2 ^ n, j - 2 ^ n) ∈ sqReg n := ⟨by omega, by omega⟩
          have hr := ih (fun a b => f (a + 2 ^ n) (b + 2 ^ n))
            (i - 2 ^ n) (j - 2 ^ n) hm
          have hei : i - 2 ^ n + 2 ^ n = i := by omega
          have hej : j - 2 ^ n + 2 ^ n = j := by omega
          simpa only [hei, hej] using hr

/-- The original graded reconstruction theorem, under its original name. -/
theorem fdsa_chap13_ex02 {α : Type u} (f : Nat → Nat → α) (n i j : Nat) :
    (i, j) ∈ sqReg n → get n (qt_of_fun f n) i j = f i j :=
  get_qt_of_fun f n i j

end Cslib.Algorithms.Lean.QTree
