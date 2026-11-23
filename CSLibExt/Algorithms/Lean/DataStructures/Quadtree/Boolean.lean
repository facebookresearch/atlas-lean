/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Quadtree.Basic

import Mathlib.Order.MinMax

/-!
# Boolean region quadtree operations

`Qc` collapses four equal Boolean leaves, `neg` complements a region,
`qtUnion` takes its union, and `qtDiff` takes its ordered difference.
`get n t i j` reads the cell at scale `n`: leaves are constant, branches
split at `2 ^ (n - 1)` and reduce coordinates modulo that split. At scale
zero a branch returns `false`, deliberately unlike the polymorphic
`QTree.get` in the function-reconstruction module.

Adapted from `auto-fdsa-13-01/solution/Solution.lean` and its specification
`auto-fdsa-13-01/environment/Task.lean` in `codimango/sw-verification-zhih`
at pinned commit
`16412d086eb5af2e74da78731bde50da0667bc79`.

The original graded theorem `fdsa_chap13_ex01` retains all six conjuncts:
pointwise union and difference at any scale bounding both input heights,
both unconditional height bounds, and preservation of compression for
both operations on compressed inputs. The pointwise claims hold for all
natural coordinates, not just those in the represented square. They do
not claim meaningful set semantics for a tree taller than the scale.
Operations preserve compression; they do not normalize arbitrary inputs
that are returned unchanged by a leaf shortcut. No cost bounds are proved.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.QTree.Boolean

/-- A branch constructor that collapses four identical Boolean leaves.
This is local compression, not recursive normalization of its arguments. -/
def Qc : QTree Bool → QTree Bool → QTree Bool → QTree Bool → QTree Bool
  | .L x0, .L x1, .L x2, .L x3 =>
      if x0 = x1 ∧ x1 = x2 ∧ x2 = x3 then .L x0
      else .Q (.L x0) (.L x1) (.L x2) (.L x3)
  | t0, t1, t2, t3 => .Q t0 t1 t2 t3

/-- Boolean lookup with `false` on a nonleaf at scale zero.
Leaves ignore coordinates; positive scales use the shared quadrant order. -/
def get : Nat → QTree Bool → Nat → Nat → Bool
  | _, .L b, _, _ => b
  | 0, .Q _ _ _ _, _, _ => false
  | Nat.succ n, .Q t0 t1 t2 t3, i, j =>
      get n (selectTree (decide (i < 2 ^ n)) (decide (j < 2 ^ n))
        t0 t1 t2 t3) (i % 2 ^ n) (j % 2 ^ n)

/-- Complements every leaf, compressing the rebuilt branches. -/
def neg : QTree Bool → QTree Bool
  | .L b => .L (!b)
  | .Q t0 t1 t2 t3 => Qc (neg t0) (neg t1) (neg t2) (neg t3)

/-- Boolean union, short-circuiting constant regions and compressing
branches when both inputs are branches. -/
def qtUnion : QTree Bool → QTree Bool → QTree Bool
  | .L true, _ => .L true
  | .L false, t => t
  | .Q _ _ _ _, .L true => .L true
  | .Q s0 s1 s2 s3, .L false => .Q s0 s1 s2 s3
  | .Q s0 s1 s2 s3, .Q t0 t1 t2 t3 =>
      Qc (qtUnion s0 t0) (qtUnion s1 t1) (qtUnion s2 t2) (qtUnion s3 t3)

/-- Ordered Boolean difference: cells in the first region but not the second.
A full first region complements the second; an empty second returns the
first. -/
def qtDiff : QTree Bool → QTree Bool → QTree Bool
  | .L false, _ => .L false
  | .L true, t => neg t
  | .Q s0 s1 s2 s3, .L false => .Q s0 s1 s2 s3
  | .Q _ _ _ _, .L true => .L false
  | .Q s0 s1 s2 s3, .Q t0 t1 t2 t3 =>
      Qc (qtDiff s0 t0) (qtDiff s1 t1) (qtDiff s2 t2) (qtDiff s3 t3)

/-- Local compression never increases a branch's height. -/
theorem height_Qc_le (t0 t1 t2 t3 : QTree Bool) :
    height (Qc t0 t1 t2 t3) ≤
      Nat.succ (max (max (height t0) (height t1))
        (max (height t2) (height t3))) := by
  cases t0 <;> cases t1 <;> cases t2 <;> cases t3 <;>
    simp only [Qc] <;>
      first | (split <;> simp only [height] <;> omega) | (simp only [height]; omega)

/-- Four compressed children produce a compressed result. -/
theorem compressed_Qc (t0 t1 t2 t3 : QTree Bool)
    (h0 : compressed t0) (h1 : compressed t1)
    (h2 : compressed t2) (h3 : compressed t3) :
    compressed (Qc t0 t1 t2 t3) := by
  by_cases hAll : ∃ x0 x1 x2 x3, t0 = QTree.L x0 ∧
      t1 = QTree.L x1 ∧ t2 = QTree.L x2 ∧ t3 = QTree.L x3
  · obtain ⟨x0, x1, x2, x3, r0, r1, r2, r3⟩ := hAll
    subst r0; subst r1; subst r2; subst r3
    rw [Qc.eq_1]
    split
    · trivial
    · rename_i hne
      simp only [compressed]
      refine ⟨trivial, trivial, trivial, trivial, ?_⟩
      rintro ⟨x, h0eq, h1eq, h2eq, h3eq⟩
      have hx1 : x1 = x0 := QTree.L.inj h1eq
      have hx2 : x2 = x0 := QTree.L.inj h2eq
      have hx3 : x3 = x0 := QTree.L.inj h3eq
      exact hne ⟨hx1.symm, hx1.trans hx2.symm, hx2.trans hx3.symm⟩
  · have hQc : Qc t0 t1 t2 t3 = QTree.Q t0 t1 t2 t3 := by
      apply Qc.eq_2
      intro x0 x1 x2 x3 e0 e1 e2 e3
      exact hAll ⟨x0, x1, x2, x3, e0, e1, e2, e3⟩
    rw [hQc]
    refine ⟨h0, h1, h2, h3, ?_⟩
    rintro ⟨x, hx0, hx1, hx2, hx3⟩
    exact hAll ⟨x, x, x, x, hx0, hx1.trans hx0,
      hx2.trans hx0, hx3.trans hx0⟩

/-- Compression preserves positive-scale lookup. Scale zero is excluded:
collapsing four `true` leaves changes a branch's zero-scale default. -/
theorem get_Qc_succ (n : Nat) (t0 t1 t2 t3 : QTree Bool) (i j : Nat) :
    get (n + 1) (Qc t0 t1 t2 t3) i j =
      get (n + 1) (QTree.Q t0 t1 t2 t3) i j := by
  by_cases hAll : ∃ x0 x1 x2 x3, t0 = QTree.L x0 ∧
      t1 = QTree.L x1 ∧ t2 = QTree.L x2 ∧ t3 = QTree.L x3
  · obtain ⟨x0, x1, x2, x3, r0, r1, r2, r3⟩ := hAll
    subst r0; subst r1; subst r2; subst r3
    rw [Qc.eq_1]
    split
    · rename_i heq
      obtain ⟨h01, h12, h23⟩ := heq
      subst x1; subst x2; subst x3
      cases hi : decide (i < 2 ^ n) <;>
        cases hj : decide (j < 2 ^ n) <;> simp [get, selectTree, hi, hj]
    · rfl
  · have hQc : Qc t0 t1 t2 t3 = QTree.Q t0 t1 t2 t3 := by
      apply Qc.eq_2
      intro x0 x1 x2 x3 e0 e1 e2 e3
      exact hAll ⟨x0, x1, x2, x3, e0, e1, e2, e3⟩
    rw [hQc]

/-- Complementation does not increase height. -/
theorem height_neg_le (t : QTree Bool) : height (neg t) ≤ height t := by
  induction t with
  | L b => simp [neg, height]
  | Q t0 t1 t2 t3 ih0 ih1 ih2 ih3 =>
      have hQc := height_Qc_le (neg t0) (neg t1) (neg t2) (neg t3)
      simp only [neg, height]
      omega

/-- Complementation preserves compression of the input. -/
theorem compressed_neg (t : QTree Bool) (hc : compressed t) :
    compressed (neg t) := by
  induction t with
  | L b => simp [neg, compressed]
  | Q t0 t1 t2 t3 ih0 ih1 ih2 ih3 =>
      exact compressed_Qc _ _ _ _ (ih0 hc.1) (ih1 hc.2.1)
        (ih2 hc.2.2.1) (ih3 hc.2.2.2.1)

/-- Complementation negates each lookup whenever the scale bounds height. -/
theorem get_neg_correct (t : QTree Bool) (n i j : Nat)
    (h : height t ≤ n) : get n (neg t) i j = (!get n t i j) := by
  induction t generalizing n i j with
  | L b => simp [neg, get]
  | Q t0 t1 t2 t3 ih0 ih1 ih2 ih3 =>
      cases n with
      | zero => simp [height] at h
      | succ n =>
          obtain ⟨h0, h1, h2, h3⟩ := height_children_le h
          rw [neg, get_Qc_succ]
          cases hi : decide (i < 2 ^ n) <;>
            cases hj : decide (j < 2 ^ n) <;>
            simp [get, selectTree, hi, hj, ih0 _ _ _ h0,
              ih1 _ _ _ h1, ih2 _ _ _ h2, ih3 _ _ _ h3]

private theorem max4_bounds (a b c d : Nat) :
    a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
      c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩

private theorem height_Qc_le_max
    (s0 s1 s2 s3 t0 t1 t2 t3 u0 u1 u2 u3 : QTree Bool)
    (h0 : height u0 ≤ max (height s0) (height t0))
    (h1 : height u1 ≤ max (height s1) (height t1))
    (h2 : height u2 ≤ max (height s2) (height t2))
    (h3 : height u3 ≤ max (height s3) (height t3)) :
    height (Qc u0 u1 u2 u3) ≤
      max (height (.Q s0 s1 s2 s3)) (height (.Q t0 t1 t2 t3)) := by
  obtain ⟨hs0, hs1, hs2, hs3⟩ := max4_bounds (height s0) (height s1)
    (height s2) (height s3)
  obtain ⟨ht0, ht1, ht2, ht3⟩ := max4_bounds (height t0) (height t1)
    (height t2) (height t3)
  refine Nat.le_trans (height_Qc_le _ _ _ _) ?_
  simp only [height, Nat.succ_max_succ, Nat.succ_le_succ_iff, Nat.max_le]
  exact ⟨⟨Nat.le_trans h0 (max_le_max hs0 ht0),
    Nat.le_trans h1 (max_le_max hs1 ht1)⟩,
    ⟨Nat.le_trans h2 (max_le_max hs2 ht2),
      Nat.le_trans h3 (max_le_max hs3 ht3)⟩⟩

/-- Union height is bounded by the maximum input height. -/
theorem height_qtUnion_le (t1 t2 : QTree Bool) :
    height (qtUnion t1 t2) ≤ max (height t1) (height t2) := by
  induction t1 generalizing t2 with
  | L b => cases b <;> simp [qtUnion, height]
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp [qtUnion, height]
      | Q t0 t1 t2 t3 =>
          exact height_Qc_le_max _ _ _ _ _ _ _ _ _ _ _ _
            (ih0 t0) (ih1 t1) (ih2 t2) (ih3 t3)

/-- Difference height is bounded by the maximum input height. -/
theorem height_qtDiff_le (t1 t2 : QTree Bool) :
    height (qtDiff t1 t2) ≤ max (height t1) (height t2) := by
  induction t1 generalizing t2 with
  | L b =>
      cases b with
      | false => simp [qtDiff, height]
      | true => simpa [qtDiff, height] using height_neg_le t2
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp [qtDiff, height]
      | Q t0 t1 t2 t3 =>
          exact height_Qc_le_max _ _ _ _ _ _ _ _ _ _ _ _
            (ih0 t0) (ih1 t1) (ih2 t2) (ih3 t3)

/-- Union preserves compression when both inputs are compressed. -/
theorem compressed_qtUnion (t1 t2 : QTree Bool)
    (hc : compressed t1 ∧ compressed t2) : compressed (qtUnion t1 t2) := by
  induction t1 generalizing t2 with
  | L b => cases b <;> simp_all [qtUnion, compressed]
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp_all [qtUnion, compressed]
      | Q t0 t1 t2 t3 =>
          exact compressed_Qc _ _ _ _ (ih0 _ ⟨hc.1.1, hc.2.1⟩)
            (ih1 _ ⟨hc.1.2.1, hc.2.2.1⟩)
            (ih2 _ ⟨hc.1.2.2.1, hc.2.2.2.1⟩)
            (ih3 _ ⟨hc.1.2.2.2.1, hc.2.2.2.2.1⟩)

/-- Difference preserves compression when both inputs are compressed. -/
theorem compressed_qtDiff (t1 t2 : QTree Bool)
    (hc : compressed t1 ∧ compressed t2) : compressed (qtDiff t1 t2) := by
  induction t1 generalizing t2 with
  | L b =>
      cases b with
      | false => simp [qtDiff, compressed]
      | true => exact compressed_neg t2 hc.2
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp_all [qtDiff, compressed]
      | Q t0 t1 t2 t3 =>
          exact compressed_Qc _ _ _ _ (ih0 _ ⟨hc.1.1, hc.2.1⟩)
            (ih1 _ ⟨hc.1.2.1, hc.2.2.1⟩)
            (ih2 _ ⟨hc.1.2.2.1, hc.2.2.2.1⟩)
            (ih3 _ ⟨hc.1.2.2.2.1, hc.2.2.2.2.1⟩)

/-- Union is pointwise Boolean disjunction at a scale bounding both heights. -/
theorem get_qtUnion_correct (t1 t2 : QTree Bool) (n i j : Nat)
    (h : height t1 ≤ n ∧ height t2 ≤ n) :
    get n (qtUnion t1 t2) i j = (get n t1 i j || get n t2 i j) := by
  induction t1 generalizing t2 n i j with
  | L b => cases b <;> simp [qtUnion, get]
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp [qtUnion, get.eq_1]
      | Q t0 t1 t2 t3 =>
          cases n with
          | zero => simp [height] at h
          | succ n =>
              obtain ⟨hs0, hs1, hs2, hs3⟩ := height_children_le h.1
              obtain ⟨ht0, ht1, ht2, ht3⟩ := height_children_le h.2
              rw [qtUnion, get_Qc_succ]
              cases hi : decide (i < 2 ^ n) <;>
                cases hj : decide (j < 2 ^ n) <;>
                simp [get, selectTree, hi, hj, ih0 _ _ _ _ ⟨hs0, ht0⟩,
                  ih1 _ _ _ _ ⟨hs1, ht1⟩, ih2 _ _ _ _ ⟨hs2, ht2⟩,
                  ih3 _ _ _ _ ⟨hs3, ht3⟩]

/-- Difference is pointwise conjunction with the second region's complement,
provided the scale bounds both heights. -/
theorem get_qtDiff_correct (t1 t2 : QTree Bool) (n i j : Nat)
    (h : height t1 ≤ n ∧ height t2 ≤ n) :
    get n (qtDiff t1 t2) i j = (get n t1 i j && !get n t2 i j) := by
  induction t1 generalizing t2 n i j with
  | L b =>
      cases b with
      | false => simp [qtDiff, get]
      | true => simpa [qtDiff, get.eq_1] using get_neg_correct t2 n i j h.2
  | Q s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
      cases t2 with
      | L b => cases b <;> simp [qtDiff, get.eq_1]
      | Q t0 t1 t2 t3 =>
          cases n with
          | zero => simp [height] at h
          | succ n =>
              obtain ⟨hs0, hs1, hs2, hs3⟩ := height_children_le h.1
              obtain ⟨ht0, ht1, ht2, ht3⟩ := height_children_le h.2
              rw [qtDiff, get_Qc_succ]
              cases hi : decide (i < 2 ^ n) <;>
                cases hj : decide (j < 2 ^ n) <;>
                simp [get, selectTree, hi, hj, ih0 _ _ _ _ ⟨hs0, ht0⟩,
                  ih1 _ _ _ _ ⟨hs1, ht1⟩, ih2 _ _ _ _ ⟨hs2, ht2⟩,
                  ih3 _ _ _ _ ⟨hs3, ht3⟩]

/-- The original graded six-part correctness statement, under its original
name. -/
theorem fdsa_chap13_ex01 :
    (∀ n t1 t2 i j, height t1 ≤ n ∧ height t2 ≤ n →
      get n (qtUnion t1 t2) i j = (get n t1 i j || get n t2 i j)) ∧
    (∀ n t1 t2 i j, height t1 ≤ n ∧ height t2 ≤ n →
      get n (qtDiff t1 t2) i j = (get n t1 i j && !get n t2 i j)) ∧
    (∀ t1 t2, height (qtUnion t1 t2) ≤ max (height t1) (height t2)) ∧
    (∀ t1 t2, height (qtDiff t1 t2) ≤ max (height t1) (height t2)) ∧
    (∀ t1 t2, compressed t1 ∧ compressed t2 → compressed (qtUnion t1 t2)) ∧
    (∀ t1 t2, compressed t1 ∧ compressed t2 → compressed (qtDiff t1 t2)) := by
  exact ⟨fun n t1 t2 i j h => get_qtUnion_correct t1 t2 n i j h,
    fun n t1 t2 i j h => get_qtDiff_correct t1 t2 n i j h,
    height_qtUnion_le, height_qtDiff_le, compressed_qtUnion, compressed_qtDiff⟩

end Cslib.Algorithms.Lean.QTree.Boolean
