/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveReindex
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellationLeft
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedCancellationRight
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryEndpointCancellation

/-!
# Intrinsic nonmixed cancellation for the Shih boundary

This file removes the external `p`, `q`, and gap parameters from the fixed-
bidegree cancellation theorems.  The resulting statements are directly
summable over `ShihIndex n`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- Insert a left position into an intrinsic Shih index. -/
def leftUpperOf {n : ℕ} (i : ShihIndex n) (a : Fin (i.p + 3)) :
    ShihIndex (n + 1) where
  p := ⟨i.p + 1, by have h := i.add_lt; omega⟩
  q := ⟨i.q, by
    change (i.q : ℕ) < n + 1 - ((i.p : ℕ) + 1)
    have hq : (i.q : ℕ) < n - (i.p : ℕ) := i.q.isLt
    omega⟩
  shuffle := Shuffle.leftBoundaryShuffle i.shuffle a

/-- The active upper face belonging to `leftUpperOf`. -/
def leftUpperFaceOf {n : ℕ} (i : ShihIndex n) (a : Fin (i.p + 3)) :
    Fin (n + 3) :=
  ⟨i.gap + (Shuffle.leftBoundaryIndex i.shuffle a).val, by
    have h := i.p_add_q_add_gap
    have ha := a.isLt
    omega⟩

/-- The lower face paired with a positive nonterminal left insertion. -/
def leftLowerFaceOf {n : ℕ} (i : ShihIndex n) (a : Fin (i.p + 3))
    (_ha : 0 < a.val) : Fin (n + 2) :=
  ⟨i.gap - 1 + a.val, by
    have h := i.p_add_q_add_gap
    have ha := a.isLt
    omega⟩

/-- Insert a right position into an intrinsic Shih index. -/
def rightUpperOf {n : ℕ} (i : ShihIndex n) (b : Fin (i.q + 2)) :
    ShihIndex (n + 1) where
  p := ⟨i.p, by have h := i.add_lt; omega⟩
  q := ⟨i.q + 1, by
    change (i.q : ℕ) + 1 < n + 1 - (i.p : ℕ)
    have h := i.add_lt
    omega⟩
  shuffle := Shuffle.rightBoundaryShuffle i.shuffle b

/-- The active upper face belonging to `rightUpperOf`. -/
def rightUpperFaceOf {n : ℕ} (i : ShihIndex n) (b : Fin (i.q + 2)) :
    Fin (n + 3) :=
  ⟨i.gap + (Shuffle.rightBoundaryIndex i.shuffle b).val, by
    have h := i.p_add_q_add_gap
    have hb := b.isLt
    omega⟩

/-- The lower face paired with a positive right insertion. -/
def rightLowerFaceOf {n : ℕ} (i : ShihIndex n) (b : Fin (i.q + 2))
    (_hb : 0 < b.val) : Fin (n + 2) :=
  ⟨i.gap + i.p + b.val, by
    have h := i.p_add_q_add_gap
    have hb := b.isLt
    omega⟩

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Intrinsic form of interior inserted-left cancellation. -/
theorem leftInteriorTerm_add_lower_eq_zero
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n)
    (a : Fin (i.p + 3)) (ha0 : 0 < a.val)
    (haLast : a.val < i.p + 2) :
    shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf a)
        (i.leftUpperFaceOf a) +
      shihLowerBoundaryTerm X Y n (i.leftLowerFaceOf a ha0) i = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihLeftBoundaryTerm_add_lower_eq_zero
    X Y p q m hm t a ha0 haLast
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1;
    simp only [leftUpperOf, leftUpperFaceOf, leftLowerFaceOf,
      ofGap, leftBoundaryUpperIndex, leftBoundaryUpperFace,
      leftBoundaryLowerFace, gap, hgap]

/-- Intrinsic form of positive inserted-right cancellation. -/
theorem rightPositiveTerm_add_lower_eq_zero
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n)
    (b : Fin (i.q + 2)) (hb : 0 < b.val) :
    shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf b)
        (i.rightUpperFaceOf b) +
      shihLowerBoundaryTerm X Y n (i.rightLowerFaceOf b hb) i = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihRightBoundaryTerm_add_lower_eq_zero
    X Y p q m hm t b hb
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1;
    simp only [rightUpperOf, rightUpperFaceOf, rightLowerFaceOf,
      ofGap, rightBoundaryUpperIndex, rightBoundaryUpperFace,
      rightBoundaryLowerFace, gap, hgap]

/-- Intrinsic form of the last-left/zero-right endpoint cancellation. -/
theorem leftLastTerm_add_rightZeroTerm_eq_zero
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n) :
    shihUpperBoundaryTerm X Y (n + 1)
        (i.leftUpperOf (Fin.last (i.p + 2)))
        (i.leftUpperFaceOf (Fin.last (i.p + 2))) +
      shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf 0)
        (i.rightUpperFaceOf 0) = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihLeftLastBoundaryTerm_add_rightZero_eq_zero
    X Y p q m hm t
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1;
    simp only [leftUpperOf, leftUpperFaceOf, rightUpperOf,
      rightUpperFaceOf, leftBoundaryUpperIndex, leftBoundaryUpperFace,
      rightBoundaryUpperIndex, rightBoundaryUpperFace, gap, hgap]

/-- The canonical left-interior upper and lower data cancel after summing
over every preceding-degree Shih index. -/
theorem leftInteriorData_sum_eq_zero
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      ∑ z : ShihLowerLeftData n,
        shihLowerBoundaryTerm X Y n
          (z.1.leftLowerFaceOf z.2 z.2.property.1) z.1 = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    leftInteriorTerm_add_lower_eq_zero X Y z.1 z.2
      z.2.property.1 z.2.property.2

/-- The canonical positive-right upper and lower data cancel after summing
over every preceding-degree Shih index. -/
theorem rightPositiveData_sum_eq_zero
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2)) +
      ∑ z : ShihLowerRightData n,
        shihLowerBoundaryTerm X Y n
          (z.1.rightLowerFaceOf z.2 z.2.property) z.1 = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    rightPositiveTerm_add_lower_eq_zero X Y z.1 z.2 z.2.property

/-- The terminal-left and initial-right endpoint families cancel after
summing over every preceding-degree Shih index. -/
theorem leftLastSum_add_rightZeroSum_eq_zero
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2)))) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ =>
    leftLastTerm_add_rightZeroTerm_eq_zero X Y i

end ShihIndex

end AlgebraicTopology.EilenbergZilber
