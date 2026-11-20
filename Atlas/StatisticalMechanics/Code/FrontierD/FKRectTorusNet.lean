/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusEulerDefect

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def fkRectCrossesHorizontalSeam (R : FKRectTorus)
    (e : Sym2 R.Vertex) : Prop :=
  Sym2.lift ⟨fun x y =>
    (x.1.val = 0 ∧ y.1.val + 1 = R.width) ∨
      (y.1.val = 0 ∧ x.1.val + 1 = R.width), by
        intro x y
        apply propext
        tauto⟩ e



def fkRectCrossesVerticalSeam (R : FKRectTorus)
    (e : Sym2 R.Vertex) : Prop :=
  Sym2.lift ⟨fun x y =>
    (x.2.val = 0 ∧ y.2.val + 1 = R.height) ∨
      (y.2.val = 0 ∧ x.2.val + 1 = R.height), by
        intro x y
        apply propext
        tauto⟩ e

@[simp] theorem fkRectCrossesHorizontalSeam_mk
    (R : FKRectTorus) (x y : R.Vertex) :
    fkRectCrossesHorizontalSeam R s(x, y) ↔
      (x.1.val = 0 ∧ y.1.val + 1 = R.width) ∨
        (y.1.val = 0 ∧ x.1.val + 1 = R.width) := Iff.rfl

@[simp] theorem fkRectCrossesVerticalSeam_mk
    (R : FKRectTorus) (x y : R.Vertex) :
    fkRectCrossesVerticalSeam R s(x, y) ↔
      (x.2.val = 0 ∧ y.2.val + 1 = R.height) ∨
        (y.2.val = 0 ∧ x.2.val + 1 = R.height) := Iff.rfl



def fkRectHorizontalCutGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex :=
  (fkRectOpenGraph R omega).deleteEdges (fkRectCrossesHorizontalSeam R)



def fkRectVerticalCutGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex :=
  (fkRectOpenGraph R omega).deleteEdges (fkRectCrossesVerticalSeam R)



def FKRectHorizontalWindingWitness (R : FKRectTorus)
    (omega : R.Configuration) (x y : R.Vertex) : Prop :=
  (fkRectOpenGraph R omega).Adj x y ∧
    fkRectCrossesHorizontalSeam R s(x, y) ∧
    (fkRectHorizontalCutGraph R omega).Reachable x y



def FKRectVerticalWindingWitness (R : FKRectTorus)
    (omega : R.Configuration) (x y : R.Vertex) : Prop :=
  (fkRectOpenGraph R omega).Adj x y ∧
    fkRectCrossesVerticalSeam R s(x, y) ∧
    (fkRectVerticalCutGraph R omega).Reachable x y


def fkRectHorizontalSeamIncrement (R : FKRectTorus)
    (x y : R.Vertex) : Int :=
  if x.1.val + 1 = R.width ∧ y.1.val = 0 then 1
  else if x.1.val = 0 ∧ y.1.val + 1 = R.width then -1
  else 0


def fkRectVerticalSeamIncrement (R : FKRectTorus)
    (x y : R.Vertex) : Int :=
  if x.2.val + 1 = R.height ∧ y.2.val = 0 then 1
  else if x.2.val = 0 ∧ y.2.val + 1 = R.height then -1
  else 0



def fkRectWalkWinding (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} : G.Walk x y → Int × Int
  | .nil' _ => (0, 0)
  | .cons' x z _ _ p =>
      (fkRectHorizontalSeamIncrement R x z + (fkRectWalkWinding R p).1,
        fkRectVerticalSeamIncrement R x z + (fkRectWalkWinding R p).2)


def FKRectWindingIndependent (u v : Int × Int) : Prop :=
  u.1 * v.2 - u.2 * v.1 ≠ 0

theorem not_FKRectWindingIndependent_self (u : Int × Int) :
    ¬ FKRectWindingIndependent u u := by
  simp [FKRectWindingIndependent, mul_comm]



theorem fkRect_diagonal_winding_not_independent :
    ¬ FKRectWindingIndependent ((1, 1) : Int × Int) (1, 1) := by
  exact not_FKRectWindingIndependent_self _





def FKRectHasNet (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∃ x : R.Vertex,
    ∃ p q : (fkRectOpenGraph R omega).Walk x x,
      FKRectWindingIndependent
        (fkRectWalkWinding R p) (fkRectWalkWinding R q)


def fkRectNetIndicator (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  by
    classical
    exact if FKRectHasNet R omega then 1 else 0

theorem fkRectNetIndicator_eq_one_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 1 ↔ FKRectHasNet R omega := by
  classical
  unfold fkRectNetIndicator
  by_cases h : FKRectHasNet R omega <;> simp [h]

theorem fkRectNetIndicator_eq_zero_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 0 ↔ ¬ FKRectHasNet R omega := by
  classical
  unfold fkRectNetIndicator
  by_cases h : FKRectHasNet R omega <;> simp [h]

theorem fkRectNetIndicator_le_one
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega ≤ 1 := by
  classical
  unfold fkRectNetIndicator
  split <;> omega

end

end StatMech.FrontierD
