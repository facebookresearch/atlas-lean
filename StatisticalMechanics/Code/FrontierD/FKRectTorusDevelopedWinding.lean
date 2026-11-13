/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusWindingSubgroup

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def fkRectDevelopedStep (R : FKRectTorus) (x y : R.Vertex) : Int × Int :=
  ((y.1.val : Int) - x.1.val +
      (R.width : Int) * fkRectHorizontalSeamIncrement R x y,
    (y.2.val : Int) - x.2.val +
      (R.height : Int) * fkRectVerticalSeamIncrement R x y)

theorem fkRectDevelopedStep_swap (R : FKRectTorus) (x y : R.Vertex) :
    fkRectDevelopedStep R y x = -fkRectDevelopedStep R x y := by
  unfold fkRectDevelopedStep
  rw [fkRectHorizontalSeamIncrement_swap,
    fkRectVerticalSeamIncrement_swap]
  apply Prod.ext <;> simp <;> ring



def fkRectWalkDevelopedDisplacement (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex} :
    G.Walk x y -> Int × Int
  | .nil' _ => 0
  | .cons' x z _ _ p =>
      fkRectDevelopedStep R x z +
        fkRectWalkDevelopedDisplacement R p




theorem fkRectWalkDevelopedDisplacement_eq
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x y : R.Vertex}
    (p : G.Walk x y) :
    fkRectWalkDevelopedDisplacement R p =
      (((y.1.val : Int) - x.1.val) +
          (R.width : Int) * (fkRectWalkWinding R p).1,
        ((y.2.val : Int) - x.2.val) +
          (R.height : Int) * (fkRectWalkWinding R p).2) := by
  induction p with
  | nil =>
      simp only [fkRectWalkDevelopedDisplacement, fkRectWalkWinding,
        sub_self, zero_add, mul_zero]
      rfl
  | @cons a b c hab p ih =>
      simp only [fkRectWalkDevelopedDisplacement, fkRectWalkWinding]
      rw [ih]
      apply Prod.ext <;> simp [fkRectDevelopedStep] <;> ring


theorem fkRectClosedWalkDevelopedDisplacement_eq_period_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x : R.Vertex}
    (p : G.Walk x x) :
    fkRectWalkDevelopedDisplacement R p =
      ((R.width : Int) * (fkRectWalkWinding R p).1,
        (R.height : Int) * (fkRectWalkWinding R p).2) := by
  rw [fkRectWalkDevelopedDisplacement_eq]
  simp



theorem fkRectWindingIndependent_period_iff
    (R : FKRectTorus) (u v : Int × Int) :
    FKRectWindingIndependent
        ((R.width : Int) * u.1, (R.height : Int) * u.2)
        ((R.width : Int) * v.1, (R.height : Int) * v.2) <->
      FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  simp only [Prod.fst, Prod.snd]
  have hw : (R.width : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.width_pos)
  have hh : (R.height : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.height_pos)
  constructor <;> intro h
  · intro hz
    apply h
    calc
      (R.width : Int) * u.1 * ((R.height : Int) * v.2) -
          (R.height : Int) * u.2 * ((R.width : Int) * v.1) =
        (R.width : Int) * R.height *
          (u.1 * v.2 - u.2 * v.1) := by ring
      _ = 0 := by rw [hz, mul_zero]
  · intro hz
    apply h
    have hscaled : (R.width : Int) * R.height *
        (u.1 * v.2 - u.2 * v.1) = 0 := by
      calc
        (R.width : Int) * R.height *
            (u.1 * v.2 - u.2 * v.1) =
          ((R.width : Int) * u.1) * ((R.height : Int) * v.2) -
            ((R.height : Int) * u.2) * ((R.width : Int) * v.1) := by ring
        _ = 0 := hz
    exact (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero hw hh)

end

end StatMech.FrontierD
