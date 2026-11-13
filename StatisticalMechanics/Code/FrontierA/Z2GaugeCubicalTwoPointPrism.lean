/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy
import Code.FrontierA.Z2GaugeTypedFK









namespace StatMech.FrontierA

open scoped BigOperators
open StatMech StatMech.Ising

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]

theorem typedSpinProduct_unanchorConfig (root x y : V) (b : Bool)
    (s : AnchoredConfig V root) :
    typedSpinProduct (unanchorConfig b s) x y =
      typedSpinProduct s.1 x y := by
  cases hx : s.1 x <;> cases hy : s.1 y <;> cases b <;>
    simp [typedSpinProduct, unanchorConfig, hx, hy]



theorem multibondIsingTwoPointNumerator_eq_two_mul_anchored
    (root : V) (ends : P -> V × V) (J : P -> Real) (x y : V) :
    (∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) =
      2 * ∑ s : AnchoredConfig V root,
        multibondIsingWeight ends J s.1 * typedSpinProduct s.1 x y := by
  calc
    (∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) =
        ∑ bs : Bool × AnchoredConfig V root,
          multibondIsingWeight ends J (unanchorConfig bs.1 bs.2) *
            typedSpinProduct (unanchorConfig bs.1 bs.2) x y := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro sigma
      rw [show unanchorConfig ((configEquivBoolAnchored root sigma).1)
          ((configEquivBoolAnchored root sigma).2) = sigma from
        (configEquivBoolAnchored root).left_inv sigma]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [multibondIsingWeight_eq_activity,
        multibondCut_unanchorConfig, typedSpinProduct_unanchorConfig]
      rw [Fintype.sum_bool]
      ring


def oddPrismPlusTwoPoint (J beta : Real) (n : Nat)
    (v w : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) : Real :=
  (∑ sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma) *
        (rectangularPrismSpin sigma v.x v.y v.z *
          rectangularPrismSpin sigma w.x w.y w.z)) /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n

theorem typedSpinProduct_oddCubical_eq_prismSpinProduct
    (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none)
    (q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)) :
    typedSpinProduct s.1 (some q) (some r) =
      rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s)
          (oddCubicalCellEquivPrismSite n q).x
          (oddCubicalCellEquivPrismSite n q).y
          (oddCubicalCellEquivPrismSite n q).z *
        rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s)
          (oddCubicalCellEquivPrismSite n r).x
          (oddCubicalCellEquivPrismSite n r).y
          (oddCubicalCellEquivPrismSite n r).z := by
  cases hq : s.1 (some q) <;> cases hr : s.1 (some r) <;>
    simp [typedSpinProduct, rectangularPrismSpin, spin,
      oddCubicalAnchoredEquivPrismConfig, oddCubicalCellEquivPrismSite,
      hq, hr]

theorem oddCubicalAnchoredWeight_eq_plusPrismWeight
    (J beta : Real) (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none) :
    multibondIsingWeight cubicalDualEnds (fun _ => beta * J) s.1 =
      Real.exp (-beta * rectangularPrismPlusEnergy J
        (oddCubicalAnchoredEquivPrismConfig n s)) := by
  unfold multibondIsingWeight
  rw [sum_oddCubicalDualAgreement_eq_plusPrismInteraction]
  unfold rectangularPrismPlusEnergy
  congr 1
  ring




theorem oddCubicalDualTwoPoint_eq_plusPrismTwoPoint
    (J beta : Real) (n : Nat)
    (q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)) :
    multibondIsingTwoPoint
        (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1)
          (c := 2 * n + 1))
        (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) =>
          beta * J)
        (some q) (some r) =
      oddPrismPlusTwoPoint J beta n
        (oddCubicalCellEquivPrismSite n q)
        (oddCubicalCellEquivPrismSite n r) := by
  unfold multibondIsingTwoPoint oddPrismPlusTwoPoint
  rw [multibondIsingTwoPointNumerator_eq_two_mul_anchored none]
  rw [oddCubicalDualPartition_eq_two_mul_plusPrismPartition]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : Real) ≠ 0)]
  rw [← Equiv.sum_comp (oddCubicalAnchoredEquivPrismConfig n)]
  apply congrArg (fun z : Real => z /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n)
  apply Finset.sum_congr rfl
  intro s _
  rw [oddCubicalAnchoredWeight_eq_plusPrismWeight,
    typedSpinProduct_oddCubical_eq_prismSpinProduct]

end

end StatMech.FrontierA
