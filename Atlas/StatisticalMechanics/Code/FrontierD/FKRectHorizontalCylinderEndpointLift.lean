/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderPlanarization
import Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison












open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section




def fkRectHorizontalCylinderSquareLiftedDisplacement
    (dx : Int) (height : Nat) : Site 2 :=
  ![dx + (height / 2 : Nat), dx - (height / 2 : Nat) + 1]



theorem fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (sourceX targetX : Fin R.width)
    (hsource : source.1 = (sourceX, fkRectBottomRow R))
    (htarget : target.1 = (targetX, fkRectTopRow R)) :
    let dx :=
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 -
        (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1
    fkRectHorizontalCylinderUnexploredLiftSite R rho S target -
        fkRectHorizontalCylinderUnexploredLiftSite R rho S source =
      fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
  dsimp only
  let p := fkRectHorizontalCylinderUnexploredLiftPoint R rho S source
  let q := fkRectHorizontalCylinderUnexploredLiftPoint R rho S target
  have hpRow : p.2 = 0 := by
    dsimp [p]
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val]
    rw [hsource]
    simp [fkRectBottomRow]
  have hqRow : q.2 = (R.height : Int) - 1 := by
    dsimp [q]
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val]
    rw [htarget]
    have hh := R.height_pos
    simp [fkRectTopRow]
    omega
  obtain ⟨k, hk⟩ := R.height_even
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderUnexploredLiftSite,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectSquareDevelopPoint, p, q, hpRow, hqRow, hk] <;>
    omega



theorem FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness_embedding_sub
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (sourceX targetX : Fin R.width)
    (hsource : source.1 = (sourceX, fkRectBottomRow R))
    (htarget : target.1 = (targetX, fkRectTopRow R)) :
    let dx :=
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 -
        (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1
    ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R rho pair S hS hW).embedding target).1 -
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R rho pair S hS hW).embedding source).1 =
      fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
  exact fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub
    R rho S source target sourceX targetX hsource htarget



theorem fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub
    (R : FKRectTorus) (dx : Int) :
    (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 0 -
        (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 1 =
      (R.height : Int) - 1 := by
  obtain ⟨k, hk⟩ := R.height_even
  simp [fkRectHorizontalCylinderSquareLiftedDisplacement, hk]
  omega




theorem fkRectHorizontalCylinder_oldDisplacement_parameter_eq
    (R : FKRectTorus) (rawDx oldDx : Int)
    (hbad : fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height =
      fkRectHorizontalCylinderLiftedDisplacement oldDx R.height) :
    oldDx = 2 * ((R.height : Int) - 1) := by
  have hcoord :=
    fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub R rawDx
  rw [hbad] at hcoord
  have hzero := congrFun hbad 0
  have hone := congrFun hbad 1
  simp [fkRectHorizontalCylinderSquareLiftedDisplacement,
    fkRectHorizontalCylinderLiftedDisplacement] at hzero hone hcoord
  omega




theorem fkRectHorizontalCylinder_not_oldDisplacement_of_width_lt
    (R : FKRectTorus) (rawDx : Int)
    (htall : R.width < 2 * (R.height - 1)) :
    ¬ (∃ oldDx : Int,
      fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height =
          fkRectHorizontalCylinderLiftedDisplacement oldDx R.height ∧
        oldDx.natAbs <= R.width) := by
  rintro ⟨oldDx, hbad, hbound⟩
  have hold := fkRectHorizontalCylinder_oldDisplacement_parameter_eq
    R rawDx oldDx hbad
  have hheight : 0 <= (R.height : Int) - 1 := by
    have hh := R.height_pos
    omega
  have habs : oldDx.natAbs = 2 * (R.height - 1) := by
    rw [hold]
    have hnonneg : 0 <= 2 * ((R.height : Int) - 1) := by positivity
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hnonneg]
    push_cast
    omega
  rw [habs] at hbound
  omega



def fkRectHorizontalCylinderFixedEndpointDisplacement
    (height : Nat) : Site 2 :=
  fkRectHorizontalCylinderSquareLiftedDisplacement 0 height



def fkRectHorizontalCylinderReflectedDiagonalDisplacement
    (height : Nat) : Site 2 :=
  ![(height / 2 : Nat), -(height / 2 : Nat)]

theorem fkRectHorizontalCylinder_fixedEndpoint_sub_reflectedDiagonal
    (R : FKRectTorus) :
    fkRectHorizontalCylinderFixedEndpointDisplacement R.height -
        fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height =
      ![0, 1] := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderFixedEndpointDisplacement,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectHorizontalCylinderReflectedDiagonalDisplacement]



def fkRectHorizontalCylinderFixedEndpointCorrection : Site 2 :=
  ![0, -1]

theorem fkRectHorizontalCylinder_fixedEndpoint_add_correction
    (R : FKRectTorus) :
    fkRectHorizontalCylinderFixedEndpointDisplacement R.height +
        fkRectHorizontalCylinderFixedEndpointCorrection =
      fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderFixedEndpointDisplacement,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectHorizontalCylinderFixedEndpointCorrection,
      fkRectHorizontalCylinderReflectedDiagonalDisplacement]



theorem fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact
    {q : Real} (hq : 4 < q) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderReflectedDiagonalDisplacement height) =
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (height / 2) := by
  let S := fkQgt4CoordinateSignBoxSym fun i : Fin 2 => i = 1
  have hsym := fkQgt4CriticalFreeTwoPoint_boxSym hq S
    (fkRectHorizontalCylinderReflectedDiagonalDisplacement height)
  have hmap : S.τ
      (fkRectHorizontalCylinderReflectedDiagonalDisplacement height) =
        fkQgt4ExactDiagonalSite (height / 2) := by
    funext i
    fin_cases i <;>
      simp [S, fkQgt4CoordinateSignBoxSym,
        fkRectHorizontalCylinderReflectedDiagonalDisplacement,
        fkQgt4ExactDiagonalSite]
  rw [hmap] at hsym
  simpa [fkQgt4CriticalFreeTwoPoint,
    fkQgt4CriticalFreeExactDiagonalTwoPoint] using hsym.symm




theorem fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact
    {q : Real} (hq : 4 < q) (R : FKRectTorus) :
    fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) *
        fkQgt4CriticalFreeTwoPoint hq
          fkRectHorizontalCylinderFixedEndpointCorrection <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) := by
  have hmul := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq
    (fkRectHorizontalCylinderFixedEndpointDisplacement R.height)
    fkRectHorizontalCylinderFixedEndpointCorrection
  rw [fkRectHorizontalCylinder_fixedEndpoint_add_correction R] at hmul
  rwa [fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact hq R.height]
    at hmul


theorem fkQgt4CriticalFreeTwoPoint_fixedEndpoint_le_exact_div
    {q : Real} (hq : 4 < q) (R : FKRectTorus) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) /
        fkQgt4CriticalFreeTwoPoint hq
          fkRectHorizontalCylinderFixedEndpointCorrection := by
  rw [le_div_iff₀ (fkQgt4CriticalFreeTwoPoint_pos hq
    fkRectHorizontalCylinderFixedEndpointCorrection)]
  exact fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact
    hq R




theorem fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub
    {q : Real} (hq : 4 < q) (x : Site 2) (n : Nat)
    (hcoord : x 0 - x 1 = (n : Int)) :
    fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
  let swap := FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)
  let neg := fkQgt4CoordinateSignBoxSym fun _ : Fin 2 => true
  let y := neg.τ (swap.τ x)
  have hswap : fkQgt4CriticalFreeTwoPoint hq (swap.τ x) =
      fkQgt4CriticalFreeTwoPoint hq x :=
    fkQgt4CriticalFreeTwoPoint_boxSym hq swap x
  have hneg : fkQgt4CriticalFreeTwoPoint hq y =
      fkQgt4CriticalFreeTwoPoint hq (swap.τ x) := by
    exact fkQgt4CriticalFreeTwoPoint_boxSym hq neg (swap.τ x)
  have hy0 : y 0 = -(x 1) := by
    simp [y, neg, swap, fkQgt4CoordinateSignBoxSym,
      FK.rot_permBoxSym, FK.rot_permEquiv]
  have hy1 : y 1 = -(x 0) := by
    simp [y, neg, swap, fkQgt4CoordinateSignBoxSym,
      FK.rot_permBoxSym, FK.rot_permEquiv]
  have hadd : x + y =
      fkRectHorizontalCylinderReflectedDiagonalDisplacement (2 * n) := by
    funext i
    fin_cases i <;>
      simp [fkRectHorizontalCylinderReflectedDiagonalDisplacement,
        hy0, hy1] <;>
      omega
  have hmul := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq x y
  rw [hneg, hswap, hadd,
    fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact hq (2 * n)] at hmul
  simpa [pow_two] using hmul



theorem fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact
    {q : Real} (hq : 4 < q) (R : FKRectTorus) (rawDx : Int) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height) <=
      Real.sqrt
        (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) := by
  let x := fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height
  have hheight : 1 <= R.height := by
    have hh := R.height_gt_two
    omega
  have hsq := fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub
    hq x (R.height - 1) (by
      dsimp [x]
      rw [fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub]
      rw [Nat.cast_sub hheight]
      norm_num)
  have hx : 0 <= fkQgt4CriticalFreeTwoPoint hq x :=
    (fkQgt4CriticalFreeTwoPoint_pos hq x).le
  have hdiag : 0 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1) :=
    (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq (R.height - 1)).le
  have hsqrt := Real.sqrt_nonneg
    (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1))
  change fkQgt4CriticalFreeTwoPoint hq x <= _
  nlinarith [Real.sq_sqrt hdiag]

end

end StatMech.FrontierD
