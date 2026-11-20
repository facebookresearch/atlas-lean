/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzFourPoint
import Code.Ising.LebowitzPfisterFourBridgeActual









namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem fourBridgeOneCoeff_zeroField_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (w x y z : V) :
    fourBridgeOneCoeff G J (fun _ => 0) w x y z = 0 := by
  unfold fourBridgeOneCoeff
  rw [FrontierA.expJ_zero_spin_eq_zero,
    FrontierA.expJ_zero_spin_eq_zero,
    FrontierA.expJ_zero_spin_eq_zero,
    FrontierA.expJ_zero_spin_eq_zero]
  ring



theorem fourBridgeThreeCoeff_zeroField_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (w x y z : V)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeThreeCoeff G J (fun _ => 0) w x y z = 0 := by
  unfold fourBridgeThreeCoeff
  rw [expJ_zero_three_spin_eq_zero G.edgeFinset J w x y hwx hwy hxy,
    expJ_zero_three_spin_eq_zero G.edgeFinset J w x z hwx hwz hxz,
    expJ_zero_three_spin_eq_zero G.edgeFinset J w y z hwy hwz hyz,
    expJ_zero_three_spin_eq_zero G.edgeFinset J x y z hxy hxz hyz]
  ring


theorem fourBridgeRankMass_rankCross_zeroField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (w x y z : V)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z
    let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z
    let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z
    let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z
    fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 =
      fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4 := by
  dsimp only
  rw [fourBridgeOneCoeff_zeroField_eq_zero G J w x y z,
    fourBridgeThreeCoeff_zeroField_eq_zero G J w x y z
      hwx hwy hwz hxy hxz hyz]
  simp only [fourBridgeRankMass]
  ring



theorem fourBridgeVarianceSkewBernsteinCoeff_five_six_zeroField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (w x y z : V)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z
    let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z
    let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z
    let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z
    fourBridgeVarianceSkewBernsteinCoeff a b c d 5 = 0 /\
      fourBridgeVarianceSkewBernsteinCoeff a b c d 6 = 0 := by
  dsimp only
  rw [fourBridgeOneCoeff_zeroField_eq_zero G J w x y z,
    fourBridgeThreeCoeff_zeroField_eq_zero G J w x y z
      hwx hwy hwz hxy hxz hyz]
  simp [fourBridgeVarianceSkewBernsteinCoeff]




theorem fourBridgeVarianceSkewBernsteinCoeff_all_zeroField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (w x y z : V)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z
    let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z
    let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z
    let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z
    ∀ i : Fin 7, fourBridgeVarianceSkewBernsteinCoeff a b c d i = 0 := by
  dsimp only
  rw [fourBridgeOneCoeff_zeroField_eq_zero G J w x y z,
    fourBridgeThreeCoeff_zeroField_eq_zero G J w x y z
      hwx hwy hwz hxy hxz hyz]
  intro i
  fin_cases i <;> simp [fourBridgeVarianceSkewBernsteinCoeff]

end

end StatMech.Ising
