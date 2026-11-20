/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterLowFaceAssembly
import Code.Ising.LebowitzPfisterFourBridgeMarginalRank











namespace StatMech.Ising

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcoeffOne : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 1 <= 0)
    (hcoeffTwo : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2 <= 0)
    (hcoeffThree : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 3 <= 0)
    (hcoeffFour : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 4 <= 0) :
    forall i, fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
  intro i
  have hzero := LowFaceCertificate.fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hend := fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  fin_cases i
  · exact hzero
  · exact hcoeffOne
  · exact hcoeffTwo
  · exact hcoeffThree
  · exact hcoeffFour
  · exact hend.1
  · exact hend.2



theorem replicaBridgeVariance_fourBridgeSites_le_neg_of_middle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmiddle : forall i : Fin 7, 1 <= i.val -> i.val <= 4 ->
      fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) i <= 0)
    (r : Real) (hr : 0 <= r) :
    replicaBridgeVariance G J hf (fourBridgeSites w x y z) r <=
      replicaBridgeVariance G J hf (fourBridgeSites w x y z) (-r) := by
  by_cases hre : r = 0
  · simp [hre]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hre)
  apply (replicaBridgeVariance_fourBridgeSites_le_neg_iff_skew
    G J hf w x y z hrp).2
  apply fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le
  · exact (Real.tanh_lt_one r).le
  · apply fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
    · exact hmiddle 1 (by norm_num) (by norm_num)
    · exact hmiddle 2 (by norm_num) (by norm_num)
    · exact hmiddle 3 (by norm_num) (by norm_num)
    · exact hmiddle 4 (by norm_num) (by norm_num)



theorem replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmiddle : forall i : Fin 7, 1 <= i.val -> i.val <= 4 ->
      fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) i <= 0)
    (r : Real) (hr : 0 <= r) :
    replicaBridgeFreeEnergy G J hf (fourBridgeSites w x y z) r <=
      2 * r * fourBridgeOneCoeff G J hf w x y z := by
  have h := replicaBridgeFreeEnergy_le_of_variance_order G J hf
    (fourBridgeSites w x y z) r hr (fun t ht =>
      replicaBridgeVariance_fourBridgeSites_le_neg_of_middle
        G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle t ht)
  simpa [fourBridgeSites, fourBridgeOneCoeff, Fin.sum_univ_succ,
    add_assoc] using h

end

end StatMech.Ising
