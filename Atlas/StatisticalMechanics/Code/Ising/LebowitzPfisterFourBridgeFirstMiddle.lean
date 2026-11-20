/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeReduction



namespace StatMech.Ising

noncomputable section



theorem fourBridge_bernsteinOne_nonpos_of_oneCoeff_le_two
    {a b c d : Real}
    (ha0 : 0 <= a) (hb0 : 0 <= b) (hc0 : 0 <= c) (hd0 : 0 <= d)
    (ha2 : a <= 2)
    (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
    (hdis : 0 <= 1 - a + b - c + d) :
    fourBridgeVarianceSkewBernsteinCoeff a b c d 1 <= 0 := by
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  let N := 3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
    5 * a * d - 3 * a + b * c + 6 * c
  change N / 3 <= 0
  by_cases ha1 : a <= 1
  · have haSq : a ^ 2 <= 1 := by nlinarith
    have hlast : 2 * a ^ 2 - 5 * b - 3 <= 0 := by nlinarith
    have htrip : a * (a - 1) * (a + 1) <= 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith)) (by linarith)
    have hprod : 0 <=
        a * (a - 1) * (a + 1) * (2 * a ^ 2 - 5 * b - 3) :=
      mul_nonneg_of_nonpos_of_nonpos htrip hlast
    have hfactor : 0 <= 2 * a ^ 2 + b + 6 := by positivity
    have hmul := mul_nonpos_of_nonneg_of_nonpos hfactor hzero
    have hdrop : N <=
        3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
          3 * a + b * c + 6 * c := by
      dsimp [N]
      nlinarith [mul_nonneg ha0 hd0]
    have hid :
        3 * (3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
          3 * a + b * c + 6 * c) =
        (2 * a ^ 2 + b + 6) *
            (a ^ 3 - 3 * a * b - a + 3 * c) -
          a * (a - 1) * (a + 1) * (2 * a ^ 2 - 5 * b - 3) := by
      ring
    have hN : N <= 0 := by nlinarith [hid]
    exact div_nonpos_of_nonpos_of_nonneg hN (by norm_num)
  · have ha1' : 1 <= a := le_of_not_ge ha1
    have haPos : 0 < a := by linarith
    have hbase : a * (a ^ 2 - 3 * b - 1) <= 0 := by
      nlinarith
    have hbLower : a ^ 2 - 1 <= 3 * b := by
      have := nonpos_of_mul_nonpos_right hbase haPos
      nlinarith
    have haSq : a ^ 2 <= 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (by linarith : 0 <= 2 + a)]
    have hlast : 2 * a ^ 2 + a - 5 * b - 6 <= 0 := by
      nlinarith
    have hfactor : 0 <= 2 * a ^ 2 - 5 * a + b + 6 := by
      nlinarith [sq_nonneg (4 * a - 5)]
    have hdLower : a - b + c - 1 <= d := by linarith
    have hdrop : N <=
        3 * a ^ 3 + 2 * a ^ 2 * c - 5 * a ^ 2 - a * b ^ 2 -
          3 * a * b - 5 * a * c + 2 * a + b * c + 6 * c := by
      dsimp [N]
      have hmul := mul_le_mul_of_nonpos_left hdLower (by nlinarith : -5 * a <= 0)
      nlinarith
    have htrip : a * (a - 2) * (a - 1) <= 0 := by
      have hfirst : 0 <= a * (a - 1) :=
        mul_nonneg ha0 (sub_nonneg.mpr ha1')
      have hlast' : a - 2 <= 0 := sub_nonpos.mpr ha2
      rw [show a * (a - 2) * (a - 1) = a * (a - 1) * (a - 2) by ring]
      exact mul_nonpos_of_nonneg_of_nonpos hfirst hlast'
    have hprod : 0 <=
        a * (a - 2) * (a - 1) * (2 * a ^ 2 + a - 5 * b - 6) :=
      mul_nonneg_of_nonpos_of_nonpos htrip hlast
    have hmul := mul_nonpos_of_nonneg_of_nonpos hfactor hzero
    have hid :
        3 * (3 * a ^ 3 + 2 * a ^ 2 * c - 5 * a ^ 2 - a * b ^ 2 -
          3 * a * b - 5 * a * c + 2 * a + b * c + 6 * c) =
        (2 * a ^ 2 - 5 * a + b + 6) *
            (a ^ 3 - 3 * a * b - a + 3 * c) -
          a * (a - 2) * (a - 1) *
            (2 * a ^ 2 + a - 5 * b - 6) := by
      ring
    have hN : N <= 0 := by nlinarith [hid]
    exact div_nonpos_of_nonpos_of_nonneg hN (by norm_num)



theorem fourBridge_bernsteinOne_nonpos_of_two_le_oneCoeff
    {a b c d : Real} (ha2 : 2 <= a)
    (hp0 : 0 <= fourBridgeRankMass a b c d 0)
    (hp1 : 0 <= fourBridgeRankMass a b c d 1)
    (hp2 : 0 <= fourBridgeRankMass a b c d 2) :
    fourBridgeVarianceSkewBernsteinCoeff a b c d 1 <= 0 := by
  let p0 := fourBridgeRankMass a b c d 0
  let p1 := fourBridgeRankMass a b c d 1
  let p2 := fourBridgeRankMass a b c d 2
  let Q :=
    (72 * a - 48) * p0 ^ 2 +
      (14 * a ^ 2 - 22 * a + 24 + 72 * (a - 1) * p1 +
        (24 * a - 32) * p2) * p0 +
      (18 * a - 24) * p1 ^ 2 +
      (5 * a ^ 2 - 14 * a + 12 + (12 * a - 20) * p2) * p1 +
      (2 * a - 4) * p2 ^ 2 + (a - 2) ^ 2 * p2
  have hp0' : 0 <= p0 := hp0
  have hp1' : 0 <= p1 := hp1
  have hp2' : 0 <= p2 := hp2
  have h00 : 0 <= 72 * a - 48 := by nlinarith
  have h01 : 0 <= 14 * a ^ 2 - 22 * a + 24 := by
    nlinarith [sq_nonneg (14 * a - 11)]
  have h02 : 0 <= 72 * (a - 1) := by nlinarith
  have h03 : 0 <= 24 * a - 32 := by nlinarith
  have h10 : 0 <= 18 * a - 24 := by nlinarith
  have h11 : 0 <= 5 * a ^ 2 - 14 * a + 12 := by
    nlinarith [sq_nonneg (5 * a - 7)]
  have h12 : 0 <= 12 * a - 20 := by nlinarith
  have h20 : 0 <= 2 * a - 4 := by nlinarith
  have hQ : 0 <= Q := by
    dsimp [Q]
    positivity
  have hid :
      3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
          5 * a * d - 3 * a + b * c + 6 * c =
        -8 * Q := by
    dsimp [Q, p0, p1, p2]
    simp only [fourBridgeRankMass]
    ring
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  rw [show
      3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
          5 * a * d - 3 * a + b * c + 6 * c = -8 * Q from hid]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hQ) (by norm_num)


theorem fourBridgeAgreementSpinMass_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) (s : Real) :
    0 <= fourBridgeAgreementSpinMass G J hf w x y z s := by
  unfold fourBridgeAgreementSpinMass
  apply Finset.sum_nonneg
  intro q _
  exact ghsiAgreementProb_nonneg G J hf q

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_of_oneCoeff_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hone : fourBridgeOneCoeff G J hf w x y z <= 2) :
    fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 1 <= 0 := by
  apply fourBridge_bernsteinOne_nonpos_of_oneCoeff_le_two
  · dsimp [fourBridgeOneCoeff]
    positivity
  · dsimp [fourBridgeTwoCoeff]
    positivity
  · dsimp [fourBridgeThreeCoeff]
    positivity
  · dsimp [fourBridgeFourCoeff]
    positivity
  · exact hone
  · exact LowFaceCertificate.fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact fourBridge_allDisagreementCoefficient_nonneg G J hf w x y z



theorem fourBridgeVarianceSkewBernsteinCoeff_one_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 1 <= 0 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  rcases le_total a 2 with ha2 | h2a
  · exact fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_of_oneCoeff_le_two
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz ha2
  · apply fourBridge_bernsteinOne_nonpos_of_two_le_oneCoeff h2a
    · have hdis := fourBridge_allDisagreementCoefficient_nonneg
        G J hf w x y z
      dsimp [a, b, c, d]
      simp only [fourBridgeRankMass]
      positivity
    · rw [← fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one]
      exact fourBridgeAgreementSpinMass_nonneg G J hf w x y z (-2)
    · exact fourBridgeRankMass_two_nonneg G J hf w x y z



theorem fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_two_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 ->
      fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) i <= 0) :
    forall i, fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
  apply fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact fourBridgeVarianceSkewBernsteinCoeff_one_nonpos
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact hmiddle 2 (by norm_num) (by norm_num)
  · exact hmiddle 3 (by norm_num) (by norm_num)
  · exact hmiddle 4 (by norm_num) (by norm_num)



theorem replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_two_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 ->
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
  · exact fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_two_four
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle



theorem replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle_two_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 ->
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
      replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_two_four
        G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle t ht)
  simpa [fourBridgeSites, fourBridgeOneCoeff, Fin.sum_univ_succ,
    add_assoc] using h

end

end StatMech.Ising
