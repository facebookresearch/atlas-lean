/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonTurning










namespace StatMech.FrontierA




theorem kwAngleTurnPhase_mul_of_sign_or_outer
    (a b c : Real.Angle)
    (hab : b - a ≠ (Real.pi : Real.Angle))
    (hbc : c - b ≠ (Real.pi : Real.Angle))
    (hsign : (b - a).sign ≠ (c - b).sign ∨
      (b - a).sign = (c - a).sign) :
    kwAngleTurnPhase a b * kwAngleTurnPhase b c =
      kwAngleTurnPhase a c := by
  unfold kwAngleTurnPhase
  rw [← Complex.exp_add]
  congr 1
  have hangle : (b - a) + (c - b) = c - a := by abel
  have hlift := Real.Angle.toReal_add_eq_toReal_add_toReal
    hab hbc (by simpa only [hangle] using hsign)
  rw [hangle] at hlift
  rw [hlift]
  push_cast
  ring





theorem kwAngleTurnPhase_mul_eq_neg_of_wrap
    (a b c : Real.Angle)
    (hab : b - a ≠ (Real.pi : Real.Angle))
    (hbc : c - b ≠ (Real.pi : Real.Angle))
    (hac : c - a ≠ (Real.pi : Real.Angle))
    (hsame : (b - a).sign = (c - b).sign)
    (hwrap : (b - a).sign ≠ (c - a).sign) :
    kwAngleTurnPhase a b * kwAngleTurnPhase b c =
      -kwAngleTurnPhase a c := by
  let theta : Real.Angle := b - a
  let psi : Real.Angle := c - b
  let phi : Real.Angle := c - a
  have hsum : theta + psi = phi := by
    dsimp only [theta, psi, phi]
    abel
  have hab' : theta ≠ (Real.pi : Real.Angle) := hab
  have hbc' : psi ≠ (Real.pi : Real.Angle) := hbc
  have hac' : phi ≠ (Real.pi : Real.Angle) := hac
  have hsame' : theta.sign = psi.sign := hsame
  have hwrap' : theta.sign ≠ phi.sign := hwrap
  have habs := Real.Angle.abs_toReal_add_eq_two_pi_sub_abs_toReal_add_abs_toReal
    hsame' (by simpa only [hsum] using hwrap')
  rw [hsum] at habs
  have hdiff :
      theta.toReal + psi.toReal - phi.toReal = 2 * Real.pi ∨
        theta.toReal + psi.toReal - phi.toReal = -(2 * Real.pi) := by
    rcases theta.sign.trichotomy with hneg | hzero | hpos
    · right
      have hpsiNeg : psi.sign = -1 := hsame'.symm ▸ hneg
      have hthetaReal : theta.toReal < 0 := by
        rwa [Real.Angle.toReal_neg_iff_sign_neg]
      have hpsiReal : psi.toReal < 0 := by
        rwa [Real.Angle.toReal_neg_iff_sign_neg]
      rcases phi.sign.trichotomy with hphiNeg | hphiZero | hphiPos
      · exact (hwrap' (hneg.trans hphiNeg.symm)).elim
      · rw [Real.Angle.sign_eq_zero_iff] at hphiZero
        rcases hphiZero with hphi | hphi
        · rw [hphi, Real.Angle.toReal_zero, abs_zero] at habs
          have hthetaLower := Real.Angle.neg_pi_lt_toReal theta
          have hpsiLower := Real.Angle.neg_pi_lt_toReal psi
          rw [abs_of_neg hthetaReal, abs_of_neg hpsiReal] at habs
          nlinarith [Real.pi_pos]
        · exact (hac' hphi).elim
      · have hphiReal : 0 < phi.toReal := by
          rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos] at hphiPos
          exact hphiPos.1
        rw [abs_of_neg hthetaReal, abs_of_neg hpsiReal,
          abs_of_pos hphiReal] at habs
        linarith
    · have hpsiZero : psi.sign = 0 := hsame'.symm.trans hzero
      rw [Real.Angle.sign_eq_zero_iff] at hzero
      rcases hzero with htheta | htheta
      · rw [Real.Angle.sign_eq_zero_iff] at hpsiZero
        rcases hpsiZero with hpsi | hpsi
        · apply (hwrap' ?_).elim
          rw [← hsum, htheta, hpsi]
          simp
        · exact (hbc' hpsi).elim
      · exact (hab' htheta).elim
    · left
      have hpsiPos : psi.sign = 1 := hsame'.symm ▸ hpos
      have hthetaReal : 0 < theta.toReal := by
        rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos] at hpos
        exact hpos.1
      have hpsiReal : 0 < psi.toReal := by
        rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos] at hpsiPos
        exact hpsiPos.1
      rcases phi.sign.trichotomy with hphiNeg | hphiZero | hphiPos
      · have hphiReal : phi.toReal < 0 := by
          rwa [Real.Angle.toReal_neg_iff_sign_neg]
        rw [abs_of_pos hthetaReal, abs_of_pos hpsiReal,
          abs_of_neg hphiReal] at habs
        linarith
      · rw [Real.Angle.sign_eq_zero_iff] at hphiZero
        rcases hphiZero with hphi | hphi
        · rw [hphi, Real.Angle.toReal_zero, abs_zero] at habs
          have hthetaUpper := Real.Angle.toReal_le_pi theta
          have hpsiUpper := Real.Angle.toReal_le_pi psi
          have hthetaNe : theta.toReal ≠ Real.pi := by
            intro heq
            apply hab'
            exact Real.Angle.toReal_injective (by simpa using heq)
          have hpsiNe : psi.toReal ≠ Real.pi := by
            intro heq
            apply hbc'
            exact Real.Angle.toReal_injective (by simpa using heq)
          have hthetaLt : theta.toReal < Real.pi :=
            lt_of_le_of_ne hthetaUpper hthetaNe
          have hpsiLt : psi.toReal < Real.pi :=
            lt_of_le_of_ne hpsiUpper hpsiNe
          rw [abs_of_pos hthetaReal, abs_of_pos hpsiReal] at habs
          nlinarith [Real.pi_pos]
        · exact (hac' hphi).elim
      · exact (hwrap' (hpos.trans hphiPos.symm)).elim
  unfold kwAngleTurnPhase
  rw [← Complex.exp_add]
  rcases hdiff with hdiff | hdiff
  · rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) =
        ((((c - a).toReal : ℂ) * Complex.I) / 2) +
          (Real.pi : ℂ) * Complex.I by
      have h := congrArg (fun r : Real => ((r : ℂ) * Complex.I) / 2) hdiff
      dsimp only [theta, psi, phi] at hdiff h
      push_cast at h
      linear_combination h]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) =
        ((((c - a).toReal : ℂ) * Complex.I) / 2) -
          (Real.pi : ℂ) * Complex.I by
      have h := congrArg (fun r : Real => ((r : ℂ) * Complex.I) / 2) hdiff
      dsimp only [theta, psi, phi] at hdiff h
      push_cast at h
      linear_combination h]
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num



theorem kwAngleTurnPhase_ear_splice_of_interiorSides
    (p a b q : ℂ)
    (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hq : q ≠ 0)
    (hpA : kwComplexCross p a ≠ 0)
    (hAB : kwComplexCross a b ≠ 0)
    (hBq : kwComplexCross b q ≠ 0)
    (hleft :
      (0 < kwComplexCross a b ∧ 0 < kwComplexCross p (a + b)) ∨
        (kwComplexCross a b < 0 ∧ kwComplexCross p (a + b) < 0))
    (hright :
      (0 < kwComplexCross a b ∧ 0 < kwComplexCross (a + b) q) ∨
        (kwComplexCross a b < 0 ∧ kwComplexCross (a + b) q < 0)) :
    kwAngleTurnPhase (Complex.arg p : Real.Angle)
          (Complex.arg a : Real.Angle) *
        kwAngleTurnPhase (Complex.arg a : Real.Angle)
          (Complex.arg b : Real.Angle) *
        kwAngleTurnPhase (Complex.arg b : Real.Angle)
          (Complex.arg q : Real.Angle) =
      kwAngleTurnPhase (Complex.arg p : Real.Angle)
          (Complex.arg (a + b) : Real.Angle) *
        kwAngleTurnPhase (Complex.arg (a + b) : Real.Angle)
          (Complex.arg q : Real.Angle) := by
  have hdiag : a + b ≠ 0 := by
    intro hzero
    have : b = -a := by linear_combination hzero
    apply hAB
    rw [this]
    simp [kwComplexCross]
    ring
  have haDiag : kwComplexCross a (a + b) = kwComplexCross a b := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hdiagB : kwComplexCross (a + b) b = kwComplexCross a b := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hleftSign :
      (((Complex.arg (a + b) : Real.Angle) -
          (Complex.arg a : Real.Angle)).sign =
        ((Complex.arg (a + b) : Real.Angle) -
          (Complex.arg p : Real.Angle)).sign) := by
    rcases hleft with h | h
    · exact (kw_angle_sub_sign_of_cross_pos ha hdiag
          (haDiag.symm ▸ h.1)).trans
        (kw_angle_sub_sign_of_cross_pos hp hdiag h.2).symm
    · exact (kw_angle_sub_sign_of_cross_neg ha hdiag
          (haDiag.symm ▸ h.1)).trans
        (kw_angle_sub_sign_of_cross_neg hp hdiag h.2).symm
  have hleftPhase :
      kwAngleTurnPhase (Complex.arg p : Real.Angle)
          (Complex.arg a : Real.Angle) *
        kwAngleTurnPhase (Complex.arg a : Real.Angle)
          (Complex.arg (a + b) : Real.Angle) =
      kwAngleTurnPhase (Complex.arg p : Real.Angle)
        (Complex.arg (a + b) : Real.Angle) := by
    apply kwAngleTurnPhase_mul_of_sign_or_outer
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hp ha hpA
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero ha hdiag
        (haDiag.symm ▸ hAB)
    · by_cases hsame :
          ((Complex.arg a : Real.Angle) -
              (Complex.arg p : Real.Angle)).sign =
            ((Complex.arg (a + b) : Real.Angle) -
              (Complex.arg a : Real.Angle)).sign
      · exact Or.inr (hsame.trans hleftSign)
      · exact Or.inl hsame
  have hrightPhase :
      kwAngleTurnPhase (Complex.arg (a + b) : Real.Angle)
          (Complex.arg b : Real.Angle) *
        kwAngleTurnPhase (Complex.arg b : Real.Angle)
          (Complex.arg q : Real.Angle) =
      kwAngleTurnPhase (Complex.arg (a + b) : Real.Angle)
        (Complex.arg q : Real.Angle) := by
    apply kwAngleTurnPhase_mul_of_sign_or_outer
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hdiag hb
        (hdiagB.symm ▸ hAB)
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hb hq hBq
    · right
      rcases hright with h | h
      · exact (kw_angle_sub_sign_of_cross_pos hdiag hb
            (hdiagB.symm ▸ h.1)).trans
          (kw_angle_sub_sign_of_cross_pos hdiag hq h.2).symm
      · exact (kw_angle_sub_sign_of_cross_neg hdiag hb
            (hdiagB.symm ▸ h.1)).trans
          (kw_angle_sub_sign_of_cross_neg hdiag hq h.2).symm
  have hmiddlePhase := kwAngleTurnPhase_vector_sum ha hb hAB
  rw [← hleftPhase, ← hrightPhase, ← hmiddlePhase]
  ring

end StatMech.FrontierA
