/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardCycleCoefficient











open scoped BigOperators

namespace StatMech.FrontierA


noncomputable def kwAngleTurnPhase (a b : Real.Angle) : ℂ :=
  Complex.exp ((((b - a).toReal : ℂ) * Complex.I) / 2)



theorem kw_principalTurnLift_add (a b c : Real.Angle)
    (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
    (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
    (c - a).toReal = (b - a).toReal + (c - b).toReal := by
  have hangle : c - a = (b - a) + (c - b) := by abel
  rw [hangle]
  have hcoe :
      (((b - a).toReal + (c - b).toReal : ℝ) : Real.Angle) =
        (b - a) + (c - b) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal,
      Real.Angle.coe_toReal]
  rw [← hcoe, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlower, hupper⟩]



theorem kwAngleTurnPhase_mul (a b c : Real.Angle)
    (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
    (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
    kwAngleTurnPhase a b * kwAngleTurnPhase b c =
      kwAngleTurnPhase a c := by
  unfold kwAngleTurnPhase
  rw [← Complex.exp_add]
  congr 1
  rw [kw_principalTurnLift_add a b c hlower hupper]
  push_cast
  ring






theorem kwAngleTurnPhase_ear_splice
    (previous incoming diagonal outgoing next : Real.Angle)
    (hleftLower : -Real.pi <
      (incoming - previous).toReal + (diagonal - incoming).toReal)
    (hleftUpper :
      (incoming - previous).toReal + (diagonal - incoming).toReal ≤ Real.pi)
    (hmiddleLower : -Real.pi <
      (diagonal - incoming).toReal + (outgoing - diagonal).toReal)
    (hmiddleUpper :
      (diagonal - incoming).toReal + (outgoing - diagonal).toReal ≤ Real.pi)
    (hrightLower : -Real.pi <
      (outgoing - diagonal).toReal + (next - outgoing).toReal)
    (hrightUpper :
      (outgoing - diagonal).toReal + (next - outgoing).toReal ≤ Real.pi) :
    kwAngleTurnPhase previous incoming *
          kwAngleTurnPhase incoming outgoing *
          kwAngleTurnPhase outgoing next =
      kwAngleTurnPhase previous diagonal * kwAngleTurnPhase diagonal next := by
  rw [← kwAngleTurnPhase_mul previous incoming diagonal
      hleftLower hleftUpper,
    ← kwAngleTurnPhase_mul diagonal outgoing next
      hrightLower hrightUpper,
    ← kwAngleTurnPhase_mul incoming diagonal outgoing
      hmiddleLower hmiddleUpper]
  ring



theorem kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi
    (a b c : Real.Angle)
    (hsign :
      (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧
          0 < (a - c).toReal) ∨
        ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧
          (a - c).toReal < 0)) :
    (b - a).toReal + (c - b).toReal + (a - c).toReal =
        2 * Real.pi ∨
      (b - a).toReal + (c - b).toReal + (a - c).toReal =
        -(2 * Real.pi) := by
  let s : ℝ := (b - a).toReal + (c - b).toReal + (a - c).toReal
  have hcoe : (s : Real.Angle) = 0 := by
    simp only [s, Real.Angle.coe_add, Real.Angle.coe_toReal]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  have hk' : (k : ℝ) * (2 * Real.pi) = s := by
    simpa [zsmul_eq_mul] using hk
  have hs_lower : -(3 * Real.pi) < s := by
    dsimp only [s]
    nlinarith [Real.Angle.neg_pi_lt_toReal (b - a),
      Real.Angle.neg_pi_lt_toReal (c - b),
      Real.Angle.neg_pi_lt_toReal (a - c)]
  have hs_upper : s ≤ 3 * Real.pi := by
    dsimp only [s]
    nlinarith [Real.Angle.toReal_le_pi (b - a),
      Real.Angle.toReal_le_pi (c - b),
      Real.Angle.toReal_le_pi (a - c)]
  have hk_lower : (-1 : ℤ) ≤ k := by
    by_contra h
    have hk2 : k ≤ -2 := by omega
    have hk2' : (k : ℝ) ≤ -2 := by exact_mod_cast hk2
    nlinarith [Real.pi_pos]
  have hk_upper : k ≤ (1 : ℤ) := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith [Real.pi_pos]
  rcases hsign with hpos | hneg
  · left
    change s = 2 * Real.pi
    have hs_pos : 0 < s := by dsimp only [s]; nlinarith
    have hk_pos : 0 < k := by
      by_contra h
      have hk_nonpos : k ≤ 0 := by omega
      have hk_nonpos' : (k : ℝ) ≤ 0 := by exact_mod_cast hk_nonpos
      nlinarith [Real.pi_pos]
    have : k = 1 := by omega
    rw [← hk', this]
    norm_num
  · right
    change s = -(2 * Real.pi)
    have hs_neg : s < 0 := by dsimp only [s]; nlinarith
    have hk_neg : k < 0 := by
      by_contra h
      have hk_nonneg : 0 ≤ k := by omega
      have hk_nonneg' : (0 : ℝ) ≤ k := by exact_mod_cast hk_nonneg
      nlinarith [Real.pi_pos]
    have : k = -1 := by omega
    rw [← hk', this]
    norm_num



theorem kw_three_principal_halfAngle_product_eq_neg_one
    (a b c : Real.Angle)
    (hsign :
      (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧
          0 < (a - c).toReal) ∨
        ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧
          (a - c).toReal < 0)) :
    Complex.exp ((((b - a).toReal : ℂ) * Complex.I) / 2) *
        Complex.exp ((((c - b).toReal : ℂ) * Complex.I) / 2) *
        Complex.exp ((((a - c).toReal : ℂ) * Complex.I) / 2) = -1 := by
  rcases kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi
      a b c hsign with hsum | hsum
  · rw [← Complex.exp_add, ← Complex.exp_add]
    have hsum' := congrArg
      (fun r : ℝ ↦ ((r : ℂ) * Complex.I) / 2) hsum
    rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) +
          (((a - c).toReal : ℂ) * Complex.I) / 2 =
        (Real.pi : ℂ) * Complex.I by
      convert hsum' using 1 <;> push_cast <;> ring]
    rw [Complex.exp_pi_mul_I]
  · rw [← Complex.exp_add, ← Complex.exp_add]
    have hsum' := congrArg
      (fun r : ℝ ↦ ((r : ℂ) * Complex.I) / 2) hsum
    rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) +
          (((a - c).toReal : ℂ) * Complex.I) / 2 =
        -(Real.pi : ℂ) * Complex.I by
      convert hsum' using 1 <;> push_cast <;> ring]
    rw [show -(Real.pi : ℂ) * Complex.I =
      -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num


def kwComplexCross (x y : ℂ) : ℝ :=
  x.re * y.im - x.im * y.re

theorem kwComplexCross_cyclic_of_sum_zero
    {x y z : ℂ} (hsum : x + y + z = 0) :
    kwComplexCross x y = kwComplexCross y z ∧
      kwComplexCross y z = kwComplexCross z x := by
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.zero_re] at hre
  simp only [Complex.add_im, Complex.zero_im] at him
  constructor
  · unfold kwComplexCross
    linear_combination y.im * hre - y.re * him
  · unfold kwComplexCross
    linear_combination z.im * hre - z.re * him


theorem kw_collinear_of_cross_sub_eq_zero {A B C : ℂ}
    (hcross : kwComplexCross (B - A) (C - B) = 0) :
    Collinear ℝ ({A, B, C} : Set ℂ) := by
  by_cases hx : B - A = 0
  · have : B = A := sub_eq_zero.mp hx
    subst B
    simpa [Set.pair_comm] using collinear_pair ℝ A C
  let r : ℝ := ((C - B) / (B - A)).re
  have hnorm : 0 < Complex.normSq (B - A) :=
    Complex.normSq_pos.mpr hx
  have him : (((C - B) / (B - A))).im = 0 := by
    rw [Complex.div_im, ← sub_div]
    apply div_eq_zero_iff.mpr
    left
    simpa only [kwComplexCross, mul_comm] using hcross
  have hquot : (C - B) / (B - A) = (r : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [him]
  have hy : C - B = (r : ℂ) * (B - A) := by
    calc
      C - B = ((C - B) / (B - A)) * (B - A) :=
        (div_mul_cancel₀ _ hx).symm
      _ = (r : ℂ) * (B - A) := by rw [hquot]
  rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set ℂ) by simp)]
  refine ⟨B - A, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp
  · subst p
    exact ⟨0, by simp⟩
  · subst p
    exact ⟨1, by simp⟩
  · refine ⟨1 + r, ?_⟩
    rw [hp]
    change C = ((1 + r : ℝ) : ℂ) * (B - A) + A
    push_cast
    rw [add_mul, one_mul, ← hy]
    ring

theorem kw_arg_div_pos_of_cross_pos {x y : ℂ}
    (hx : x ≠ 0) (hxy : 0 < kwComplexCross x y) :
    0 < Complex.arg (y / x) := by
  have hnorm : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
  have him : 0 < (y / x).im := by
    rw [Complex.div_im]
    rw [← sub_div]
    apply div_pos _ hnorm
    simpa only [kwComplexCross, mul_comm] using hxy
  have hnonneg : 0 ≤ Complex.arg (y / x) :=
    Complex.arg_nonneg_iff.mpr him.le
  refine hnonneg.lt_of_ne ?_
  intro hzero
  have := Complex.arg_eq_zero_iff.mp hzero.symm
  exact him.ne' this.2

theorem kw_arg_div_neg_of_cross_neg {x y : ℂ}
    (hx : x ≠ 0) (hxy : kwComplexCross x y < 0) :
    Complex.arg (y / x) < 0 := by
  apply Complex.arg_neg_iff.mpr
  have hnorm : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
  rw [Complex.div_im]
  rw [← sub_div]
  apply div_neg_of_neg_of_pos _ hnorm
  simpa only [kwComplexCross, mul_comm] using hxy

theorem kw_angle_sub_toReal_eq_arg_div {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ((Complex.arg y : Real.Angle) -
        (Complex.arg x : Real.Angle)).toReal =
      Complex.arg (y / x) := by
  rw [← Complex.arg_div_coe_angle hy hx,
    Complex.arg_coe_angle_toReal_eq_arg]

theorem kw_angle_sub_ne_pi_of_cross_ne_zero {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hcross : kwComplexCross x y ≠ 0) :
    (Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle) ≠
      (Real.pi : Real.Angle) := by
  intro hpi
  have harg : Complex.arg (y / x) = Real.pi := by
    rw [← kw_angle_sub_toReal_eq_arg_div hx hy,
      hpi, Real.Angle.toReal_pi]
  have himzero : (y / x).im = 0 :=
    (Complex.arg_eq_pi_iff.mp harg).2
  rw [Complex.div_im, ← sub_div] at himzero
  have hnum : y.im * x.re - y.re * x.im = 0 := by
    rcases div_eq_zero_iff.mp himzero with h | h
    · exact h
    · exact ((Complex.normSq_pos.mpr hx).ne' h).elim
  apply hcross
  simpa only [kwComplexCross, mul_comm] using hnum

theorem kw_angle_sub_sign_of_cross_pos {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hcross : 0 < kwComplexCross x y) :
    ((Complex.arg y : Real.Angle) -
      (Complex.arg x : Real.Angle)).sign = 1 := by
  have hcrossne : kwComplexCross x y ≠ 0 := ne_of_gt hcross
  rw [← Real.Angle.sign_toReal
    (kw_angle_sub_ne_pi_of_cross_ne_zero hx hy hcrossne),
    kw_angle_sub_toReal_eq_arg_div hx hy]
  exact sign_pos (kw_arg_div_pos_of_cross_pos hx hcross)

theorem kw_angle_sub_sign_of_cross_neg {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hcross : kwComplexCross x y < 0) :
    ((Complex.arg y : Real.Angle) -
      (Complex.arg x : Real.Angle)).sign = -1 := by
  rw [← Real.Angle.toReal_neg_iff_sign_neg,
    kw_angle_sub_toReal_eq_arg_div hx hy]
  exact kw_arg_div_neg_of_cross_neg hx hcross



theorem kwAngleTurnPhase_mul_of_outer_sign (a b c : Real.Angle)
    (hab : b - a ≠ (Real.pi : Real.Angle))
    (hbc : c - b ≠ (Real.pi : Real.Angle))
    (hsign : (b - a).sign = (c - a).sign) :
    kwAngleTurnPhase a b * kwAngleTurnPhase b c =
      kwAngleTurnPhase a c := by
  unfold kwAngleTurnPhase
  rw [← Complex.exp_add]
  congr 1
  have hangle : (b - a) + (c - b) = c - a := by abel
  have hsign' : (b - a).sign = ((b - a) + (c - b)).sign := by
    rw [hangle]
    exact hsign
  have hlift := Real.Angle.toReal_add_eq_toReal_add_toReal
    hab hbc (Or.inr hsign')
  rw [hangle] at hlift
  rw [hlift]
  push_cast
  ring




theorem kwAngleTurnPhase_vector_sum {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hcross : kwComplexCross x y ≠ 0) :
    kwAngleTurnPhase (Complex.arg x : Real.Angle)
          (Complex.arg (x + y) : Real.Angle) *
        kwAngleTurnPhase (Complex.arg (x + y) : Real.Angle)
          (Complex.arg y : Real.Angle) =
      kwAngleTurnPhase (Complex.arg x : Real.Angle)
        (Complex.arg y : Real.Angle) := by
  have hsum : x + y ≠ 0 := by
    intro hzero
    have : y = -x := by linear_combination hzero
    apply hcross
    rw [this]
    simp [kwComplexCross]
    ring
  have hcrossLeft : kwComplexCross x (x + y) = kwComplexCross x y := by
    simp only [kwComplexCross, Complex.add_re, Complex.add_im]
    ring
  have hcrossRight : kwComplexCross (x + y) y = kwComplexCross x y := by
    simp only [kwComplexCross, Complex.add_re, Complex.add_im]
    ring
  apply kwAngleTurnPhase_mul_of_outer_sign
  · exact kw_angle_sub_ne_pi_of_cross_ne_zero hx hsum
      (hcrossLeft.symm ▸ hcross)
  · exact kw_angle_sub_ne_pi_of_cross_ne_zero hsum hy
      (hcrossRight.symm ▸ hcross)
  · rcases lt_or_gt_of_ne hcross with hneg | hpos
    · have hleft :
          (((Complex.arg (x + y) : Real.Angle) -
            (Complex.arg x : Real.Angle)).toReal < 0) := by
          rw [kw_angle_sub_toReal_eq_arg_div hx hsum]
          exact kw_arg_div_neg_of_cross_neg hx (hcrossLeft.symm ▸ hneg)
      have houter :
          (((Complex.arg y : Real.Angle) -
            (Complex.arg x : Real.Angle)).toReal < 0) := by
          rw [kw_angle_sub_toReal_eq_arg_div hx hy]
          exact kw_arg_div_neg_of_cross_neg hx hneg
      rw [Real.Angle.toReal_neg_iff_sign_neg] at hleft houter
      exact hleft.trans houter.symm
    · have hleftArg : 0 < Complex.arg ((x + y) / x) :=
          kw_arg_div_pos_of_cross_pos hx (by rw [hcrossLeft]; exact hpos)
      have houterArg : 0 < Complex.arg (y / x) :=
          kw_arg_div_pos_of_cross_pos hx hpos
      have hleftSign :
          ((Complex.arg (x + y) : Real.Angle) -
            (Complex.arg x : Real.Angle)).sign = 1 := by
        rw [← Real.Angle.sign_toReal
          (kw_angle_sub_ne_pi_of_cross_ne_zero hx hsum
            (hcrossLeft.symm ▸ hcross))]
        rw [kw_angle_sub_toReal_eq_arg_div hx hsum]
        exact sign_pos hleftArg
      have houterSign :
          ((Complex.arg y : Real.Angle) -
            (Complex.arg x : Real.Angle)).sign = 1 := by
        rw [← Real.Angle.sign_toReal
          (kw_angle_sub_ne_pi_of_cross_ne_zero hx hy hcross)]
        rw [kw_angle_sub_toReal_eq_arg_div hx hy]
        exact sign_pos houterArg
      exact hleftSign.trans houterSign.symm





theorem kwAngleTurnPhase_ear_splice_vectors
    (previous incoming outgoing next : ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwAngleTurnPhase (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle) *
        kwAngleTurnPhase (Complex.arg incoming : Real.Angle)
          (Complex.arg outgoing : Real.Angle) *
        kwAngleTurnPhase (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle) =
      kwAngleTurnPhase (Complex.arg previous : Real.Angle)
          (Complex.arg (incoming + outgoing) : Real.Angle) *
        kwAngleTurnPhase (Complex.arg (incoming + outgoing) : Real.Angle)
          (Complex.arg next : Real.Angle) := by
  have hdiag : incoming + outgoing ≠ 0 := by
    intro hzero
    have : outgoing = -incoming := by linear_combination hzero
    apply hmiddle
    rw [this]
    simp [kwComplexCross]
    ring
  have hleftFirst : kwComplexCross previous incoming ≠ 0 := by
    rcases hleft with h | h <;> nlinarith [h.1]
  have hleftDiag : kwComplexCross previous (incoming + outgoing) ≠ 0 := by
    rcases hleft with h | h <;> nlinarith [h.2]
  have hrightFirst : kwComplexCross (incoming + outgoing) outgoing ≠ 0 := by
    rcases hright with h | h <;> nlinarith [h.1]
  have hrightNext : kwComplexCross (incoming + outgoing) next ≠ 0 := by
    rcases hright with h | h <;> nlinarith [h.2]
  have hleftPhase :
      kwAngleTurnPhase (Complex.arg previous : Real.Angle)
          (Complex.arg incoming : Real.Angle) *
        kwAngleTurnPhase (Complex.arg incoming : Real.Angle)
          (Complex.arg (incoming + outgoing) : Real.Angle) =
      kwAngleTurnPhase (Complex.arg previous : Real.Angle)
        (Complex.arg (incoming + outgoing) : Real.Angle) := by
    apply kwAngleTurnPhase_mul_of_outer_sign
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hp hi hleftFirst
    · have hcross : kwComplexCross incoming (incoming + outgoing) =
          kwComplexCross incoming outgoing := by
          simp only [kwComplexCross, Complex.add_re, Complex.add_im]
          ring
      exact kw_angle_sub_ne_pi_of_cross_ne_zero hi hdiag
        (hcross.symm ▸ hmiddle)
    · rcases hleft with h | h
      · exact (kw_angle_sub_sign_of_cross_pos hp hi h.1).trans
          (kw_angle_sub_sign_of_cross_pos hp hdiag h.2).symm
      · exact (kw_angle_sub_sign_of_cross_neg hp hi h.1).trans
          (kw_angle_sub_sign_of_cross_neg hp hdiag h.2).symm
  have hrightPhase :
      kwAngleTurnPhase (Complex.arg (incoming + outgoing) : Real.Angle)
          (Complex.arg outgoing : Real.Angle) *
        kwAngleTurnPhase (Complex.arg outgoing : Real.Angle)
          (Complex.arg next : Real.Angle) =
      kwAngleTurnPhase (Complex.arg (incoming + outgoing) : Real.Angle)
        (Complex.arg next : Real.Angle) := by
    apply kwAngleTurnPhase_mul_of_outer_sign
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hdiag ho hrightFirst
    · exact hrightTurn
    · rcases hright with h | h
      · exact (kw_angle_sub_sign_of_cross_pos hdiag ho h.1).trans
          (kw_angle_sub_sign_of_cross_pos hdiag hn h.2).symm
      · exact (kw_angle_sub_sign_of_cross_neg hdiag ho h.1).trans
          (kw_angle_sub_sign_of_cross_neg hdiag hn h.2).symm
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  rw [← hleftPhase, ← hrightPhase, ← hmiddlePhase]
  ring



theorem kw_triangle_edgeAngles_same_sign {x y z : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0)
    (hcross : kwComplexCross x y ≠ 0) :
    (0 < ((Complex.arg y : Real.Angle) -
          (Complex.arg x : Real.Angle)).toReal ∧
      0 < ((Complex.arg z : Real.Angle) -
          (Complex.arg y : Real.Angle)).toReal ∧
      0 < ((Complex.arg x : Real.Angle) -
          (Complex.arg z : Real.Angle)).toReal) ∨
    (((Complex.arg y : Real.Angle) -
          (Complex.arg x : Real.Angle)).toReal < 0 ∧
      ((Complex.arg z : Real.Angle) -
          (Complex.arg y : Real.Angle)).toReal < 0 ∧
      ((Complex.arg x : Real.Angle) -
          (Complex.arg z : Real.Angle)).toReal < 0) := by
  obtain ⟨hxy_yz, hyz_zx⟩ := kwComplexCross_cyclic_of_sum_zero hsum
  rcases lt_or_gt_of_ne hcross with hneg | hpos
  · right
    rw [kw_angle_sub_toReal_eq_arg_div hx hy,
      kw_angle_sub_toReal_eq_arg_div hy hz,
      kw_angle_sub_toReal_eq_arg_div hz hx]
    exact ⟨kw_arg_div_neg_of_cross_neg hx hneg,
      kw_arg_div_neg_of_cross_neg hy (hxy_yz ▸ hneg),
      kw_arg_div_neg_of_cross_neg hz (hyz_zx ▸ hxy_yz ▸ hneg)⟩
  · left
    rw [kw_angle_sub_toReal_eq_arg_div hx hy,
      kw_angle_sub_toReal_eq_arg_div hy hz,
      kw_angle_sub_toReal_eq_arg_div hz hx]
    exact ⟨kw_arg_div_pos_of_cross_pos hx hpos,
      kw_arg_div_pos_of_cross_pos hy (hxy_yz ▸ hpos),
      kw_arg_div_pos_of_cross_pos hz (hyz_zx ▸ hxy_yz ▸ hpos)⟩



theorem kw_triangle_principal_phaseProduct_eq_neg_one {x y z : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0)
    (hcross : kwComplexCross x y ≠ 0) :
    Complex.exp (((Complex.arg (y / x) : ℂ) * Complex.I) / 2) *
        Complex.exp (((Complex.arg (z / y) : ℂ) * Complex.I) / 2) *
        Complex.exp (((Complex.arg (x / z) : ℂ) * Complex.I) / 2) = -1 := by
  have hsign := kw_triangle_edgeAngles_same_sign hx hy hz hsum hcross
  have hphase := kw_three_principal_halfAngle_product_eq_neg_one
    (Complex.arg x : Real.Angle) (Complex.arg y : Real.Angle)
    (Complex.arg z : Real.Angle) hsign
  rwa [kw_angle_sub_toReal_eq_arg_div hx hy,
    kw_angle_sub_toReal_eq_arg_div hy hz,
    kw_angle_sub_toReal_eq_arg_div hz hx] at hphase




theorem KWStraightLineEmbedding.triangle_not_collinear
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d₀ d₁ d₂ : G.Dart)
    (h₀₁ : d₀.snd = d₁.fst) (h₁₂ : d₁.snd = d₂.fst)
    (h₂₀ : d₂.snd = d₀.fst) :
    ¬Collinear ℝ
      ({embedding.vertex d₀.fst, embedding.vertex d₀.snd,
        embedding.vertex d₁.snd} : Set ℂ) := by
  have hAB : d₀.fst ≠ d₀.snd := d₀.fst_ne_snd
  have hBC : d₀.snd ≠ d₁.snd := by
    rw [h₀₁]
    exact d₁.fst_ne_snd
  have hCA : d₁.snd ≠ d₀.fst := by
    rw [h₁₂, ← h₂₀]
    exact d₂.fst_ne_snd
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · have hs : Sbtw ℝ (embedding.vertex d₂.fst)
        (embedding.vertex d₀.snd) (embedding.vertex d₂.snd) := by
      refine ⟨?_, embedding.vertex_injective.ne ?_,
        embedding.vertex_injective.ne ?_⟩
      · simpa only [h₂₀, h₁₂] using hmid.symm
      · simpa only [← h₁₂] using hBC
      · simpa only [h₂₀] using hAB.symm
    exact embedding.vertex_not_strictly_between d₂ d₀.snd
      (by simpa only [← h₁₂] using hBC)
      (by simpa only [h₂₀] using hAB.symm) hs
  · have hs : Sbtw ℝ (embedding.vertex d₀.snd)
        (embedding.vertex d₁.snd) (embedding.vertex d₀.fst) := by
      exact ⟨hmid, embedding.vertex_injective.ne hBC.symm,
        embedding.vertex_injective.ne hCA⟩
    exact embedding.vertex_not_strictly_between d₀.symm d₁.snd
      (by simpa only using hBC.symm)
      (by simpa only using hCA) hs
  · have hs : Sbtw ℝ (embedding.vertex d₁.snd)
        (embedding.vertex d₀.fst) (embedding.vertex d₀.snd) := by
      exact ⟨hmid, embedding.vertex_injective.ne hCA.symm,
        embedding.vertex_injective.ne hAB⟩
    exact embedding.vertex_not_strictly_between d₁.symm d₀.fst
      (by simpa only [h₀₁] using hCA.symm)
      (by simpa only [h₀₁] using hAB) (by simpa [h₀₁] using hs)



theorem KWStraightLineEmbedding.turnPhase_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d₀ d₁ d₂ : G.Dart)
    (h₀₁ : d₀.snd = d₁.fst) (h₁₂ : d₁.snd = d₂.fst)
    (h₂₀ : d₂.snd = d₀.fst) :
    embedding.turnPhase d₀ d₁ * embedding.turnPhase d₁ d₂ *
        embedding.turnPhase d₂ d₀ = -1 := by
  let x : ℂ := embedding.vertex d₀.snd - embedding.vertex d₀.fst
  let y : ℂ := embedding.vertex d₁.snd - embedding.vertex d₁.fst
  let z : ℂ := embedding.vertex d₂.snd - embedding.vertex d₂.fst
  have hx : x ≠ 0 := by
    simpa only [x] using embedding.dartVector_ne_zero d₀
  have hy : y ≠ 0 := by
    simpa only [y] using embedding.dartVector_ne_zero d₁
  have hz : z ≠ 0 := by
    simpa only [z] using embedding.dartVector_ne_zero d₂
  have hsum : x + y + z = 0 := by
    dsimp only [x, y, z]
    rw [h₀₁, h₁₂, h₂₀]
    ring
  have hcross : kwComplexCross x y ≠ 0 := by
    intro hzero
    apply embedding.triangle_not_collinear d₀ d₁ d₂ h₀₁ h₁₂ h₂₀
    apply kw_collinear_of_cross_sub_eq_zero
    simpa only [x, y, h₀₁] using hzero
  simpa only [KWStraightLineEmbedding.turnPhase, x, y, z] using
    kw_triangle_principal_phaseProduct_eq_neg_one hx hy hz hsum hcross

end StatMech.FrontierA
