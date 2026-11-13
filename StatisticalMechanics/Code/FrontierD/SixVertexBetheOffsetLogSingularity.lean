/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronTruncation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds





namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogNormKernel (c x : Real) : Real :=
  let a := c ^ 2 - 1
  (1 / 2 : Real) *
    (Real.log (a ^ 2 + 1 + 2 * a * Real.cos x) -
      Real.log (2 - 2 * Real.cos x))

def sixVertexBetheLogNormDerivative (c x : Real) : Real :=
  let a := c ^ 2 - 1
  (-a * Real.sin x / (a ^ 2 + 1 + 2 * a * Real.cos x)) -
    Real.sin x / (2 - 2 * Real.cos x)

theorem hasDerivAt_sixVertexBetheLogNormKernel
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    HasDerivAt (sixVertexBetheLogNormKernel c)
      (sixVertexBetheLogNormDerivative c x) x := by
  let a := c ^ 2 - 1
  let A : Real → Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real → Real := fun y => 2 - 2 * Real.cos y
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [← Real.cos_abs, ← Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · exact le_rfl
      · exact abs_le.mpr hxIcc
      · exact abs_pos.mpr hx
    linarith
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add (a ^ 2 + 1)
      using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    dsimp [B]
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add 2
      using 1 <;> ring
  have hlogA := hAderiv.log hA.ne'
  have hlogB := hBderiv.log hB.ne'
  have hlog := (hlogA.sub hlogB).const_mul (1 / 2 : Real)
  unfold sixVertexBetheLogNormKernel sixVertexBetheLogNormDerivative
  dsimp [a, A, B] at hlog ⊢
  convert hlog using 1 <;> field_simp [hA.ne', hB.ne'] <;> ring

theorem abs_mul_sixVertexBetheLogNormDenominatorDerivative_le
    {x : Real} (hx : x ≠ 0) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * (Real.sin x / (2 - 2 * Real.cos x))| ≤ Real.pi / 2 := by
  let u := x / 2
  have huIcc : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [u]
    constructor <;> linarith [hxIcc.1, hxIcc.2]
  have husin : 2 / Real.pi * |u| ≤ |Real.sin u| :=
    Real.mul_abs_le_abs_sin (abs_le.2 huIcc)
  have hu0 : u ≠ 0 := by dsimp [u]; exact div_ne_zero hx (by norm_num)
  have hsin0 : Real.sin u ≠ 0 := by
    intro h
    rw [h, abs_zero] at husin
    have : 0 < 2 / Real.pi * |u| := mul_pos (by positivity) (abs_pos.mpr hu0)
    linarith
  have hsin : Real.sin x = 2 * Real.sin u * Real.cos u := by
    rw [show x = 2 * u by dsimp [u]; ring, Real.sin_two_mul]
  have hden : 2 - 2 * Real.cos x = 4 * Real.sin u ^ 2 := by
    rw [show x = 2 * u by dsimp [u]; ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [hden, hsin, abs_mul, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (2 : Real) by norm_num)]
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : Real) by norm_num), abs_pow]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hucos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  have hux : |x| = 2 * |u| := by
    calc
      |x| = |2 * u| := by congr 1; dsimp [u]; ring
      _ = 2 * |u| := by rw [abs_mul]; norm_num
  have hsinLower : |x| / Real.pi ≤ |Real.sin u| := by
    calc
      |x| / Real.pi = 2 / Real.pi * |u| := by rw [hux]; ring
      _ ≤ |Real.sin u| := husin
  have hsinPos : 0 < |Real.sin u| := abs_pos.mpr hsin0
  rw [pow_two]
  have heq :
      |x| * (2 * |Real.sin u| * |Real.cos u| /
        (4 * (|Real.sin u| * |Real.sin u|))) =
      |x| * |Real.cos u| / (2 * |Real.sin u|) := by
    field_simp [hsinPos.ne']
    ring
  rw [heq, div_le_iff₀ (mul_pos (by positivity) hsinPos)]
  have hxnonneg : 0 ≤ |x| := abs_nonneg x
  have hxle : |x| ≤ Real.pi * |Real.sin u| := by
    simpa [mul_comm] using (div_le_iff₀ Real.pi_pos).mp hsinLower
  have hmul := mul_le_mul_of_nonneg_left hucos hxnonneg
  nlinarith

theorem abs_mul_sixVertexBetheLogNormDerivative_le
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * sixVertexBetheLogNormDerivative c x| ≤
      Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : (a - 1) ^ 2 ≤ A := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := lt_of_lt_of_le (sq_pos_of_pos (sub_pos.mpr ha)) hA
  have hxabs : |x| ≤ Real.pi := abs_le.mpr hxIcc
  have hsabs : |Real.sin x| ≤ 1 := by
    exact abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  have hreg : |x * (-a * Real.sin x / A)| ≤
      Real.pi * a / (a - 1) ^ 2 := by
    rw [abs_mul, abs_div, abs_mul, abs_neg, abs_of_pos (zero_lt_one.trans ha),
      abs_of_pos hApos]
    rw [show |x| * (a * |Real.sin x| / A) =
      (|x| * a * |Real.sin x|) / A by ring]
    rw [div_le_div_iff₀ hApos (sq_pos_of_pos (sub_pos.mpr ha))]
    have hprod : |x| * |Real.sin x| ≤ Real.pi := by
      nlinarith [mul_le_mul hxabs hsabs (abs_nonneg (Real.sin x)) Real.pi_pos.le]
    have ha0 : 0 ≤ a := ha.le.trans' zero_le_one
    calc
      |x| * a * |Real.sin x| * (a - 1) ^ 2 =
          a * (|x| * |Real.sin x|) * (a - 1) ^ 2 := by ring
      _ ≤ a * Real.pi * (a - 1) ^ 2 := by gcongr
      _ ≤ a * Real.pi * A := by gcongr
      _ = Real.pi * a * A := by ring
  have hsing := abs_mul_sixVertexBetheLogNormDenominatorDerivative_le hx hxIcc
  unfold sixVertexBetheLogNormDerivative
  dsimp [a, A] at hreg ⊢
  calc
    |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x) -
        Real.sin x / (2 - 2 * Real.cos x))| ≤
        |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x))| +
        |x * (Real.sin x / (2 - 2 * Real.cos x))| := by
          rw [mul_sub]
          exact abs_sub _ _
    _ ≤ Real.pi * a / (a - 1) ^ 2 + Real.pi / 2 :=
      add_le_add hreg hsing
    _ = Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
      dsimp [a]
      ring

theorem abs_mul_sixVertexBetheLogNormDerivative_of_linearOffset
    {c C x f : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hf : |f| ≤ C * |x|) :
    |f * sixVertexBetheLogNormDerivative c x| ≤
      C * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2) := by
  have hkernel := abs_mul_sixVertexBetheLogNormDerivative_le hc hx hxIcc
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hC : 0 ≤ C := by
    have hCx : 0 ≤ C * |x| := (abs_nonneg f).trans hf
    exact nonneg_of_mul_nonneg_left hCx hxpos
  rw [abs_mul]
  calc
    |f| * |sixVertexBetheLogNormDerivative c x| =
        (|f| / |x|) * |x * sixVertexBetheLogNormDerivative c x| := by
          rw [abs_mul]
          field_simp [hxpos.ne']
    _ ≤ C * |x * sixVertexBetheLogNormDerivative c x| := by
      gcongr
      exact (div_le_iff₀ hxpos).2 hf
    _ ≤ C * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hkernel hC

def sixVertexBetheLogNormSecondDerivativeBound (c : Real) : Real :=
  Real.pi ^ 2 *
      ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4) +
    Real.pi ^ 2 / 4

theorem hasDerivAt_sixVertexBetheLogNormDerivative
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    HasDerivAt (sixVertexBetheLogNormDerivative c)
      ((-(c ^ 2 - 1) * Real.cos x *
            ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) -
          2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2) /
          (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos x) ^ 2) +
        1 / (2 - 2 * Real.cos x)) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real -> Real := fun y => 2 - 2 * Real.cos y
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [<- Real.cos_abs, <- Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · exact le_rfl
      · exact abs_le.mpr hxIcc
      · exact abs_pos.mpr hx
    linarith
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add (a ^ 2 + 1)
      using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    dsimp [B]
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add 2
      using 1 <;> ring
  have hreg := ((Real.hasDerivAt_sin x).const_mul (-a)).div hAderiv hA.ne'
  have hsing := (Real.hasDerivAt_sin x).neg.div hBderiv hB.ne'
  have hsingValue :
      (-Real.cos x * B x - -Real.sin x * (2 * Real.sin x)) / (B x) ^ 2 =
        1 / B x := by
    field_simp [hB.ne']
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hsing' : HasDerivAt (-Real.sin / B) (1 / B x) x := by
    apply hsing.congr_deriv
    simpa only [Pi.neg_apply] using hsingValue
  unfold sixVertexBetheLogNormDerivative
  dsimp [a, A, B] at hreg hsing' ⊢
  convert hreg.add hsing' using 1
  · funext y
    simp only [Pi.add_apply, Pi.div_apply, Pi.neg_apply]
    ring
  · ring

theorem abs_sq_mul_sixVertexBetheLogNormSecondDerivative_le
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x ^ 2 *
      ((-(c ^ 2 - 1) * Real.cos x *
            ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) -
          2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2) /
          (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos x) ^ 2) +
        1 / (2 - 2 * Real.cos x))| <=
      sixVertexBetheLogNormSecondDerivativeBound c := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let d := c ^ 2 - 2
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hA : d ^ 2 <= A := by
    dsimp [A, a, d]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := (sq_pos_of_pos hd).trans_le hA
  have hxabs : |x| <= Real.pi := abs_le.mpr hxIcc
  have hx2 : x ^ 2 <= Real.pi ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg x) Real.pi_pos.le).2 hxabs
  have hreg : |x ^ 2 *
      ((-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2) / A ^ 2)| <=
      Real.pi ^ 2 * (a / d ^ 2 + 2 * a ^ 2 / d ^ 4) := by
    simp only [abs_mul, abs_div, abs_pow, abs_of_pos hApos]
    have hnum : |-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| <=
        a * A + 2 * a ^ 2 := by
      calc
        _ <= |-a * Real.cos x * A| + |2 * a ^ 2 * Real.sin x ^ 2| :=
          abs_sub _ _
        _ <= a * A + 2 * a ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos ha,
            abs_of_pos hApos,
            abs_of_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
              (sq_nonneg a)),
            abs_of_nonneg (sq_nonneg (Real.sin x))]
          have hcoss := abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
          have hsins := abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
          have hsinSq : Real.sin x ^ 2 <= 1 := by
            simpa [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (Real.sin x)) zero_le_one).2 hsins
          calc
            a * |Real.cos x| * A + 2 * a ^ 2 * Real.sin x ^ 2 <=
                a * 1 * A + 2 * a ^ 2 * 1 := by gcongr
            _ = _ := by ring
    have hfrac : (a * A + 2 * a ^ 2) / A ^ 2 <=
        a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by
      have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
      have hA2 : d ^ 4 <= A ^ 2 := by nlinarith [sq_nonneg (A - d ^ 2)]
      calc
        (a * A + 2 * a ^ 2) / A ^ 2 = a / A + 2 * a ^ 2 / A ^ 2 := by
          field_simp [hApos.ne']
        _ <= a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by
          gcongr
    have hx2abs : |x| ^ 2 <= Real.pi ^ 2 := by simpa [sq_abs] using hx2
    calc
      |x| ^ 2 * (|-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| /
          A ^ 2) <= Real.pi ^ 2 * ((a * A + 2 * a ^ 2) / A ^ 2) := by
            exact mul_le_mul hx2abs
              (div_le_div_of_nonneg_right hnum (sq_nonneg A))
              (div_nonneg (abs_nonneg _) (sq_nonneg A)) (sq_nonneg Real.pi)
      _ <= _ := mul_le_mul_of_nonneg_left hfrac (sq_nonneg Real.pi)
  have hsing : |x ^ 2 * (1 / (2 - 2 * Real.cos x))| <= Real.pi ^ 2 / 4 := by
    let u := x / 2
    have huIcc : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [u]
      constructor <;> linarith [hxIcc.1, hxIcc.2]
    have husin : 2 / Real.pi * |u| <= |Real.sin u| :=
      Real.mul_abs_le_abs_sin (abs_le.2 huIcc)
    have hu0 : u ≠ 0 := by dsimp [u]; exact div_ne_zero hx (by norm_num)
    have hsin0 : Real.sin u ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at husin
      have : 0 < 2 / Real.pi * |u| := mul_pos (by positivity) (abs_pos.mpr hu0)
      linarith
    rw [show 2 - 2 * Real.cos x = 4 * Real.sin u ^ 2 by
      rw [show x = 2 * u by dsimp [u]; ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq u]]
    rw [abs_mul, abs_of_nonneg (sq_nonneg x), abs_div, abs_one,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 4)
        (sq_nonneg (Real.sin u)))]
    have hxu : |x| = 2 * |u| := by
      rw [show x = 2 * u by dsimp [u]; ring, abs_mul]
      norm_num
    rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs], hxu]
    have hsquare := sq_le_sq₀ (by positivity : 0 <= 2 / Real.pi * |u|)
      (abs_nonneg (Real.sin u)) |>.2 husin
    rw [show (2 * |u|) ^ 2 * (1 / (4 * Real.sin u ^ 2)) =
      (2 * |u|) ^ 2 / (4 * Real.sin u ^ 2) by ring]
    rw [div_le_iff₀ (by positivity : 0 < 4 * Real.sin u ^ 2)]
    field_simp [Real.pi_ne_zero] at hsquare
    simp only [sq_abs] at hsquare
    have huSq : (2 * |u|) ^ 2 = 4 * u ^ 2 := by
      calc
        (2 * |u|) ^ 2 = 4 * |u| ^ 2 := by ring
        _ = 4 * u ^ 2 := by rw [sq_abs]
    rw [huSq]
    nlinarith [Real.pi_pos, sq_nonneg (Real.pi)]
  unfold sixVertexBetheLogNormSecondDerivativeBound
  dsimp [a, A, d] at hreg ⊢
  rw [mul_add]
  exact (abs_add_le _ _).trans (add_le_add hreg hsing)

end

end StatMech.FrontierD
