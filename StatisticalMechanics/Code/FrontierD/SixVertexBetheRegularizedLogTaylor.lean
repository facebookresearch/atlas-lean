/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit





namespace StatMech.FrontierD

noncomputable section

def sixVertexRegularizedBetheLogNormSecondDerivative
    (c epsilon x : Real) : Real :=
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let B := 2 - 2 * Real.cos x + epsilon
  (-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2) / A ^ 2 +
    (-Real.cos x * B + 2 * Real.sin x ^ 2) / B ^ 2

def sixVertexRegularizedBetheLogNormSecondDerivativeBound
    (c epsilon : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
    2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4 +
    1 / epsilon + 2 / epsilon ^ 2

theorem hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    HasDerivAt (sixVertexRegularizedBetheLogNormDerivative c epsilon)
      (sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real -> Real := fun y => 2 - 2 * Real.cos y + epsilon
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add
      (a ^ 2 + 1) using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    dsimp [B]
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add
      (2 + epsilon) using 1
    · funext y
      ring
    · ring
  have hreg := ((Real.hasDerivAt_sin x).const_mul (-a)).div hAderiv hA.ne'
  have hsing := (Real.hasDerivAt_sin x).neg.div hBderiv hB.ne'
  unfold sixVertexRegularizedBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormSecondDerivative
  dsimp [a, A, B] at hreg hsing ⊢
  convert hreg.add hsing using 1
  · funext y
    simp only [Pi.add_apply, Pi.div_apply, Pi.neg_apply]
    ring
  · ring

theorem abs_sixVertexRegularizedBetheLogNormSecondDerivative_le
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    |sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x| <=
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let d := c ^ 2 - 2
  let B := 2 - 2 * Real.cos x + epsilon
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hA : d ^ 2 <= A := by
    dsimp [A, a, d]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := (sq_pos_of_pos hd).trans_le hA
  have hBbase : epsilon <= B := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hBpos : 0 < B := hepsilon.trans_le hBbase
  have hsinSq : Real.sin x ^ 2 <= 1 := by
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (Real.sin x)) zero_le_one).2
        (Real.abs_sin_le_one x)
  have hreg :
      |(-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2) / A ^ 2| <=
        a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by
    rw [abs_div, abs_pow, abs_of_pos hApos]
    have hnum : |-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| <=
        a * A + 2 * a ^ 2 := by
      calc
        _ <= |-a * Real.cos x * A| +
            |2 * a ^ 2 * Real.sin x ^ 2| := abs_sub _ _
        _ <= a * A + 2 * a ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos ha,
            abs_of_pos hApos,
            abs_of_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2)
              (sq_nonneg a)), abs_of_nonneg (sq_nonneg (Real.sin x))]
          calc
            a * |Real.cos x| * A + 2 * a ^ 2 * Real.sin x ^ 2 <=
                a * 1 * A + 2 * a ^ 2 * 1 := by
              gcongr
              exact Real.abs_cos_le_one x
            _ = _ := by ring
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have hA2 : d ^ 4 <= A ^ 2 := by
      nlinarith [sq_nonneg (A - d ^ 2)]
    calc
      |-a * Real.cos x * A - 2 * a ^ 2 * Real.sin x ^ 2| / A ^ 2 <=
          (a * A + 2 * a ^ 2) / A ^ 2 := by gcongr
      _ = a / A + 2 * a ^ 2 / A ^ 2 := by field_simp [hApos.ne']
      _ <= a / d ^ 2 + 2 * a ^ 2 / d ^ 4 := by gcongr
  have hsing :
      |(-Real.cos x * B + 2 * Real.sin x ^ 2) / B ^ 2| <=
        1 / epsilon + 2 / epsilon ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos hBpos]
    have hnum : |-Real.cos x * B + 2 * Real.sin x ^ 2| <= B + 2 := by
      calc
        _ <= |-Real.cos x * B| + |2 * Real.sin x ^ 2| := abs_add_le _ _
        _ <= B + 2 := by
          rw [abs_mul, abs_neg, abs_of_pos hBpos, abs_mul,
            abs_of_nonneg (by norm_num : (0 : Real) <= 2),
            abs_of_nonneg (sq_nonneg (Real.sin x))]
          nlinarith [Real.abs_cos_le_one x]
    have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hB2 : epsilon ^ 2 <= B ^ 2 := by nlinarith
    calc
      |-Real.cos x * B + 2 * Real.sin x ^ 2| / B ^ 2 <=
          (B + 2) / B ^ 2 := by gcongr
      _ = 1 / B + 2 / B ^ 2 := by field_simp [hBpos.ne']
      _ <= 1 / epsilon + 2 / epsilon ^ 2 := by gcongr
  unfold sixVertexRegularizedBetheLogNormSecondDerivative
    sixVertexRegularizedBetheLogNormSecondDerivativeBound
  dsimp [a, A, d, B] at hreg hsing ⊢
  calc
    |_ + _| <= |_| + |_| := abs_add_le _ _
    _ <= ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4) +
        (1 / epsilon + 2 / epsilon ^ 2) := add_le_add hreg hsing
    _ = _ := by ring

def sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
    (c epsilon : Real) : NNReal :=
  Real.toNNReal
    (sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon)

theorem lipschitzWith_sixVertexRegularizedBetheLogNormDerivative
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    LipschitzWith
      (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon)
      (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
  have hboundNonneg : 0 <=
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon := by
    unfold sixVertexRegularizedBetheLogNormSecondDerivativeBound
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
      hc hepsilon).differentiableAt
  · intro x
    rw [(hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
      hc hepsilon).deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    change |sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x| <= _
    rw [show (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
        c epsilon : Real) =
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon by
        exact Real.coe_toNNReal _ hboundNonneg]
    exact abs_sixVertexRegularizedBetheLogNormSecondDerivative_le hc hepsilon

def sixVertexRegularizedBetheLogNormDerivativeBound
    (c epsilon : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + 1 / epsilon

theorem abs_sixVertexRegularizedBetheLogNormDerivative_le
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    |sixVertexRegularizedBetheLogNormDerivative c epsilon x| <=
      sixVertexRegularizedBetheLogNormDerivativeBound c epsilon := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let d := c ^ 2 - 2
  let B := 2 - 2 * Real.cos x + epsilon
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hA : d ^ 2 <= A := by
    dsimp [A, a, d]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := (sq_pos_of_pos hd).trans_le hA
  have hB : epsilon <= B := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hBpos : 0 < B := hepsilon.trans_le hB
  unfold sixVertexRegularizedBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormDerivativeBound
  dsimp [a, A, d, B]
  calc
    |(-a * Real.sin x / A) - Real.sin x / B| <=
        |-a * Real.sin x / A| + |Real.sin x / B| := abs_sub _ _
    _ <= a / d ^ 2 + 1 / epsilon := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hApos,
        abs_div, abs_of_pos hBpos]
      apply add_le_add
      · calc
          a * |Real.sin x| / A <= a / A := by
            apply div_le_div_of_nonneg_right _ hApos.le
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) ha.le
          _ <= a / d ^ 2 :=
            div_le_div_of_nonneg_left ha.le (sq_pos_of_pos hd) hA
      · calc
          |Real.sin x| / B <= 1 / B := by
            exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hBpos.le
          _ <= 1 / epsilon :=
            div_le_div_of_nonneg_left zero_le_one hepsilon hB

def sixVertexLogOffsetQuotientLipschitzBound
    (c lower U G Lu D : Real) : Real :=
  (Lu * G + U * D) / lower +
    U * G * (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
      lower ^ 2

def sixVertexLogOffsetQuotientLipschitzNNReal
    (c lower U G Lu D : Real) : NNReal :=
  Real.toNNReal
    (sixVertexLogOffsetQuotientLipschitzBound c lower U G Lu D)

theorem lipschitzWith_mul_div_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n <= N)
    (p : Fin n -> Real) {lower U G : Real} (hlower : 0 < lower)
    (hU : 0 <= U) (hG : 0 <= G)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y)
    {u tau : Real -> Real} {Lu D : NNReal}
    (huLip : LipschitzWith Lu u) (huBound : forall y, |u y| <= U)
    (htauLip : LipschitzWith D tau) (htauBound : forall y, |tau y| <= G) :
    LipschitzWith
      (sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D)
      (fun y => u y * tau y /
        sixVertexFiniteRootDensity c N n p y) := by
  let rho := sixVertexFiniteRootDensity c N n p
  let LR : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let C := sixVertexLogOffsetQuotientLipschitzBound c lower U G Lu D
  have hLR : 0 <= LR := by dsimp [LR]; exact NNReal.coe_nonneg _
  have hC : 0 <= C := by
    dsimp [C, sixVertexLogOffsetQuotientLipschitzBound]
    positivity
  have hcoe :
      (sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D : Real) =
        C := Real.coe_toNNReal _ hC
  have hrhoLip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  let dyz := |y - z|
  have hudiff : |u y - u z| <= (Lu : Real) * dyz := by
    simpa [Real.dist_eq, dyz] using huLip.dist_le_mul y z
  have htaudiff : |tau y - tau z| <= (D : Real) * dyz := by
    simpa [Real.dist_eq, dyz] using htauLip.dist_le_mul y z
  have hrhodiff : |rho z - rho y| <= LR * dyz := by
    have h := hrhoLip.dist_le_mul z y
    simpa only [Real.dist_eq, rho, LR, dyz, abs_sub_comm] using h
  have hry : 0 < rho y := hlower.trans_le (hdensity y)
  have hrz : 0 < rho z := hlower.trans_le (hdensity z)
  have hrearrange :
      u y * tau y / rho y - u z * tau z / rho z =
        (u y - u z) * tau y / rho y +
        u z * (tau y - tau z) / rho y +
        u z * tau z * (rho z - rho y) / (rho y * rho z) := by
    field_simp [hry.ne', hrz.ne']
    ring
  rw [hrearrange]
  calc
    |_ + _ + _| <= |_| + |_| + |_| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ <= ((Lu : Real) * dyz * G) / lower +
        (U * ((D : Real) * dyz)) / lower +
        (U * G * (LR * dyz)) / lower ^ 2 := by
      rw [abs_div, abs_div, abs_div, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_mul, abs_of_pos hry, abs_of_pos hrz]
      apply add_le_add
      · apply add_le_add
        · have hnum := mul_le_mul hudiff (htauBound y)
            (abs_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _))
          exact (div_le_div_of_nonneg_right hnum hry.le).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)) hG)
              hlower (hdensity y))
        · have hnum := mul_le_mul (huBound z) htaudiff
            (abs_nonneg _) hU
          exact (div_le_div_of_nonneg_right hnum hry.le).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg hU (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)))
              hlower (hdensity y))
      · have hprod : |u z| * |tau z| <= U * G :=
          mul_le_mul (huBound z) (htauBound z) (abs_nonneg _) hU
        have hnum : |u z| * |tau z| * |rho z - rho y| <=
            U * G * (LR * dyz) :=
          mul_le_mul hprod hrhodiff (abs_nonneg _) (mul_nonneg hU hG)
        have hdenLower : lower ^ 2 <= rho y * rho z := by
          nlinarith [hdensity y, hdensity z]
        exact (div_le_div_of_nonneg_right hnum
            (mul_nonneg hry.le hrz.le)).trans
          (div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hU hG)
              (mul_nonneg hLR (abs_nonneg (y - z))))
            (sq_pos_of_pos hlower) hdenLower)
    _ = C * |y - z| := by
      dsimp [C, sixVertexLogOffsetQuotientLipschitzBound, dyz, LR]
      ring

theorem abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (a b : Real) :
    |sixVertexRegularizedBetheLogKernel c epsilon b -
        sixVertexRegularizedBetheLogKernel c epsilon a -
      sixVertexRegularizedBetheLogNormDerivative c epsilon a * (b - a)| <=
        (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
          c epsilon : Real) * |b - a| ^ 2 := by
  exact abs_sub_sub_deriv_mul_le_of_lipschitz
    (fun x => hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon)
    (lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon) a b

end

end StatMech.FrontierD
