/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddWallisCore










namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

private theorem abs_log_sub_log_le_of_pos_lower_avg
    {lower x y : Real} (hlower : 0 < lower)
    (hlowerX : lower <= x) (hlowerY : lower <= y) :
    |Real.log x - Real.log y| <= |x - y| / lower := by
  have hx : 0 < x := hlower.trans_le hlowerX
  have hy : 0 < y := hlower.trans_le hlowerY
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x <= Real.log y :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx)
        (Set.mem_Ioi.mpr hy) hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hlog),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hbasic := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hbasic
    have hdiv : (y - x) / x <= (y - x) / lower :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hlower hlowerX
    calc
      -(Real.log x - Real.log y) = Real.log y - Real.log x := by ring
      _ <= y / x - 1 := hbasic
      _ = (y - x) / x := by field_simp [hx.ne']
      _ <= (y - x) / lower := hdiv
      _ = -(x - y) / lower := by ring
  · have hlog : Real.log y <= Real.log x :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hy)
        (Set.mem_Ioi.mpr hx) hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hlog),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hbasic := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hbasic
    calc
      Real.log x - Real.log y <= x / y - 1 := hbasic
      _ = (x - y) / y := by field_simp [hy.ne']
      _ <= (x - y) / lower :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hlower hlowerY



theorem lipschitzOnWith_primitive_div_id_Ioi
    {F rho : Real -> Real} {C : NNReal}
    (hF : forall x, HasDerivAt F (rho x) x)
    (hF0 : F 0 = 0) (hrho : LipschitzWith C rho) :
    LipschitzOnWith C (fun x => F x / x) (Set.Ioi 0) := by
  apply (convex_Ioi 0).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact ((hF x).div (hasDerivAt_id x) hx.ne').differentiableAt
  · intro x hx
    have hx0 : x ≠ 0 := hx.ne'
    have hderiv := (hF x).div (hasDerivAt_id x) hx0
    have hderiv' : HasDerivAt (fun y => F y / y)
        ((rho x * x - F x) / x ^ 2) x := by
      simpa only [id_eq, mul_one] using hderiv
    rw [hderiv'.deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    have htaylor := abs_sub_sub_deriv_mul_le_of_lipschitz
      hF hrho x 0
    rw [hF0] at htaylor
    have hnum : |rho x * x - F x| <= (C : Real) * x ^ 2 := by
      have hrearrange :
          0 - F x - rho x * (0 - x) = rho x * x - F x := by ring
      rw [hrearrange] at htaylor
      simpa [abs_of_pos (show 0 < x from hx)] using htaylor
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (show 0 < x from hx)]
    exact (div_le_iff₀ (sq_pos_of_pos hx)).2 (by
      simpa [mul_comm] using hnum)

theorem primitive_div_id_lower
    {F rho : Real -> Real} {lower x : Real}
    (hF : forall y, HasDerivAt F (rho y) y) (hF0 : F 0 = 0)
    (hcont : Continuous rho) (hx : 0 < x)
    (hrho : forall y : Set.Icc (0 : Real) x,
      lower <= rho y) :
    lower <= F x / x := by
  have hFTC : (∫ y in (0 : Real)..x, rho y) = F x := by
    have hderiv : deriv F = rho := by
      funext y
      exact (hF y).deriv
    have hdiff : forall y, y ∈ Set.uIcc (0 : Real) x ->
        DifferentiableAt Real F y := fun y _ => (hF y).differentiableAt
    have h := intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff
      hcont.continuousOn
    simpa [hF0] using h
  have hmono := intervalIntegral.integral_mono_on hx.le
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 x)
    (hcont.intervalIntegrable 0 x) (fun y hy => hrho ⟨y, hy⟩)
  rw [intervalIntegral.integral_const, hFTC] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  exact (le_div_iff₀ hx).2 (by simpa [mul_comm] using hmono)



theorem abs_primitive_midpoint_defect_le
    {F rho : Real -> Real} {C : NNReal}
    (hF : forall x, HasDerivAt F (rho x) x)
    (hrho : LipschitzWith C rho) (a b : Real) :
    |F ((a + b) / 2) - (F a + F b) / 2| <=
      (C : Real) * (b - a) ^ 2 / 4 := by
  let m := (a + b) / 2
  have ha := abs_sub_sub_deriv_mul_le_of_lipschitz hF hrho m a
  have hb := abs_sub_sub_deriv_mul_le_of_lipschitz hF hrho m b
  have hsum :
      |(F a - F m - rho m * (a - m)) +
          (F b - F m - rho m * (b - m))| <=
        (C : Real) * |a - m| ^ 2 + (C : Real) * |b - m| ^ 2 :=
    (abs_add_le _ _).trans (add_le_add ha hb)
  have hleft :
      (F a - F m - rho m * (a - m)) +
          (F b - F m - rho m * (b - m)) =
        -2 * (F m - (F a + F b) / 2) := by
    dsimp [m]
    ring
  rw [hleft, abs_mul, abs_neg] at hsum
  norm_num at hsum
  have hright :
      (C : Real) * (a - m) ^ 2 + (C : Real) * (b - m) ^ 2 =
        (C : Real) * (b - a) ^ 2 / 2 := by
    dsimp [m]
    ring
  rw [hright] at hsum
  linarith



theorem abs_primitive_div_id_midpoint_defect_le
    {F rho : Real -> Real} {C : NNReal}
    (hF : forall x, HasDerivAt F (rho x) x) (hF0 : F 0 = 0)
    (hrho : LipschitzWith C rho) {a b : Real}
    (ha : 0 < a) (hab : a <= b) :
    let m := (a + b) / 2
    |F m / m - (F a / a + F b / b) / 2| <=
      (C : Real) * (b - a) ^ 2 / (2 * m) := by
  dsimp
  let m := (a + b) / 2
  let A := fun x : Real => F x / x
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < m := by dsimp [m]; linarith
  have hA := lipschitzOnWith_primitive_div_id_Ioi hF hF0 hrho
  have hAab : |A b - A a| <= (C : Real) * (b - a) := by
    have h := hA.dist_le_mul b (Set.mem_Ioi.mpr hb)
      a (Set.mem_Ioi.mpr ha)
    simpa [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hdefect := abs_primitive_midpoint_defect_le hF hrho a b
  have hid :
      A m - (A a + A b) / 2 =
        (F m - (F a + F b) / 2) / m +
          (b - a) * (A b - A a) / (4 * m) := by
    dsimp [A]
    field_simp [ha.ne', hb.ne', hm.ne']
    ring
  rw [hid]
  calc
    |(F m - (F a + F b) / 2) / m +
        (b - a) * (A b - A a) / (4 * m)| <=
        |(F m - (F a + F b) / 2) / m| +
          |(b - a) * (A b - A a) / (4 * m)| := abs_add_le _ _
    _ <= ((C : Real) * (b - a) ^ 2 / 4) / m +
        ((b - a) * ((C : Real) * (b - a))) / (4 * m) := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hm]
        exact div_le_div_of_nonneg_right hdefect hm.le
      · rw [abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hab),
          abs_of_pos (by positivity : 0 < (4 : Real) * m)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAab (sub_nonneg.mpr hab)) (by positivity)
    _ = (C : Real) * (b - a) ^ 2 / (2 * m) := by ring



theorem abs_primitive_div_id_sub_deriv_zero_le
    {F rho : Real -> Real} {C : NNReal}
    (hF : forall x, HasDerivAt F (rho x) x) (hF0 : F 0 = 0)
    (hrho : LipschitzWith C rho) {x : Real} (hx : 0 < x) :
    |F x / x - rho 0| <= (C : Real) * x := by
  have htaylor := abs_sub_sub_deriv_mul_le_of_lipschitz hF hrho 0 x
  rw [hF0] at htaylor
  have hrearrange : F x / x - rho 0 =
      (F x - 0 - rho 0 * (x - 0)) / x := by
    field_simp [hx.ne']
    ring
  rw [hrearrange, abs_div, abs_of_pos hx]
  apply (div_le_iff₀ hx).2
  calc
    |F x - 0 - rho 0 * (x - 0)| <=
        (C : Real) * |x - 0| ^ 2 := htaylor
    _ = ((C : Real) * x) * x := by
      rw [sub_zero, abs_of_pos hx]
      ring



theorem abs_two_log_average_sub_log_sub_log_le
    {lower x y : Real} (hlower : 0 < lower)
    (hx : lower <= x) (hy : lower <= y) :
    |2 * Real.log ((x + y) / 2) - Real.log x - Real.log y| <=
      (x - y) ^ 2 / (4 * lower ^ 2) := by
  have hx0 : 0 < x := hlower.trans_le hx
  have hy0 : 0 < y := hlower.trans_le hy
  have havg : 0 < (x + y) / 2 := by positivity
  have hxy : 0 < x * y := mul_pos hx0 hy0
  let r := ((x + y) / 2) ^ 2 / (x * y)
  have hrEq : r = 1 + (x - y) ^ 2 / (4 * x * y) := by
    dsimp [r]
    field_simp [hx0.ne', hy0.ne']
    ring
  have hrOne : 1 <= r := by
    rw [hrEq]
    exact le_add_of_nonneg_right
      (div_nonneg (sq_nonneg (x - y)) (by positivity))
  have hrPos : 0 < r := zero_lt_one.trans_le hrOne
  have hlogEq :
      2 * Real.log ((x + y) / 2) - Real.log x - Real.log y =
        Real.log r := by
    dsimp [r]
    rw [Real.log_div (sq_pos_of_pos havg).ne' hxy.ne', Real.log_pow,
      Real.log_mul hx0.ne' hy0.ne']
    ring
  rw [hlogEq, abs_of_nonneg (Real.log_nonneg hrOne)]
  have hlog := Real.log_le_sub_one_of_pos hrPos
  have hden : 4 * lower ^ 2 <= 4 * x * y := by
    nlinarith [mul_le_mul hx hy hlower.le hx0.le]
  calc
    Real.log r <= r - 1 := hlog
    _ = (x - y) ^ 2 / (4 * x * y) := by rw [hrEq]; ring
    _ <= (x - y) ^ 2 / (4 * lower ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg (x - y))
        (by positivity) hden



theorem abs_two_log_sub_two_log_le_of_pos_lower
    {lower x y : Real} (hlower : 0 < lower)
    (hx : lower <= x) (hy : lower <= y) :
    |2 * Real.log x - 2 * Real.log y| <= 2 * |x - y| / lower := by
  have h := abs_log_sub_log_le_of_pos_lower_avg hlower hx hy
  rw [show 2 * Real.log x - 2 * Real.log y =
    2 * (Real.log x - Real.log y) by ring, abs_mul]
  norm_num
  calc
    2 * |Real.log x - Real.log y| <=
        2 * (|x - y| / lower) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 * |x - y| / lower := by ring



theorem abs_two_log_primitive_div_id_midpoint_sub_le
    {F rho : Real -> Real} {C : NNReal} {lower a b : Real}
    (hF : forall x, HasDerivAt F (rho x) x) (hF0 : F 0 = 0)
    (hrho : LipschitzWith C rho) (hlower : 0 < lower)
    (ha : 0 < a) (hab : a <= b)
    (hlowerA : forall x : Set.Icc a b, lower <= F x / x) :
    let m := (a + b) / 2
    |2 * Real.log (F m / m) - Real.log (F a / a) -
        Real.log (F b / b)| <=
      (C : Real) * (b - a) ^ 2 / (m * lower) +
        (C : Real) ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) := by
  dsimp
  let m := (a + b) / 2
  let A := fun x : Real => F x / x
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < m := by dsimp [m]; linarith
  have ham : a <= m := by dsimp [m]; linarith
  have hmb : m <= b := by dsimp [m]; linarith
  have hAa : lower <= A a := hlowerA ⟨a, le_rfl, hab⟩
  have hAb : lower <= A b := hlowerA ⟨b, hab, le_rfl⟩
  have hAm : lower <= A m := hlowerA ⟨m, ham, hmb⟩
  have hAavg : lower <= (A a + A b) / 2 := by linarith
  have hquot := abs_primitive_div_id_midpoint_defect_le
    hF hF0 hrho ha hab
  change |A m - (A a + A b) / 2| <=
    (C : Real) * (b - a) ^ 2 / (2 * m) at hquot
  have hfirst := abs_two_log_sub_two_log_le_of_pos_lower
    hlower hAm hAavg
  have hfirst' :
      |2 * Real.log (A m) - 2 * Real.log ((A a + A b) / 2)| <=
        (C : Real) * (b - a) ^ 2 / (m * lower) := by
    calc
      _ <= 2 * |A m - (A a + A b) / 2| / lower := hfirst
      _ <= 2 * ((C : Real) * (b - a) ^ 2 / (2 * m)) / lower := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquot (by norm_num)) hlower.le
      _ = (C : Real) * (b - a) ^ 2 / (m * lower) := by ring
  have hsecond := abs_two_log_average_sub_log_sub_log_le
    hlower hAa hAb
  have hALip := lipschitzOnWith_primitive_div_id_Ioi hF hF0 hrho
  have hdiff : |A a - A b| <= (C : Real) * (b - a) := by
    have h := hALip.dist_le_mul a (Set.mem_Ioi.mpr ha)
      b (Set.mem_Ioi.mpr hb)
    calc
      |A a - A b| = dist (A a) (A b) := by rw [Real.dist_eq]
      _ <= (C : Real) * dist a b := h
      _ = (C : Real) * (b - a) := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  have hsquare : (A a - A b) ^ 2 <=
      (C : Real) ^ 2 * (b - a) ^ 2 := by
    have hnonneg : 0 <= (C : Real) * (b - a) :=
      mul_nonneg C.coe_nonneg (sub_nonneg.mpr hab)
    have hdiff' : |A a - A b| <= |(C : Real) * (b - a)| := by
      simpa [abs_of_nonneg hnonneg] using hdiff
    have hs := (sq_le_sq).2 hdiff'
    simpa [mul_pow] using hs
  have hsecond' :
      |2 * Real.log ((A a + A b) / 2) - Real.log (A a) - Real.log (A b)| <=
        (C : Real) ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) := by
    exact hsecond.trans (div_le_div_of_nonneg_right hsquare (by positivity))
  have hdecomp :
      2 * Real.log (A m) - Real.log (A a) - Real.log (A b) =
        (2 * Real.log (A m) - 2 * Real.log ((A a + A b) / 2)) +
        (2 * Real.log ((A a + A b) / 2) - Real.log (A a) - Real.log (A b)) := by
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond')



theorem lipschitzOnWith_sixVertexCanonicalOddCounting_div_id
    {c : Real} (hc : 2 < c) (s k : Nat) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    LipschitzOnWith (sixVertexFiniteRootDensityLipschitzConstant c)
      (fun x => sixVertexBetheCountingFunction c N n p x / x)
      (Set.Ioi 0) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hn : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hpSymm : SixVertexRootSymmetric p :=
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.1
  apply lipschitzOnWith_primitive_div_id_Ioi
    (F := sixVertexBetheCountingFunction c N n p)
    (rho := sixVertexFiniteRootDensity c N n p)
  · exact fun x => hasDerivAt_sixVertexBetheCountingFunction hc hN p x
  · exact sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  · exact lipschitzWith_sixVertexFiniteRootDensity hc hN hn p



theorem abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (j : Fin (s + k + 1)) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let F := sixVertexBetheCountingFunction c N n p
    let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
    let b := sixVertexCanonicalOddRightHalfRoot hc s k j
    let m := sixVertexCanonicalOddMidpointHalfRoot hc s k j
    |2 * Real.log (F m / m) - Real.log (F a / a) - Real.log (F b / b)| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          (b - a) ^ 2 / (m * lower) +
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 *
          (b - a) ^ 2 / (4 * lower ^ 2) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let F := sixVertexBetheCountingFunction c N n p
  let rho := sixVertexFiniteRootDensity c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
  let b := sixVertexCanonicalOddRightHalfRoot hc s k j
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hn : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hpSymm : SixVertexRootSymmetric p :=
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.1
  have hF : forall x, HasDerivAt F (rho x) x := fun x =>
    hasDerivAt_sixVertexBetheCountingFunction hc hN p x
  have hF0 : F 0 = 0 :=
    sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  have hrho : LipschitzWith (sixVertexFiniteRootDensityLipschitzConstant c) rho :=
    lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  have ha : 0 < a := by
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by omega⟩
    simpa [a, sixVertexCanonicalOddLeftHalfRoot] using hmem.1
  have hab : a <= b := by
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [a, b, sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hlowerA : forall x : Set.Icc a b, lower <= F x / x := by
    intro x
    apply primitive_div_id_lower hF hF0
      (continuous_sixVertexFiniteRootDensity hc N n p)
      (ha.trans_le x.property.1)
    intro y
    simpa [rho, N, n, p] using hdensity y
  have h := abs_two_log_primitive_div_id_midpoint_sub_le
    hF hF0 hrho hlower ha hab hlowerA
  simpa [F, rho, N, n, p, a, b,
    sixVertexCanonicalOddMidpointHalfRoot] using h


theorem abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_invWidth
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (j : Fin (s + k + 1)) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let F := sixVertexBetheCountingFunction c N n p
    let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
    let b := sixVertexCanonicalOddRightHalfRoot hc s k j
    let m := sixVertexCanonicalOddMidpointHalfRoot hc s k j
    |2 * Real.log (F m / m) - Real.log (F a / a) - Real.log (F b / b)| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          ((N : Real) * lower ^ 3 * Real.pi * (2 * (j : Real) + 1)) +
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 /
          (4 * (N : Real) ^ 2 * lower ^ 4) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let F := sixVertexBetheCountingFunction c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
  let b := sixVertexCanonicalOddRightHalfRoot hc s k j
  let m := sixVertexCanonicalOddMidpointHalfRoot hc s k j
  let C : Real := sixVertexFiniteRootDensityLipschitzConstant c
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hq : 0 < 2 * (j : Real) + 1 := by positivity
  have hquant : Real.pi * (2 * (j : Real) + 1) < (N : Real) * m := by
    simpa [N, m] using
      sixVertexCanonicalOddMidpointHalfRoot_quantile_lower hc s k j
  have hm : 0 < m := by nlinarith [Real.pi_pos]
  have hab : a <= b := by
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [a, b, sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hgapNonneg : 0 <= b - a := sub_nonneg.mpr hab
  have hgap := sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower
    hc s k hlower hdensity j
  change b - a <= 1 / ((N : Real) * lower) at hgap
  have hgapSq : (b - a) ^ 2 <= (1 / ((N : Real) * lower)) ^ 2 :=
    pow_le_pow_left₀ hgapNonneg hgap 2
  have hrecip : 1 / m <= (N : Real) /
      (Real.pi * (2 * (j : Real) + 1)) := by
    exact (div_le_div_iff₀ hm (mul_pos Real.pi_pos hq)).2 (by
      simpa using hquant.le)
  have hraw :=
    abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le
      hc s k hlower hdensity j
  change |2 * Real.log (F m / m) - Real.log (F a / a) -
      Real.log (F b / b)| <=
    C * (b - a) ^ 2 / (m * lower) +
      C ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) at hraw
  calc
    _ <= C * (b - a) ^ 2 / (m * lower) +
        C ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) := hraw
    _ <= C * (1 / ((N : Real) * lower)) ^ 2 / (m * lower) +
        C ^ 2 * (1 / ((N : Real) * lower)) ^ 2 /
          (4 * lower ^ 2) := by
      gcongr
    _ = (C / ((N : Real) ^ 2 * lower ^ 3)) * (1 / m) +
        C ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4) := by
      field_simp [hN.ne', hlower.ne', hm.ne']
    _ <= (C / ((N : Real) ^ 2 * lower ^ 3)) *
          ((N : Real) / (Real.pi * (2 * (j : Real) + 1))) +
        C ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4) := by
      gcongr
    _ = C / ((N : Real) * lower ^ 3 * Real.pi *
          (2 * (j : Real) + 1)) +
        C ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4) := by
      field_simp [hN.ne', hlower.ne', Real.pi_ne_zero, hq.ne']


theorem abs_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let F := sixVertexBetheCountingFunction c N n p
    |∑ j : Fin (s + k + 1),
      (2 * Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) /
          sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
        Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) /
          sixVertexCanonicalOddLeftHalfRoot hc s k j) -
        Real.log (F (sixVertexCanonicalOddRightHalfRoot hc s k j) /
          sixVertexCanonicalOddRightHalfRoot hc s k j))| <=
      ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          ((N : Real) * lower ^ 3 * Real.pi)) *
          (1 + Real.log (s + k + 1 : Nat)) +
        (s + k + 1 : Real) *
          ((sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 /
            (4 * (N : Real) ^ 2 * lower ^ 4)) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := s + k + 1
  let C : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let A := C / ((N : Real) * lower ^ 3 * Real.pi)
  let B := C ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4)
  have hA : 0 <= A := by dsimp [A, C]; positivity
  have hB : 0 <= B := by dsimp [B, C]; positivity
  calc
    _ <= ∑ j : Fin n,
        |2 * Real.log (sixVertexBetheCountingFunction c N
              ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
              (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
              (sixVertexCanonicalOddMidpointHalfRoot hc s k j) /
            sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          Real.log (sixVertexBetheCountingFunction c N
              ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
              (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
              (sixVertexCanonicalOddLeftHalfRoot hc s k j) /
            sixVertexCanonicalOddLeftHalfRoot hc s k j) -
          Real.log (sixVertexBetheCountingFunction c N
              ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
              (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
              (sixVertexCanonicalOddRightHalfRoot hc s k j) /
            sixVertexCanonicalOddRightHalfRoot hc s k j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j : Fin n, (A / (2 * (j : Real) + 1) + B) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [A, B, C, N, n, div_div] using
        abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_invWidth
          hc s k hlower hdensity j
    _ <= ∑ j : Fin n, (A / ((j : Real) + 1) + B) := by
      apply Finset.sum_le_sum
      intro j _
      have hj : 0 <= (j : Real) := by positivity
      exact add_le_add
        (div_le_div_of_nonneg_left hA (by positivity) (by linarith)) le_rfl
    _ = A * (harmonic n : Real) + (n : Real) * B := by
      rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ j : Fin n, A / ((j : Real) + 1)) =
              ∑ j ∈ Finset.range n, A / ((j : Real) + 1) := by
            simpa using (Fin.sum_univ_eq_sum_range
              (fun j : Nat => A / ((j : Real) + 1)) n)
          _ = A * (harmonic n : Real) := by
            simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_range] at hj
            field_simp
            push_cast
            rfl
      · simp
    _ <= A * (1 + Real.log n) + (n : Real) * B := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (harmonic_le_one_add_log n) hA) le_rfl
    _ = _ := by simp [A, B, C, N, n]

theorem tendsto_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
      let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      let F := sixVertexBetheCountingFunction c N n p
      ∑ j : Fin (s + k + 1),
        (2 * Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) /
            sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) /
            sixVertexCanonicalOddLeftHalfRoot hc s k j) -
          Real.log (F (sixVertexCanonicalOddRightHalfRoot hc s k j) /
            sixVertexCanonicalOddRightHalfRoot hc s k j)))
      atTop (nhds 0) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  let C : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let C1 := C / (lower ^ 3 * Real.pi)
  let C2 := C ^ 2 / (4 * lower ^ 4)
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hC1 : 0 <= C1 := by dsimp [C1, C]; positivity
  have hC2 : 0 <= C2 := by dsimp [C2, C]; positivity
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hone : Tendsto (fun k => (1 : Real) /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hlog : Tendsto (fun k =>
      Real.log (sixVertexFourWidth (2 * s + 1) k : Real) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 1 one_ne_zero).comp hwidth
  have hmajor : Tendsto (fun k =>
      C1 * ((1 + Real.log (sixVertexFourWidth (2 * s + 1) k : Real)) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) +
      C2 / (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) := by
    have h := ((hone.add hlog).const_mul C1).add (hone.const_mul C2)
    convert h using 1
    · funext k
      ring
    · simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  filter_upwards [hfloor] with k hk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := s + k + 1
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hn : 0 < (n : Real) := by positivity
  have hnN : (n : Real) <= N := by
    exact_mod_cast (show n <= N by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega)
  have hk' : forall x, lower <=
      sixVertexFiniteRootDensity c N
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, N, sixVertexFourWidth] using hk
  have hbound :=
    abs_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le
      hc s k hlower hk'
  have hlogLe : Real.log n <= Real.log (N : Real) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hn)
      (Set.mem_Ioi.mpr hN) hnN
  rw [Real.norm_eq_abs, sub_zero]
  calc
    _ <= (C / ((N : Real) * lower ^ 3 * Real.pi)) *
          (1 + Real.log n) +
        (n : Real) * (C ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4)) := by
      simpa [C, lower, N, n] using hbound
    _ = C1 * ((1 + Real.log n) / (N : Real)) +
        C2 * ((n : Real) / (N : Real) ^ 2) := by
      dsimp [C1, C2]
      ring
    _ <= C1 * ((1 + Real.log (N : Real)) / (N : Real)) +
        C2 * (1 / (N : Real)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hC1
        apply div_le_div_of_nonneg_right _ hN.le
        linarith
      · apply mul_le_mul_of_nonneg_left _ hC2
        rw [div_le_div_iff₀ (sq_pos_of_pos hN) hN]
        nlinarith [mul_le_mul_of_nonneg_right hnN hN.le]
    _ = C1 * ((1 + Real.log (N : Real)) / (N : Real)) +
        C2 / (N : Real) := by ring

theorem tendsto_sixVertexCanonicalOddHalfFilledFiniteDensity_zero
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) 0)
      atTop (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
  let w := sixVertexRootDensityWeight c 0
  let E := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  have hw : 0 < w := sixVertexRootDensityWeight_pos hc 0
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hmajor : Tendsto (fun k => (E / w) /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hgauge := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth hc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards [hgauge] with k hk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hpoint := (abs_weightedFiniteDensity_sub_le_gauge hc p
    (sixVertexFourierPhysicalDensityMap hc) 0
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).trans hk
  have hpoint' : |w * (sixVertexFiniteRootDensity c N n p 0 -
      sixVertexFourierPhysicalDensity c hc 0)| <= E / (N : Real) := by
    simpa [w, E, N, n, p, sixVertexFourWidth,
      sixVertexFourierPhysicalDensityMap] using hpoint
  have hdiv := abs_sub_le_of_weighted_abs_sub_le_invWidth
    hN hw (le_rfl : w <= sixVertexRootDensityWeight c 0) hpoint'
  rw [Real.norm_eq_abs]
  simpa [w, E, N, n, p, sixVertexFourWidth] using hdiv



theorem two_sum_sixVertexCanonicalOddMidpoint_sub_eq_boundary_add_secondDifference
    (f : Real -> Real) {c : Real} (hc : 2 < c) (s k : Nat) :
    2 * ∑ j : Fin (s + k + 1),
        (f (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          f (sixVertexCanonicalOddLeftHalfRoot hc s k j)) =
      f (sixVertexCanonicalOddBoundaryHalfRoot hc s k
          ⟨0, Nat.succ_pos s⟩) -
        f (sixVertexCanonicalOddLeftHalfRoot hc s k
          ⟨0, by omega⟩) +
        ∑ j : Fin (s + k + 1),
          (2 * f (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
            f (sixVertexCanonicalOddLeftHalfRoot hc s k j) -
            f (sixVertexCanonicalOddRightHalfRoot hc s k j)) := by
  let n := s + k + 1
  let M := 2 * s + 1 + k + 1
  have hM : NeZero M := ⟨by dsimp [M]; omega⟩
  letI : NeZero M := hM
  let x : Nat -> Real := fun j =>
    sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
      (Fin.ofNat M j)
  have hxLeft (j : Fin n) :
      x j.val = sixVertexCanonicalOddLeftHalfRoot hc s k
        ⟨j.val, by dsimp [n] at j ⊢; omega⟩ := by
    dsimp [x, M, sixVertexCanonicalOddLeftHalfRoot]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt]
    omega
  have hxRight (j : Fin n) :
      x (j.val + 1) = sixVertexCanonicalOddRightHalfRoot hc s k
        ⟨j.val, by dsimp [n] at j ⊢; omega⟩ := by
    dsimp [x, M, sixVertexCanonicalOddRightHalfRoot]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt]
    omega
  have hxZero : x 0 = sixVertexCanonicalOddLeftHalfRoot hc s k
      ⟨0, by omega⟩ := by
    dsimp [x, M, sixVertexCanonicalOddLeftHalfRoot]
    congr 1
  have hxN : x n = sixVertexCanonicalOddBoundaryHalfRoot hc s k
      ⟨0, Nat.succ_pos s⟩ := by
    dsimp [x, n, M, sixVertexCanonicalOddBoundaryHalfRoot]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt]
    omega
  have h := two_sum_midpoint_sub_eq_endpoint_add_secondDifference n x f
  have hfin :
      2 * ∑ j : Fin n,
          (f ((x j.val + x (j.val + 1)) / 2) - f (x j.val)) =
        f (x n) - f (x 0) +
          ∑ j : Fin n,
            (2 * f ((x j.val + x (j.val + 1)) / 2) -
              f (x j.val) - f (x (j.val + 1))) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : Nat =>
      f ((x j + x (j + 1)) / 2) - f (x j)) n,
      Fin.sum_univ_eq_sum_range (fun j : Nat =>
        2 * f ((x j + x (j + 1)) / 2) - f (x j) - f (x (j + 1))) n]
    exact h
  rw [hxN, hxZero] at hfin
  simpa [n, sixVertexCanonicalOddMidpointHalfRoot, hxLeft, hxRight] using hfin

end

end StatMech.FrontierD
