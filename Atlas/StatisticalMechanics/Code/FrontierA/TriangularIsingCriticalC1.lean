/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingIntegralAnalytic
import Code.FrontierA.TriangularIsingCriticalParameter

open Filter MeasureTheory Topology
open scoped Real Interval

namespace StatMech.FrontierA

noncomputable section


def triangularIsingRaySymbolDeriv
    (J beta p q : Real) : Real :=
  4 * Real.cosh (2 * beta) * Real.sinh (2 * beta) *
      Real.cosh (2 * beta * J) +
    2 * J * Real.cosh (2 * beta) ^ 2 * Real.sinh (2 * beta * J) +
    4 * Real.sinh (2 * beta) * Real.cosh (2 * beta) *
      Real.sinh (2 * beta * J) +
    2 * J * Real.sinh (2 * beta) ^ 2 * Real.cosh (2 * beta * J) -
    2 * Real.cosh (2 * beta) * (Real.cos p + Real.cos q) -
    2 * J * Real.cosh (2 * beta * J) * Real.cos (p + q)

theorem hasDerivAt_triangularIsingSymbol_along_ray
    (J beta p q : Real) :
    HasDerivAt
      (fun b => triangularIsingSymbol b b (b * J) p q)
      (triangularIsingRaySymbolDeriv J beta p q) beta := by
  have hlin : HasDerivAt (fun b : Real => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1 <;> ring
  have hlinJ : HasDerivAt (fun b : Real => 2 * b * J) (2 * J) beta := by
    convert ((hasDerivAt_id beta).const_mul 2).mul_const J using 1 <;> ring
  have hC := (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin
  have hS := (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin
  have hCJ := (Real.hasDerivAt_cosh (2 * beta * J)).comp beta hlinJ
  have hSJ := (Real.hasDerivAt_sinh (2 * beta * J)).comp beta hlinJ
  have h := ((hC.pow 2).mul hCJ).add ((hS.pow 2).mul hSJ) |>.sub
    ((hS.mul_const (Real.cos p + Real.cos q)).add
      (hSJ.mul_const (Real.cos (p + q))))
  convert h using 1
  · ext b
    change triangularIsingSymbol b b (b * J) p q =
      Real.cosh (2 * b) ^ 2 * Real.cosh (2 * b * J) +
        Real.sinh (2 * b) ^ 2 * Real.sinh (2 * b * J) -
        (Real.sinh (2 * b) * (Real.cos p + Real.cos q) +
          Real.sinh (2 * b * J) * Real.cos (p + q))
    unfold triangularIsingSymbol
    ring
  · unfold triangularIsingRaySymbolDeriv
    simp only [Function.comp_apply, Pi.pow_apply, Nat.reduceSub, pow_one]
    ring

theorem triangularIsingRaySymbolDeriv_sub_zero
    (J beta p q : Real) :
    triangularIsingRaySymbolDeriv J beta p q -
        triangularIsingRaySymbolDeriv J beta 0 0 =
      2 * Real.cosh (2 * beta) *
          ((1 - Real.cos p) + (1 - Real.cos q)) +
        2 * J * Real.cosh (2 * beta * J) *
          (1 - Real.cos (p + q)) := by
  simp [triangularIsingRaySymbolDeriv]
  ring

theorem triangularIsingRaySymbolDeriv_zero_at_root
    {beta J : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    triangularIsingRaySymbolDeriv J beta 0 0 = 0 := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  have hP : HasDerivAt P (deriv P beta) beta :=
    (differentiableAt_triangularIsingCriticalPolynomialAlong J beta).hasDerivAt
  have hH : HasDerivAt H (deriv H beta) beta := by
    exact (by unfold H triangularIsingZeroModePrefactorAlong; fun_prop :
      DifferentiableAt Real H beta).hasDerivAt
  have hPzero : P beta = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hbeta).2 hroot
  have hright : HasDerivAt (fun b => P b ^ 2 * H b) 0 beta := by
    convert (hP.pow 2).mul hH using 1
    simp [hPzero]
  have heq : (fun b => triangularIsingSymbol b b (b * J) 0 0) =
      fun b => P b ^ 2 * H b := by
    funext b
    exact triangularIsing_zeroMode_eq_polynomialAlong_sq_mul J b
  have hright' : HasDerivAt
      (fun b => triangularIsingSymbol b b (b * J) 0 0) 0 beta := by
    rw [heq]
    exact hright
  exact (hasDerivAt_triangularIsingSymbol_along_ray J beta 0 0).unique hright'

theorem differentiable_triangularIsingRaySymbolDeriv (J p q : Real) :
    Differentiable Real (fun b => triangularIsingRaySymbolDeriv J b p q) := by
  unfold triangularIsingRaySymbolDeriv
  fun_prop




set_option maxHeartbeats 800000 in

theorem exists_triangularIsingCriticalRay_local_bounds
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ∃ U : Set Real, U ∈ nhds beta ∧ IsOpen U ∧
      ∃ m K : Real, 0 < m ∧ 0 < K ∧ ∀ b ∈ U, ∀ p q : Real,
        m * ((b - beta) ^ 2 +
            ((1 - Real.cos p) + (1 - Real.cos q))) <=
          triangularIsingSymbol b b (b * J) p q ∧
        |triangularIsingRaySymbolDeriv J b p q| <=
          K * (2 * |b - beta| +
            ((1 - Real.cos p) + (1 - Real.cos q))) := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  let D0 : Real -> Real := fun b => triangularIsingRaySymbolDeriv J b 0 0
  let g : Real -> Real := fun b =>
    if 0 <= J then Real.sinh (2 * b)
    else Real.sinh (2 * b) + 2 * Real.sinh (2 * b * J)
  have hP : HasDerivAt P (deriv P beta) beta :=
    (differentiableAt_triangularIsingCriticalPolynomialAlong J beta).hasDerivAt
  have hPne : deriv P beta ≠ 0 := by
    exact (deriv_triangularIsingCriticalPolynomialAlong_neg_at_root
      hbeta (by linarith) hroot).ne
  have hPzero : P beta = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hbeta).2 hroot
  obtain ⟨CP, hCP, hPbig⟩ := (hP.isTheta_sub hPne).isBigO_symm.exists_pos
  have hPbound : ∀ᶠ b in nhds beta, |b - beta| <= CP * |P b| := by
    have ht : Tendsto (fun b : Real => (b, beta)) (nhds beta)
        (nhds beta ×ˢ pure beta) := tendsto_id.prodMk tendsto_const_pure
    filter_upwards [ht.eventually hPbig.bound] with b hb
    simpa only [Real.norm_eq_abs, hPzero, sub_zero] using hb
  have hHbeta : 0 < H beta := by
    unfold H triangularIsingZeroModePrefactorAlong
    positivity
  have hHbound : ∀ᶠ b in nhds beta, H beta / 2 <= H b := by
    exact (continuous_triangularIsingZeroModePrefactorAlong J).continuousAt
      |>.eventually (eventually_ge_nhds (by linarith : H beta / 2 < H beta))
  have hpos : ∀ᶠ b in nhds beta, 0 < b := eventually_gt_nhds hbeta
  have hgbeta : 0 < g beta := by
    by_cases hJnonneg : 0 <= J
    · simp only [g, if_pos hJnonneg]
      exact Real.sinh_pos_iff.mpr (by linarith)
    · simp only [g, if_neg hJnonneg]
      have hs : 0 < Real.sinh (2 * beta) :=
        Real.sinh_pos_iff.mpr (by linarith)
      have hrate := hroot
      rw [triangularIsingCriticalRate] at hrate
      have harg : 2 * (beta * J) = 2 * beta * J := by ring
      rw [harg] at hrate
      have hprod : 0 < Real.sinh (2 * beta) *
          (Real.sinh (2 * beta) + 2 * Real.sinh (2 * beta * J)) := by
        nlinarith
      rcases mul_pos_iff.mp hprod with hpos | hneg
      · exact hpos.2
      · exact (lt_asymm hs hneg.1).elim
  have hgbound : ∀ᶠ b in nhds beta, g beta / 2 <= g b := by
    have hgcont : Continuous g := by
      unfold g
      split <;> fun_prop
    exact hgcont.continuousAt.eventually
      (eventually_ge_nhds (by linarith : g beta / 2 < g beta))
  have hDdiff : DifferentiableAt Real D0 beta := by
    exact differentiable_triangularIsingRaySymbolDeriv J 0 0 beta
  obtain ⟨CD, hCD, hDbig⟩ := hDdiff.isBigO_sub.exists_pos
  have hDzero : D0 beta = 0 :=
    triangularIsingRaySymbolDeriv_zero_at_root hbeta hroot
  have hDbound : ∀ᶠ b in nhds beta, |D0 b| <= CD * |b - beta| := by
    filter_upwards [hDbig.bound] with b hb
    simpa only [Real.norm_eq_abs, hDzero, sub_zero] using hb
  let Cmom : Real :=
    2 * (|Real.cosh (2 * beta)| + 1) +
      4 * |J| * (|Real.cosh (2 * beta * J)| + 1)
  have hCmom : 0 < Cmom := by
    unfold Cmom
    positivity
  have hcosh : ∀ᶠ b in nhds beta,
      |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 := by
    have hc : Continuous (fun b : Real => |Real.cosh (2 * b)|) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
  have hcoshJ : ∀ᶠ b in nhds beta,
      |Real.cosh (2 * b * J)| < |Real.cosh (2 * beta * J)| + 1 := by
    have hc : Continuous (fun b : Real => |Real.cosh (2 * b * J)|) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
  let a : Real := H beta / (2 * CP ^ 2)
  let c : Real := g beta / 2
  let m : Real := min a c
  let K : Real := max (CD + 1) Cmom
  have ha : 0 < a := by unfold a; positivity
  have hc : 0 < c := by
    unfold c
    positivity
  have hm : 0 < m := by simp only [m, lt_min_iff]; exact ⟨ha, hc⟩
  have hK : 0 < K := lt_of_lt_of_le hCmom (le_max_right _ _)
  let S : Set Real := {b | 0 < b ∧
      |b - beta| <= CP * |P b| ∧
      H beta / 2 <= H b ∧
      c <= g b ∧
      |D0 b| <= CD * |b - beta| ∧
      |Real.cosh (2 * b)| <= |Real.cosh (2 * beta)| + 1 ∧
      |Real.cosh (2 * b * J)| <= |Real.cosh (2 * beta * J)| + 1}
  have hS : S ∈ nhds beta := by
    filter_upwards [hpos, hPbound, hHbound, hgbound, hDbound,
      hcosh, hcoshJ] with b hb hp hH hs hD hC hCJ
    exact ⟨hb, hp, hH, hs, hD, hC.le, hCJ.le⟩
  obtain ⟨U, hUS, hUopen, hbetaU⟩ := mem_nhds_iff.mp hS
  have hU : U ∈ nhds beta := hUopen.mem_nhds hbetaU
  refine ⟨U, hU, hUopen, m, K, hm, hK, ?_⟩
  intro b hb p q
  have hbS := hUS hb
  let A : Real := (1 - Real.cos p) + (1 - Real.cos q)
  let B : Real := 1 - Real.cos (p + q)
  have hA : 0 <= A := by
    unfold A
    nlinarith [Real.cos_le_one p, Real.cos_le_one q]
  have hB : 0 <= B := by unfold B; linarith [Real.cos_le_one (p + q)]
  have hBA : B <= 2 * A := one_sub_cos_add_le_two_sum p q
  have hPsq : (b - beta) ^ 2 <= CP ^ 2 * P b ^ 2 := by
    have hsquare := sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hCP.le (abs_nonneg _)) |>.2 hbS.2.1
    nlinarith [hsquare, sq_abs (b - beta), sq_abs (P b)]
  have hzero : a * (b - beta) ^ 2 <=
      triangularIsingSymbol b b (b * J) 0 0 := by
    rw [triangularIsing_zeroMode_eq_polynomialAlong_sq_mul]
    have hH : H beta / 2 <= H b := hbS.2.2.1
    have hCP0 : CP ^ 2 > 0 := sq_pos_of_pos hCP
    unfold a
    calc
      H beta / (2 * CP ^ 2) * (b - beta) ^ 2 <=
          H beta / (2 * CP ^ 2) * (CP ^ 2 * P b ^ 2) := by
            gcongr
      _ = H beta / 2 * P b ^ 2 := by
            field_simp [hCP.ne']
      _ <= P b ^ 2 * H b := by
            nlinarith [sq_nonneg (P b)]
  have hmA : m * ((b - beta) ^ 2 + A) <=
      a * (b - beta) ^ 2 + c * A := by
    have hma : m <= a := min_le_left _ _
    have hmc : m <= c := min_le_right _ _
    nlinarith [sq_nonneg (b - beta)]
  have hexcess := triangularIsingSymbol_sub_zero b (b * J) p q
  change triangularIsingSymbol b b (b * J) p q -
      triangularIsingSymbol b b (b * J) 0 0 =
        Real.sinh (2 * b) * A + Real.sinh (2 * (b * J)) * B at hexcess
  have hmomentumLower : c * A <=
      Real.sinh (2 * b) * A + Real.sinh (2 * (b * J)) * B := by
    have hg : c <= g b := hbS.2.2.2.1
    by_cases hJnonneg : 0 <= J
    · have hgeq : g b = Real.sinh (2 * b) := by
        simp only [g, if_pos hJnonneg]
      have hr : 0 <= Real.sinh (2 * (b * J)) :=
        Real.sinh_nonneg_iff.mpr (by
          exact mul_nonneg (by norm_num)
            (mul_nonneg hbS.1.le hJnonneg))
      have hsA := mul_le_mul_of_nonneg_right (hgeq ▸ hg) hA
      nlinarith [mul_nonneg hr hB]
    · have hJneg : J < 0 := lt_of_not_ge hJnonneg
      have hr : Real.sinh (2 * (b * J)) < 0 :=
        Real.sinh_neg_iff.mpr (by
          have := mul_neg_of_pos_of_neg hbS.1 hJneg
          linarith)
      have hgeq : g b = Real.sinh (2 * b) +
          2 * Real.sinh (2 * b * J) := by
        simp only [g, if_neg hJnonneg]
      have hrB : 2 * Real.sinh (2 * (b * J)) * A <=
          Real.sinh (2 * (b * J)) * B := by
        have := mul_le_mul_of_nonpos_left hBA hr.le
        nlinarith
      have hgA := mul_le_mul_of_nonneg_right hg hA
      rw [hgeq] at hgA
      have harg : 2 * (b * J) = 2 * b * J := by ring
      rw [harg] at hrB ⊢
      linarith [hgA]
  have hlower : a * (b - beta) ^ 2 + c * A <=
      triangularIsingSymbol b b (b * J) p q := by
    linarith [hzero, hexcess, hmomentumLower]
  refine ⟨hmA.trans hlower, ?_⟩
  have hdiff := triangularIsingRaySymbolDeriv_sub_zero J b p q
  have hmomentum :
      |triangularIsingRaySymbolDeriv J b p q - D0 b| <= Cmom * A := by
    rw [hdiff]
    have hterm1 : |2 * Real.cosh (2 * b) * A| <=
        (2 * (|Real.cosh (2 * beta)| + 1)) * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
        abs_of_nonneg hA]
      gcongr
      exact hbS.2.2.2.2.2.1
    have hterm2 : |2 * J * Real.cosh (2 * b * J) * B| <=
        (4 * |J| * (|Real.cosh (2 * beta * J)| + 1)) * A := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2), abs_of_nonneg hB]
      have hcJ := hbS.2.2.2.2.2.2
      calc
        2 * |J| * |Real.cosh (2 * b * J)| * B <=
            2 * |J| * (|Real.cosh (2 * beta * J)| + 1) * B := by gcongr
        _ <= 2 * |J| * (|Real.cosh (2 * beta * J)| + 1) * (2 * A) := by gcongr
        _ = _ := by ring
    calc
      |_ + _| <= |2 * Real.cosh (2 * b) * A| +
          |2 * J * Real.cosh (2 * b * J) * B| := abs_add_le _ _
      _ <= Cmom * A := by unfold Cmom; linarith
  have hD0 : |D0 b| <= (CD + 1) * |b - beta| := by
    have := hbS.2.2.2.2.1
    nlinarith [abs_nonneg (b - beta)]
  have htotal : |triangularIsingRaySymbolDeriv J b p q| <=
      (CD + 1) * |b - beta| + Cmom * A := by
    calc
      |triangularIsingRaySymbolDeriv J b p q| =
          |(triangularIsingRaySymbolDeriv J b p q - D0 b) + D0 b| := by ring_nf
      _ <= |triangularIsingRaySymbolDeriv J b p q - D0 b| + |D0 b| :=
        abs_add_le _ _
      _ <= _ := by linarith
  have hCDK : CD + 1 <= K := le_max_left _ _
  have hCK : Cmom <= K := le_max_right _ _
  have hK0 : 0 <= K := hK.le
  dsimp [A] at htotal ⊢
  calc
    |triangularIsingRaySymbolDeriv J b p q| <=
        (CD + 1) * |b - beta| + Cmom *
          ((1 - Real.cos p) + (1 - Real.cos q)) := htotal
    _ <= K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))) := by
      nlinarith [abs_nonneg (b - beta), hA]



def triangularIsingRayLogDeriv (J b p q : Real) : Real :=
  triangularIsingRaySymbolDeriv J b p q /
    triangularIsingSymbol b b (b * J) p q

theorem hasDerivAt_log_triangularIsingSymbol_along_ray
    {J b p q : Real}
    (hpos : 0 < triangularIsingSymbol b b (b * J) p q) :
    HasDerivAt
      (fun t => Real.log (triangularIsingSymbol t t (t * J) p q))
      (triangularIsingRayLogDeriv J b p q) b := by
  simpa only [triangularIsingRayLogDeriv] using
    (hasDerivAt_triangularIsingSymbol_along_ray J b p q).log hpos.ne'


def triangularIsingCriticalFirstMajorant
    (m K x y : Real) : Real :=
  (K / m) *
    (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
      StatMech.Onsager.ons_criticalOneDimMajorant y + 1)

theorem triangularIsingRayLogDeriv_abs_le_criticalMajorant
    {beta J m K b x y : Real}
    (hm : 0 < m) (hK : 0 < K)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hlower : m * ((b - beta) ^ 2 +
        ((1 - Real.cos x) + (1 - Real.cos y))) <=
      triangularIsingSymbol b b (b * J) x y)
    (hderiv : |triangularIsingRaySymbolDeriv J b x y| <=
      K * (2 * |b - beta| +
        ((1 - Real.cos x) + (1 - Real.cos y)))) :
    |triangularIsingRayLogDeriv J b x y| <=
      triangularIsingCriticalFirstMajorant m K x y := by
  let A : Real := 2 - Real.cos x - Real.cos y
  let delta : Real := b - beta
  have hAeq : (1 - Real.cos x) + (1 - Real.cos y) = A := by
    unfold A
    ring
  rw [hAeq] at hlower hderiv
  have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hA : 0 < A := by
    exact (div_pos hxy hpi).trans_le
      (StatMech.Onsager.ons_criticalDenom_lower_abs_mul hx hy)
  have hden0 : 0 < m * (delta ^ 2 + A) := by positivity
  have hsymbol : 0 < triangularIsingSymbol b b (b * J) x y := by
    apply hden0.trans_le
    simpa only [A, delta] using hlower
  change |triangularIsingRaySymbolDeriv J b x y /
      triangularIsingSymbol b b (b * J) x y| <= _
  rw [abs_div, abs_of_pos hsymbol]
  have hratio := StatMech.Onsager.ons_delta_ratio_le_inv_sqrt
    (delta := delta) hA
  have hfirst :
      |triangularIsingRaySymbolDeriv J b x y| /
          triangularIsingSymbol b b (b * J) x y <=
        (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := by
    calc
      _ <= (K * (2 * |delta| + A)) /
          (m * (delta ^ 2 + A)) := by
            apply div_le_div₀
            · positivity
            · simpa only [A, delta] using hderiv
            · exact hden0
            · simpa only [A, delta] using hlower
      _ = (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := by
            field_simp [hm.ne', (show delta ^ 2 + A ≠ 0 by positivity)]
            <;> ring
  calc
    _ <= (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := hfirst
    _ <= (K / m) * (1 / Real.sqrt A + 1) := by
      gcongr
    _ <= (K / m) *
        (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
          StatMech.Onsager.ons_criticalOneDimMajorant y + 1) := by
      gcongr
      simpa only [A, StatMech.Onsager.ons_criticalOneDimMajorant] using
        StatMech.Onsager.ons_inv_sqrt_criticalDenom_le_product
          hx hy hx0 hy0
    _ = triangularIsingCriticalFirstMajorant m K x y := rfl

theorem triangularIsingCriticalFirstMajorant_inner_intervalIntegrable
    {m K : Real} (x : Real) :
    IntervalIntegrable (triangularIsingCriticalFirstMajorant m K x)
      volume (-Real.pi) Real.pi := by
  unfold triangularIsingCriticalFirstMajorant
  exact (((StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul
    (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x)).add
      intervalIntegral.intervalIntegrable_const).const_mul (K / m))

theorem triangularIsingCriticalFirstMajorant_inner_integral
    (m K x : Real) :
    (∫ y in (-Real.pi)..Real.pi,
      triangularIsingCriticalFirstMajorant m K x y) =
      (K / m) *
        (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
          (∫ y in (-Real.pi)..Real.pi,
            StatMech.Onsager.ons_criticalOneDimMajorant y) +
          2 * Real.pi) := by
  have hfirst : IntervalIntegrable
      (fun y => Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
        StatMech.Onsager.ons_criticalOneDimMajorant y)
      volume (-Real.pi) Real.pi :=
    StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul _
  unfold triangularIsingCriticalFirstMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hfirst
    intervalIntegral.intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  ring

def triangularIsingCriticalFirstOuterMajorant
    (m K x : Real) : Real :=
  (K / m) *
    (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
      (∫ y in (-Real.pi)..Real.pi,
        StatMech.Onsager.ons_criticalOneDimMajorant y) + 2 * Real.pi)

theorem triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
    {m K : Real} :
    IntervalIntegrable (triangularIsingCriticalFirstOuterMajorant m K)
      volume (-Real.pi) Real.pi := by
  let Q : Real := ∫ y in (-Real.pi)..Real.pi,
    StatMech.Onsager.ons_criticalOneDimMajorant y
  have hterm : IntervalIntegrable
      (fun x => Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x * Q)
      volume (-Real.pi) Real.pi := by
    convert StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul
      (Real.pi * Q) using 1
    ext x
    ring
  unfold triangularIsingCriticalFirstOuterMajorant
  change IntervalIntegrable
    (fun x => (K / m) *
      (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x * Q +
        2 * Real.pi)) volume (-Real.pi) Real.pi
  exact (hterm.add intervalIntegral.intervalIntegrable_const).const_mul (K / m)

def triangularIsingRaySymbolAbsBound (J b : Real) : Real :=
  |Real.cosh (2 * b)| ^ 2 * |Real.cosh (2 * b * J)| +
    |Real.sinh (2 * b)| ^ 2 * |Real.sinh (2 * b * J)| +
    2 * |Real.sinh (2 * b)| + |Real.sinh (2 * b * J)| + 1

theorem triangularIsingRaySymbolAbsBound_pos (J b : Real) :
    0 < triangularIsingRaySymbolAbsBound J b := by
  unfold triangularIsingRaySymbolAbsBound
  positivity

theorem triangularIsingSymbol_le_rayAbsBound (J b p q : Real) :
    triangularIsingSymbol b b (b * J) p q <=
      triangularIsingRaySymbolAbsBound J b := by
  have hcp := Real.abs_cos_le_one p
  have hcq := Real.abs_cos_le_one q
  have hcpq := Real.abs_cos_le_one (p + q)
  unfold triangularIsingSymbol triangularIsingRaySymbolAbsBound
  have hraw := le_trans (le_abs_self
    (Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J)) +
      Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J)) -
      (Real.sinh (2 * b) * Real.cos p + Real.sinh (2 * b) * Real.cos q +
        Real.sinh (2 * (b * J)) * Real.cos (p + q))))
    (abs_sub _ _)
  calc
    _ <= |Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J)) +
        Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J))| +
      |Real.sinh (2 * b) * Real.cos p + Real.sinh (2 * b) * Real.cos q +
        Real.sinh (2 * (b * J)) * Real.cos (p + q)| := hraw
    _ <= (|Real.cosh (2 * b)| ^ 2 * |Real.cosh (2 * (b * J))| +
          |Real.sinh (2 * b)| ^ 2 * |Real.sinh (2 * (b * J))|) +
        (2 * |Real.sinh (2 * b)| + |Real.sinh (2 * (b * J))|) := by
      calc
        _ <= (|Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J))| +
              |Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J))|) +
            ((|Real.sinh (2 * b) * Real.cos p| +
                |Real.sinh (2 * b) * Real.cos q|) +
              |Real.sinh (2 * (b * J)) * Real.cos (p + q)|) := by
          gcongr
          · exact abs_add_le _ _
          · calc
              |(Real.sinh (2 * b) * Real.cos p +
                    Real.sinh (2 * b) * Real.cos q) +
                  Real.sinh (2 * (b * J)) * Real.cos (p + q)| <=
                  |Real.sinh (2 * b) * Real.cos p +
                    Real.sinh (2 * b) * Real.cos q| +
                  |Real.sinh (2 * (b * J)) * Real.cos (p + q)| :=
                    abs_add_le _ _
              _ <= (|Real.sinh (2 * b) * Real.cos p| +
                    |Real.sinh (2 * b) * Real.cos q|) +
                  |Real.sinh (2 * (b * J)) * Real.cos (p + q)| :=
                    by
                      have hab := abs_add_le
                        (Real.sinh (2 * b) * Real.cos p)
                        (Real.sinh (2 * b) * Real.cos q)
                      linarith
        _ <= _ := by
          simp only [abs_mul]
          have hpM : |Real.sinh (2 * b)| * |Real.cos p| <=
              |Real.sinh (2 * b)| :=
            mul_le_of_le_one_right (abs_nonneg _) hcp
          have hqM : |Real.sinh (2 * b)| * |Real.cos q| <=
              |Real.sinh (2 * b)| :=
            mul_le_of_le_one_right (abs_nonneg _) hcq
          have hpqM : |Real.sinh (2 * (b * J))| * |Real.cos (p + q)| <=
              |Real.sinh (2 * (b * J))| :=
            mul_le_of_le_one_right (abs_nonneg _) hcpq
          ring_nf at hpM hqM hpqM ⊢
          nlinarith
    _ <= _ := by
      have harg : 2 * (b * J) = 2 * b * J := by ring
      rw [harg]
      linarith

def triangularIsingCriticalLogBound (m J b y : Real) : Real :=
  |Real.log m| + |Real.log (triangularIsingRaySymbolAbsBound J b)| +
    |Real.log (1 - Real.cos y)|

theorem triangularIsingCriticalLogBound_intervalIntegrable
    {m J b : Real} :
    IntervalIntegrable (triangularIsingCriticalLogBound m J b)
      volume (-Real.pi) Real.pi := by
  have hmer : MeromorphicOn (fun y : Real => 1 - Real.cos y)
      [[-Real.pi, Real.pi]] :=
    (analyticOnNhd_const.sub Real.analyticOnNhd_cos).meromorphicOn
  have hlog : IntervalIntegrable
      (fun y : Real => |Real.log (1 - Real.cos y)|)
      volume (-Real.pi) Real.pi := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      (hmer.intervalIntegrable_log).norm
  unfold triangularIsingCriticalLogBound
  exact (intervalIntegral.intervalIntegrable_const.add
    intervalIntegral.intervalIntegrable_const).add hlog

theorem triangularIsing_logSymbol_abs_le_criticalLogBound
    {beta J m b x y : Real} (hm : 0 < m)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi) (hy0 : y ≠ 0)
    (hlower : m * ((b - beta) ^ 2 +
        ((1 - Real.cos x) + (1 - Real.cos y))) <=
      triangularIsingSymbol b b (b * J) x y) :
    |Real.log (triangularIsingSymbol b b (b * J) x y)| <=
      triangularIsingCriticalLogBound m J b y := by
  have hB0 : 0 <= 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have hB : 0 < 1 - Real.cos y := by
    apply lt_of_le_of_ne hB0
    intro hz
    have hcos : Real.cos y = 1 := by linarith
    have habs : |y| <= Real.pi := abs_le.mpr hy
    exact hy0 ((Real.cos_eq_one_iff_of_lt_of_lt
      (by rw [abs_le] at habs; linarith [Real.pi_pos])
      (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos)
  have hbase : m * (1 - Real.cos y) <=
      triangularIsingSymbol b b (b * J) x y := by
    have hA : 0 <= 1 - Real.cos x := by linarith [Real.cos_le_one x]
    have hdelta : 0 <= (b - beta) ^ 2 := sq_nonneg _
    nlinarith [hlower]
  have hpos : 0 < triangularIsingSymbol b b (b * J) x y :=
    (mul_pos hm hB).trans_le hbase
  have hupper := triangularIsingSymbol_le_rayAbsBound J b x y
  have hC := triangularIsingRaySymbolAbsBound_pos J b
  have hlogLower := Real.log_le_log (mul_pos hm hB) hbase
  rw [Real.log_mul hm.ne' hB.ne'] at hlogLower
  have hlogUpper := Real.log_le_log hpos hupper
  rw [abs_le]
  constructor
  · unfold triangularIsingCriticalLogBound
    have hmabs := neg_abs_le (Real.log m)
    have hBabs := neg_abs_le (Real.log (1 - Real.cos y))
    have hCabs := abs_nonneg (Real.log (triangularIsingRaySymbolAbsBound J b))
    linarith
  · unfold triangularIsingCriticalLogBound
    have hCm := le_abs_self (Real.log (triangularIsingRaySymbolAbsBound J b))
    have hmabs := abs_nonneg (Real.log m)
    have hBabs := abs_nonneg (Real.log (1 - Real.cos y))
    linarith

theorem triangularIsingSymbol_pos_of_critical_local_bounds
    {beta J m K : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    {b x y : Real} (hb : b ∈ U)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < triangularIsingSymbol b b (b * J) x y := by
  have hA : 0 < (1 - Real.cos x) + (1 - Real.cos y) := by
    have h := StatMech.Onsager.ons_criticalDenom_pos_of_mem_Icc_left
      hx hx0 (y := y)
    linarith
  have hlower := (hbounds b hb x y).1
  exact (mul_pos hm (by positivity :
    0 < (b - beta) ^ 2 + ((1 - Real.cos x) + (1 - Real.cos y)))).trans_le
    hlower

theorem continuous_triangularIsing_log_right_of_critical_local_bounds
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y =>
      Real.log (triangularIsingSymbol b b (b * J) x y)) := by
  apply Continuous.log (by unfold triangularIsingSymbol; fun_prop)
  intro y
  exact (triangularIsingSymbol_pos_of_critical_local_bounds
    hm hbounds hb hx hx0 (y := y)).ne'

theorem continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => triangularIsingRayLogDeriv J b x y) := by
  unfold triangularIsingRayLogDeriv
  apply Continuous.div
  · unfold triangularIsingRaySymbolDeriv
    fun_prop
  · unfold triangularIsingSymbol
    fun_prop
  · intro y
    exact (triangularIsingSymbol_pos_of_critical_local_bounds
      hm hbounds hb hx hx0 (y := y)).ne'

theorem continuous_triangularIsing_criticalInnerLog
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    Continuous (fun x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol b b (b * J) x y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalLogBound m J b)
  · filter_upwards [] with x'
    exact (Real.measurable_log.comp (by
      unfold triangularIsingSymbol
      fun_prop)).aestronglyMeasurable
  · filter_upwards [] with x'
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsing_logSymbol_abs_le_criticalLogBound hm hy hy0
        (hbounds b hb x' y).1
  · exact triangularIsingCriticalLogBound_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    have hB : 0 < 1 - Real.cos y := by
      have hB0 : 0 <= 1 - Real.cos y := by linarith [Real.cos_le_one y]
      apply lt_of_le_of_ne hB0
      intro hz
      have hcos : Real.cos y = 1 := by linarith
      have habs : |y| <= Real.pi := abs_le.mpr hy
      exact hy0 ((Real.cos_eq_one_iff_of_lt_of_lt
        (by rw [abs_le] at habs; linarith [Real.pi_pos])
        (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos)
    have hpos : 0 < triangularIsingSymbol b b (b * J) x y := by
      have hlower := (hbounds b hb x y).1
      have hxnonneg : 0 <= 1 - Real.cos x := by
        linarith [Real.cos_le_one x]
      have hsum : 0 < (b - beta) ^ 2 +
          ((1 - Real.cos x) + (1 - Real.cos y)) := by
        nlinarith [sq_nonneg (b - beta)]
      exact (mul_pos hm hsum).trans_le hlower
    have hc : ContinuousAt
        (fun x' => triangularIsingSymbol b b (b * J) x' y) x := by
      unfold triangularIsingSymbol
      fun_prop
    simpa only [Function.comp_apply] using hc.log hpos.ne'

theorem hasDerivAt_triangularIsing_criticalInnerIntegral
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt
      (fun t => ∫ y in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol t t (t * J) x y))
      (∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => Real.log (triangularIsingSymbol t t (t * J) x y))
    (F' := fun t y => triangularIsingRayLogDeriv J t x y)
    (bound := triangularIsingCriticalFirstMajorant m K x) hs
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_log_right_of_critical_local_bounds
      hm hbounds ht hx hx0).aestronglyMeasurable
  · exact (continuous_triangularIsing_log_right_of_critical_local_bounds
      hm hbounds hb hx hx0).intervalIntegrable _ _
  · exact (continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
      hm hbounds hb hx hx0).aestronglyMeasurable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI t ht
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsingRayLogDeriv_abs_le_criticalMajorant hm hK hx hy hx0 hy0
        (hbounds t ht x y).1 (hbounds t ht x y).2
  · exact triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI t ht
    exact hasDerivAt_log_triangularIsingSymbol_along_ray
      (triangularIsingSymbol_pos_of_critical_local_bounds
        hm hbounds ht hx hx0 (y := y))

theorem triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable
    (J b : Real) :
    AEStronglyMeasurable
      (fun x => ∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y)
      (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
  let mu := volume.restrict (Set.Ioc (-Real.pi) Real.pi)
  have hjoint : AEStronglyMeasurable
      (fun p : Real × Real => triangularIsingRayLogDeriv J b p.1 p.2)
      (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    unfold triangularIsingRayLogDeriv triangularIsingRaySymbolDeriv
      triangularIsingSymbol
    fun_prop
  have hi := hjoint.integral_prod_right'
  have hpi : -Real.pi <= Real.pi := by linarith [Real.pi_pos]
  simpa only [mu, intervalIntegral.integral_of_le hpi,
    Set.uIoc_of_le hpi] using hi

theorem triangularIsing_criticalInnerLogDeriv_norm_le
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ‖∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J b x y‖ <=
      triangularIsingCriticalFirstOuterMajorant m K x := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun y => triangularIsingRayLogDeriv J b x y)
    (g := triangularIsingCriticalFirstMajorant m K x)
    (show -Real.pi <= Real.pi by linarith [Real.pi_pos]) (by
      filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
      have hy : y ∈ Set.Icc (-Real.pi) Real.pi := ⟨hyI.1.le, hyI.2⟩
      simpa only [Real.norm_eq_abs] using
        triangularIsingRayLogDeriv_abs_le_criticalMajorant
          hm hK hx hy hx0 hy0 (hbounds b hb x y).1 (hbounds b hb x y).2)
    (triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x)
  rw [triangularIsingCriticalFirstMajorant_inner_integral] at hnorm
  exact hnorm

theorem hasDerivAt_triangularIsing_criticalDoubleIntegral
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    HasDerivAt
      (fun t => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol t t (t * J) x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J b x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol t t (t * J) x y))
    (F' := fun t x => ∫ y in (-Real.pi)..Real.pi,
      triangularIsingRayLogDeriv J t x y)
    (bound := triangularIsingCriticalFirstOuterMajorant m K) hs
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_criticalInnerLog hm hbounds ht).aestronglyMeasurable
  · exact (continuous_triangularIsing_criticalInnerLog hm hbounds hb).intervalIntegrable _ _
  · exact triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable J b
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI t ht
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact triangularIsing_criticalInnerLogDeriv_norm_le
      hm hK hbounds ht hx hx0
  · exact triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI t ht
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact hasDerivAt_triangularIsing_criticalInnerIntegral
      hm hK hUopen hbounds ht hx hx0

theorem continuousAt_triangularIsing_criticalInnerLogDeriv
    {beta J m K b x : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt
      (fun t => ∫ y in (-Real.pi)..Real.pi,
        triangularIsingRayLogDeriv J t x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalFirstMajorant m K x)
  · filter_upwards [hs] with t ht
    exact (continuous_triangularIsing_logDeriv_right_of_critical_local_bounds
      hm hbounds ht hx hx0).aestronglyMeasurable
  · filter_upwards [hs] with t ht
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      triangularIsingRayLogDeriv_abs_le_criticalMajorant
        hm hK hx hy hx0 hy0 (hbounds t ht x y).1 (hbounds t ht x y).2
  · exact triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI
    have hpos := triangularIsingSymbol_pos_of_critical_local_bounds
      hm hbounds hb hx hx0 (y := y)
    unfold triangularIsingRayLogDeriv
    apply ContinuousAt.div
    · unfold triangularIsingRaySymbolDeriv
      fun_prop
    · unfold triangularIsingSymbol
      fun_prop
    · exact hpos.ne'

theorem continuousAt_triangularIsing_criticalDoubleLogDeriv
    {beta J m K b : Real} {U : Set Real}
    (hm : 0 < m) (hK : 0 < K) (hUopen : IsOpen U)
    (hbounds : ∀ b ∈ U, ∀ p q : Real,
      m * ((b - beta) ^ 2 +
          ((1 - Real.cos p) + (1 - Real.cos q))) <=
        triangularIsingSymbol b b (b * J) p q ∧
      |triangularIsingRaySymbolDeriv J b p q| <=
        K * (2 * |b - beta| +
          ((1 - Real.cos p) + (1 - Real.cos q))))
    (hb : b ∈ U) :
    ContinuousAt
      (fun t => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J t x y) b := by
  have hs : U ∈ nhds b := hUopen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (triangularIsingCriticalFirstOuterMajorant m K)
  · exact Filter.Eventually.of_forall
      (triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable J)
  · filter_upwards [hs] with t ht
    filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact triangularIsing_criticalInnerLogDeriv_norm_le
      hm hK hbounds ht hx hx0
  · exact triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
  · filter_upwards [StatMech.Onsager.ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact continuousAt_triangularIsing_criticalInnerLogDeriv
      hm hK hUopen hbounds hb hx hx0



theorem triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ContDiffAt Real 1
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
  obtain ⟨U, hUnhds, hUopen, m, K, hm, hK, hbounds⟩ :=
    exists_triangularIsingCriticalRay_local_bounds hbeta hJ hroot
  let d : Real -> Real := fun b =>
    -(1 / (8 * Real.pi ^ 2)) *
      ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          triangularIsingRayLogDeriv J b x y
  let f' : Real -> Real →L[Real] Real := fun b =>
    d b • ContinuousLinearMap.id Real Real
  have hderiv : ∀ b ∈ U,
      HasDerivAt (fun t => triangularIsingFreeEnergyValue t t (t * J))
        (d b) b := by
    intro b hb
    have hdouble := hasDerivAt_triangularIsing_criticalDoubleIntegral
      hm hK hUopen hbounds hb
    unfold triangularIsingFreeEnergyValue
    have hconst := hasDerivAt_const b (-Real.log 2)
    have hscaled := hdouble.const_mul (1 / (8 * Real.pi ^ 2))
    simpa only [d, zero_sub, neg_mul] using hconst.sub hscaled
  rw [contDiffAt_one_iff]
  refine ⟨f', U, hUnhds, ?_, ?_⟩
  · have hd : ContinuousOn d U := by
      intro b hb
      exact (continuousAt_triangularIsing_criticalDoubleLogDeriv
        hm hK hUopen hbounds hb).const_mul
          (-(1 / (8 * Real.pi ^ 2))) |>.continuousWithinAt
    exact hd.smul continuousOn_const
  · intro b hb
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa only [f', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hderiv b hb

theorem triangularIsingFreeEnergyValue_contDiffAt_one_of_nonnegative_root
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    ContDiffAt Real 1
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
    hbeta (by linarith) hroot

end

end StatMech.FrontierA
