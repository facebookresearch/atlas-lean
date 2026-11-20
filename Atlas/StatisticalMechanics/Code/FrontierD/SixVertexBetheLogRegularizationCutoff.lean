/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRegularizedLogBulk
import Code.FrontierD.SixVertexBetheCanonicalEvenOffsetLinear
import Code.FrontierD.SixVertexBetheCanonicalPerronBulk





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexBetheLogRegularizationError
    (c epsilon x : Real) : Real :=
  sixVertexBetheLogNormKernel c x -
    sixVertexRegularizedBetheLogKernel c epsilon x

theorem hasDerivAt_sixVertexBetheLogRegularizationError
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hx : x ≠ 0) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    HasDerivAt (sixVertexBetheLogRegularizationError c epsilon)
      (sixVertexBetheLogNormDerivative c x -
        sixVertexRegularizedBetheLogNormDerivative c epsilon x) x := by
  exact (hasDerivAt_sixVertexBetheLogNormKernel hc hx hxIcc).sub
    (hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon)

private theorem denominator_lower_quadratic
    {x : Real} (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    4 * x ^ 2 / Real.pi ^ 2 <= 2 - 2 * Real.cos x := by
  let u := x / 2
  have huIcc : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [u]
    constructor <;> linarith [hxIcc.1, hxIcc.2]
  have hsine : 2 / Real.pi * |u| <= |Real.sin u| :=
    Real.mul_abs_le_abs_sin (abs_le.2 huIcc)
  have hsquare := sq_le_sq₀ (by positivity : 0 <= 2 / Real.pi * |u|)
    (abs_nonneg (Real.sin u)) |>.2 hsine
  rw [show 2 - 2 * Real.cos x = 4 * Real.sin u ^ 2 by
    rw [show x = 2 * u by dsimp [u]; ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq u]]
  have hxhalf : |x / 2| ^ 2 = x ^ 2 / 4 := by
    rw [sq_abs]
    ring
  dsimp [u] at hsquare ⊢
  rw [mul_pow, hxhalf, sq_abs] at hsquare
  field_simp [Real.pi_ne_zero] at hsquare ⊢
  nlinarith

theorem abs_sixVertexBetheLogRegularizationError_derivative_le_singular
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hx : x ≠ 0) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexBetheLogNormDerivative c x -
        sixVertexRegularizedBetheLogNormDerivative c epsilon x| <=
      Real.pi / |x| := by
  let B := 2 - 2 * Real.cos x
  have hB : 0 < B := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [<- Real.cos_abs, <- Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (abs_le.mpr hxIcc)
        (abs_pos.mpr hx)
    linarith
  have hreg : |Real.sin x / (B + epsilon)| <= |Real.sin x / B| := by
    rw [abs_div, abs_div, abs_of_pos hB, abs_of_pos (add_pos hB hepsilon)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hB
      (le_add_of_nonneg_right hepsilon.le)
  have hbase := abs_mul_sixVertexBetheLogNormDenominatorDerivative_le hx hxIcc
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsing : |Real.sin x / B| <= Real.pi / (2 * |x|) := by
    rw [abs_mul] at hbase
    have h := (le_div_iff₀ hxabs).2 (by
      calc
        |Real.sin x / B| * |x| = |x| * |Real.sin x / B| := mul_comm _ _
        _ <= Real.pi / 2 := by simpa [B] using hbase)
    simpa [div_div] using h
  unfold sixVertexBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormDerivative
  dsimp [B] at hreg hsing ⊢
  let R := -(c ^ 2 - 1) * Real.sin x /
    ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x)
  change |R - Real.sin x / (2 - 2 * Real.cos x) -
    (R - Real.sin x / (2 - 2 * Real.cos x + epsilon))| <= _
  rw [show R - Real.sin x / (2 - 2 * Real.cos x) -
      (R - Real.sin x / (2 - 2 * Real.cos x + epsilon)) =
    -(Real.sin x / (2 - 2 * Real.cos x)) +
      Real.sin x / (2 - 2 * Real.cos x + epsilon) by ring]
  calc
    |_ + _| <= |Real.sin x / (2 - 2 * Real.cos x)| +
        |Real.sin x / (2 - 2 * Real.cos x + epsilon)| := by
      simpa using abs_add_le
        (-(Real.sin x / (2 - 2 * Real.cos x)))
        (Real.sin x / (2 - 2 * Real.cos x + epsilon))
    _ <= 2 * (Real.pi / (2 * |x|)) := by linarith
    _ = Real.pi / |x| := by field_simp [hxabs.ne']

theorem abs_sixVertexBetheLogRegularizationError_derivative_le_far
    {c epsilon x delta : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hx : delta <= |x|) :
    |sixVertexBetheLogNormDerivative c x -
        sixVertexRegularizedBetheLogNormDerivative c epsilon x| <=
      epsilon * Real.pi ^ 4 / (16 * delta ^ 4) := by
  have hx0 : x ≠ 0 := by exact abs_pos.mp (hdelta.trans_le hx)
  let B := 2 - 2 * Real.cos x
  have hBquad : 4 * x ^ 2 / Real.pi ^ 2 <= B := by
    simpa [B] using denominator_lower_quadratic hxIcc
  have hB : 0 < B := by
    have : 0 < 4 * x ^ 2 / Real.pi ^ 2 := by positivity
    exact this.trans_le hBquad
  have hBne : B ≠ 0 := hB.ne'
  have hBene : B + epsilon ≠ 0 := (add_pos hB hepsilon).ne'
  unfold sixVertexBetheLogNormDerivative
    sixVertexRegularizedBetheLogNormDerivative
  dsimp [B] at hBquad hB ⊢
  let R := -(c ^ 2 - 1) * Real.sin x /
    ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x)
  change |R - Real.sin x / B - (R - Real.sin x / (B + epsilon))| <= _
  rw [show R - Real.sin x / B - (R - Real.sin x / (B + epsilon)) =
    -Real.sin x * epsilon / (B * (B + epsilon)) by
      field_simp [hBne, hBene] <;> ring]
  rw [abs_div, abs_mul, abs_mul, abs_neg, abs_of_pos hepsilon,
    abs_of_pos hB, abs_of_pos (add_pos hB hepsilon)]
  have hden : (4 * delta ^ 2 / Real.pi ^ 2) ^ 2 <= B * (B + epsilon) := by
    have hx2 : delta ^ 2 <= x ^ 2 := by
      simpa [sq_abs] using (sq_le_sq₀ hdelta.le (abs_nonneg x)).2 hx
    have hlower : 4 * delta ^ 2 / Real.pi ^ 2 <= B := by
      calc
        _ <= 4 * x ^ 2 / Real.pi ^ 2 := by gcongr
        _ <= B := hBquad
    have hbase : 0 <= 4 * delta ^ 2 / Real.pi ^ 2 := by positivity
    calc
      (4 * delta ^ 2 / Real.pi ^ 2) ^ 2 <= B ^ 2 :=
        (sq_le_sq₀ hbase hB.le).2 hlower
      _ <= B * (B + epsilon) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left
          (show B <= B + epsilon from le_add_of_nonneg_right hepsilon.le)
          hB.le
  have hnum : |Real.sin x| * epsilon <= epsilon := by
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) hepsilon.le
  calc
    |Real.sin x| * epsilon / (B * (B + epsilon)) <=
        epsilon / (B * (B + epsilon)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hB (add_pos hB hepsilon)).le
    _ <= epsilon / (4 * delta ^ 2 / Real.pi ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left hepsilon.le (by positivity) hden
    _ = epsilon * Real.pi ^ 4 / (16 * delta ^ 4) := by
      field_simp [Real.pi_ne_zero, hdelta.ne']
      ring

theorem abs_sixVertexBetheLogRegularizationError_sub_le_singular
    {c epsilon p q : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hp : p ∈ Set.Ioo 0 Real.pi) (hq : q ∈ Set.Ioo 0 Real.pi)
    (hclose : |q - p| <= p / 2) :
    |sixVertexBetheLogRegularizationError c epsilon q -
        sixVertexBetheLogRegularizationError c epsilon p| <=
      (2 * Real.pi / p) * |q - p| := by
  have hqLower : p / 2 <= q := by
    have := neg_le_of_abs_le hclose
    linarith
  have hzLower (z : Real) (hz : z ∈ Set.uIcc p q) : p / 2 <= z := by
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at hz
      exact (half_le_self hp.1.le).trans hz.1
    · rw [Set.uIcc_of_ge hqp] at hz
      exact hqLower.trans hz.1
  have hzUpper (z : Real) (hz : z ∈ Set.uIcc p q) : z <= Real.pi := by
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at hz
      exact hz.2.trans hq.2.le
    · rw [Set.uIcc_of_ge hqp] at hz
      exact hz.2.trans hp.2.le
  have hdiff (z : Real) (hz : z ∈ Set.uIcc p q) :
      DifferentiableAt Real (sixVertexBetheLogRegularizationError c epsilon) z := by
    have hzpos : 0 < z := (half_pos hp.1).trans_le (hzLower z hz)
    exact (hasDerivAt_sixVertexBetheLogRegularizationError hc hepsilon
      hzpos.ne' ⟨by linarith [Real.pi_pos], hzUpper z hz⟩).differentiableAt
  have hbound (z : Real) (hz : z ∈ Set.uIcc p q) :
      ‖deriv (sixVertexBetheLogRegularizationError c epsilon) z‖ <=
        2 * Real.pi / p := by
    have hzpos : 0 < z := (half_pos hp.1).trans_le (hzLower z hz)
    rw [(hasDerivAt_sixVertexBetheLogRegularizationError hc hepsilon
      hzpos.ne' ⟨by linarith [Real.pi_pos], hzUpper z hz⟩).deriv,
      Real.norm_eq_abs]
    have hs := abs_sixVertexBetheLogRegularizationError_derivative_le_singular
      hc hepsilon hzpos.ne' ⟨by linarith [Real.pi_pos], hzUpper z hz⟩
    have hp2 : p <= 2 * z := by linarith [hzLower z hz]
    calc
      _ <= Real.pi / |z| := hs
      _ <= 2 * Real.pi / p := by
        rw [abs_of_pos hzpos]
        calc
          Real.pi / z <= Real.pi / (p / 2) :=
            div_le_div_of_nonneg_left Real.pi_pos.le (half_pos hp.1)
              (hzLower z hz)
          _ = 2 * Real.pi / p := by field_simp [hp.1.ne']
  have hmvt := (convex_uIcc p q).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmvt

theorem abs_sixVertexBetheLogRegularizationError_sub_le_far
    {c epsilon delta p q : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hp : p ∈ Set.Ioo 0 Real.pi)
    (hq : q ∈ Set.Ioo 0 Real.pi) (hpFar : delta <= p)
    (hclose : |q - p| <= p / 2) :
    |sixVertexBetheLogRegularizationError c epsilon q -
        sixVertexBetheLogRegularizationError c epsilon p| <=
      (epsilon * Real.pi ^ 4 / delta ^ 4) * |q - p| := by
  have hqLower : p / 2 <= q := by
    have := neg_le_of_abs_le hclose
    linarith
  have hzLower (z : Real) (hz : z ∈ Set.uIcc p q) : delta / 2 <= z := by
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at hz
      exact (by linarith [hpFar] : delta / 2 <= p) |>.trans hz.1
    · rw [Set.uIcc_of_ge hqp] at hz
      exact (by linarith [hpFar] : delta / 2 <= p / 2) |>.trans
        (hqLower.trans hz.1)
  have hzUpper (z : Real) (hz : z ∈ Set.uIcc p q) : z <= Real.pi := by
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at hz
      exact hz.2.trans hq.2.le
    · rw [Set.uIcc_of_ge hqp] at hz
      exact hz.2.trans hp.2.le
  have hdiff (z : Real) (hz : z ∈ Set.uIcc p q) :
      DifferentiableAt Real (sixVertexBetheLogRegularizationError c epsilon) z := by
    have hzpos : 0 < z := (half_pos hdelta).trans_le (hzLower z hz)
    exact (hasDerivAt_sixVertexBetheLogRegularizationError hc hepsilon
      hzpos.ne' ⟨by linarith [Real.pi_pos], hzUpper z hz⟩).differentiableAt
  have hbound (z : Real) (hz : z ∈ Set.uIcc p q) :
      ‖deriv (sixVertexBetheLogRegularizationError c epsilon) z‖ <=
        epsilon * Real.pi ^ 4 / delta ^ 4 := by
    have hzpos : 0 < z := (half_pos hdelta).trans_le (hzLower z hz)
    rw [(hasDerivAt_sixVertexBetheLogRegularizationError hc hepsilon
      hzpos.ne' ⟨by linarith [Real.pi_pos], hzUpper z hz⟩).deriv,
      Real.norm_eq_abs]
    have hfar := abs_sixVertexBetheLogRegularizationError_derivative_le_far
      hc hepsilon (half_pos hdelta) ⟨by linarith [Real.pi_pos], hzUpper z hz⟩
      (by rw [abs_of_pos hzpos]; exact hzLower z hz)
    convert hfar using 1
    field_simp [hdelta.ne']
    ring
  have hmvt := (convex_uIcc p q).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using hmvt

private theorem card_filter_fin_val_lt_le (n T : Nat) :
    (Finset.univ.filter (fun j : Fin n => j.val < T)).card <= T := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < T)
  let f : {j // j ∈ S} -> Fin T := fun j =>
    ⟨j.1.val, (Finset.mem_filter.mp j.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hv : (f a).val = (f b).val :=
      congrArg (fun z : Fin T => z.val) hab
    apply Subtype.ext
    apply Fin.ext
    exact hv
  have hcard := Fintype.card_le_of_injective f hf
  change S.card <= T
  rw [<- Fintype.card_coe]
  simpa using hcard




theorem abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff
    {c epsilon delta C : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hC : 0 <= C) {N n T : Nat} (hN : 0 < N)
    {p q : Fin n -> Real}
    (hp : forall j, p j ∈ Set.Ioo 0 Real.pi)
    (hq : forall j, q j ∈ Set.Ioo 0 Real.pi)
    (hclose : forall j, |q j - p j| <= p j / 2)
    (hdiff : forall j, |q j - p j| <= C * p j / N)
    (hfar : forall j, T <= j.val -> delta <= p j) :
    |∑ j, (sixVertexBetheLogRegularizationError c epsilon (q j) -
        sixVertexBetheLogRegularizationError c epsilon (p j))| <=
      (T : Real) * (2 * Real.pi * C / N) +
        (n : Real) *
          ((epsilon * Real.pi ^ 4 / delta ^ 4) * (C * Real.pi / N)) := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < T)
  let f : Fin n -> Real := fun j =>
    sixVertexBetheLogRegularizationError c epsilon (q j) -
      sixVertexBetheLogRegularizationError c epsilon (p j)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hsmall (j : Fin n) (hj : j ∈ S) :
      |f j| <= 2 * Real.pi * C / N := by
    have hs := abs_sixVertexBetheLogRegularizationError_sub_le_singular
      hc hepsilon (hp j) (hq j) (hclose j)
    have hp0 := (hp j).1
    calc
      |f j| <= (2 * Real.pi / p j) * |q j - p j| := hs
      _ <= (2 * Real.pi / p j) * (C * p j / N) := by
        exact mul_le_mul_of_nonneg_left (hdiff j) (by positivity)
      _ = 2 * Real.pi * C / N := by field_simp [hp0.ne'] <;> ring
  have hlarge (j : Fin n) (hj : j ∉ S) :
      |f j| <=
        (epsilon * Real.pi ^ 4 / delta ^ 4) * (C * Real.pi / N) := by
    have hjFar : T <= j.val := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hj
      exact hj
    have hs := abs_sixVertexBetheLogRegularizationError_sub_le_far
      hc hepsilon hdelta (hp j) (hq j) (hfar j hjFar) (hclose j)
    have hqpdiff := hdiff j
    have hpPi : p j <= Real.pi := (hp j).2.le
    have hCp : C * p j <= C * Real.pi :=
      mul_le_mul_of_nonneg_left hpPi hC
    calc
      |f j| <= (epsilon * Real.pi ^ 4 / delta ^ 4) * |q j - p j| := hs
      _ <= (epsilon * Real.pi ^ 4 / delta ^ 4) * (C * p j / N) := by
        gcongr
      _ <= (epsilon * Real.pi ^ 4 / delta ^ 4) *
          (C * Real.pi / N) := by
        gcongr
  rw [show (∑ j, f j) = (∑ j ∈ S, f j) + ∑ j ∈ Sᶜ, f j by
    rw [Finset.sum_add_sum_compl]]
  calc
    |(∑ j ∈ S, f j) + ∑ j ∈ Sᶜ, f j| <=
        |∑ j ∈ S, f j| + |∑ j ∈ Sᶜ, f j| := abs_add_le _ _
    _ <= (∑ j ∈ S, |f j|) + ∑ j ∈ Sᶜ, |f j| := by
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _)
        (Finset.abs_sum_le_sum_abs _ _)
    _ <= (∑ _j ∈ S, 2 * Real.pi * C / N) +
        ∑ _j ∈ Sᶜ,
          (epsilon * Real.pi ^ 4 / delta ^ 4) * (C * Real.pi / N) := by
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro j hj
        exact hsmall j hj
      · intro j hj
        exact hlarge j (by simpa using hj)
    _ <= (T : Real) * (2 * Real.pi * C / N) +
        (n : Real) *
          ((epsilon * Real.pi ^ 4 / delta ^ 4) * (C * Real.pi / N)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_filter_fin_val_lt_le n T
        · positivity
      · apply mul_le_mul_of_nonneg_right
        · have hc : (Sᶜ).card <= n := by
            simpa using (Finset.card_le_univ Sᶜ)
          exact_mod_cast hc
        · positivity



theorem eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s) k
      let n := s + k + 1
      let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
      |∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
            sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| <=
        ((N / M + 1 : Nat) : Real) * (2 * Real.pi * C / N) +
          (n : Real) *
            ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
              (C * Real.pi / N)) := by
  let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
  have hC : 0 <= C := sixVertexCanonicalEvenOffsetLinearBound_nonneg hc s
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hwide : ∀ᶠ k : Nat in atTop,
      2 * C <= (sixVertexFourWidth (2 * s) k : Real) :=
    hwidth.eventually (eventually_ge_atTop (2 * C))
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s,
      eventually_abs_sixVertexCanonicalEvenChargeOffset_le_mul_abs_aligned
        hc s,
      hwide] with k hk hoff hNk
  let N := sixVertexFourWidth (2 * s) k
  let n := s + k + 1
  let p : Fin n -> Real := sixVertexCanonicalEvenCommonHalfRoot hc s k
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hMreal : 0 < (M : Real) := by exact_mod_cast hM
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    exact sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    unfold q sixVertexCanonicalFixedEvenDensityPositiveRoots
    rw [sixVertexEvenSymmetricLift_projection (s + k + 1) hk.1.1.2.1]
    exact hk.1.1
  have hdiff (j : Fin n) : |q j - p j| <= C * p j / N := by
    let i : Fin (n + n) := Fin.natAdd n j
    have hi := hoff i
    have haligned :
        sixVertexCanonicalEvenAlignedHalfRoots hc s k i = p j := by
      dsimp [i, n, p]
      exact sixVertexCanonicalEvenAlignedHalfRoots_positive hc s k j
    have hfixed :
        sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i = q j := by
      rfl
    rw [sixVertexCanonicalEvenChargeOffset, haligned, hfixed,
      abs_mul, abs_of_pos hNreal, abs_of_pos (hp j).1] at hi
    apply (le_div_iff₀ hNreal).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi
  have hclose (j : Fin n) : |q j - p j| <= p j / 2 := by
    calc
      |q j - p j| <= C * p j / N := hdiff j
      _ <= p j / 2 := by
        apply (div_le_iff₀ hNreal).2
        have hp0 := (hp j).1
        have hCN : 2 * C <= (N : Real) := by simpa [N, C] using hNk
        nlinarith
  have hfar (j : Fin n) (hj : N / M + 1 <= j.val) :
      2 * Real.pi / M <= p j := by
    have hjdiv : N / M < j.val := by omega
    have hNjM : N < j.val * M :=
      (Nat.div_lt_iff_lt_mul hM).1 hjdiv
    have hNjMreal : (N : Real) < (j.val : Real) * M := by
      exact_mod_cast hNjM
    have hjpos : 0 < (j.val : Real) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ _) hj)
    have hquant :=
      sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc
        (2 * s + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
    have hwidthEq : sixVertexFourWidth 0 (2 * s + k) = N := by
      dsimp [N]
      unfold sixVertexFourWidth
      omega
    rw [hwidthEq] at hquant
    have hquant' : Real.pi * (2 * (j.val : Real) + 1) <
        (N : Real) * p j := by
      simpa [p, sixVertexCanonicalEvenCommonHalfRoot] using hquant
    have hNp : (N : Real) * p j <
        ((j.val : Real) * M) * p j :=
      mul_lt_mul_of_pos_right hNjMreal (hp j).1
    apply (div_le_iff₀ hMreal).2
    by_contra hbad
    rw [not_le] at hbad
    have hbad' : (M : Real) * p j < 2 * Real.pi := by
      simpa [mul_comm] using hbad
    have hjbad := mul_lt_mul_of_pos_left hbad' hjpos
    nlinarith
  exact abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff
    hc hepsilon (div_pos (mul_pos (by norm_num) Real.pi_pos) hMreal)
    hC hN hp hq hclose hdiff hfar



theorem eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s) k
      let n := s + k + 1
      let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
      |∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
            sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| <=
        2 * Real.pi * C * (1 / M + 1 / N) +
          epsilon * C * Real.pi * M ^ 4 / 16 := by
  let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
  filter_upwards
    [eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le
      hc hepsilon s hM] with k hk
  let N := sixVertexFourWidth (2 * s) k
  let n := s + k + 1
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hMreal : 0 < (M : Real) := by exact_mod_cast hM
  have hC : 0 <= C := sixVertexCanonicalEvenOffsetLinearBound_nonneg hc s
  have hnN : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hcastDiv : ((N / M : Nat) : Real) <= (N : Real) / M :=
    Nat.cast_div_le
  have hfirst :
      ((N / M + 1 : Nat) : Real) * (2 * Real.pi * C / N) <=
        2 * Real.pi * C * (1 / M + 1 / N) := by
    calc
      ((N / M + 1 : Nat) : Real) * (2 * Real.pi * C / N) =
          (((N / M : Nat) : Real) + 1) *
            (2 * Real.pi * C / N) := by push_cast; ring
      _ <= ((N : Real) / M + 1) * (2 * Real.pi * C / N) := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · positivity
      _ = 2 * Real.pi * C * (1 / M + 1 / N) := by
        field_simp [hMreal.ne', hNreal.ne']
  have hcoefficient :
      0 <= (epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
        (C * Real.pi / N) := by positivity
  have hsecond :
      (n : Real) *
          ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
            (C * Real.pi / N)) <=
        epsilon * C * Real.pi * M ^ 4 / 16 := by
    calc
      (n : Real) *
          ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
            (C * Real.pi / N)) <=
          (N : Real) *
            ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
              (C * Real.pi / N)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hnN
        · exact hcoefficient
      _ = epsilon * C * Real.pi * M ^ 4 / 16 := by
        field_simp [hMreal.ne', hNreal.ne', Real.pi_ne_zero]
        ring
  exact hk.trans (add_le_add hfirst hsecond)



theorem exists_eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_lt
    {c : Real} (hc : 2 < c) (s : Nat) {eta : Real} (heta : 0 < eta) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ᶠ k : Nat in atTop,
        |∑ j : Fin (s + k + 1),
            (sixVertexBetheLogRegularizationError c epsilon
                (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
              sixVertexBetheLogRegularizationError c epsilon
                (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| < eta := by
  let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
  have hC : 0 <= C := sixVertexCanonicalEvenOffsetLinearBound_nonneg hc s
  obtain ⟨M : Nat, hMlarge⟩ :=
    exists_nat_gt (8 * Real.pi * C / eta)
  have hM : 0 < M := by
    have hnonneg : 0 <= 8 * Real.pi * C / eta := by positivity
    exact_mod_cast (hnonneg.trans_lt hMlarge)
  have hMreal : 0 < (M : Real) := by exact_mod_cast hM
  let D : Real := C * Real.pi * (M : Real) ^ 4 / 16
  have hD : 0 <= D := by dsimp [D]; positivity
  let epsilon : Real := eta / (8 * (D + 1))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hcut : 2 * Real.pi * C * (1 / (M : Real)) < eta / 4 := by
    have hscaled : 8 * Real.pi * C < (M : Real) * eta := by
      exact (div_lt_iff₀ heta).1 hMlarge
    rw [show 2 * Real.pi * C * (1 / (M : Real)) =
      (2 * Real.pi * C) / M by ring]
    apply (div_lt_iff₀ hMreal).2
    nlinarith
  have hepsilonD : epsilon * C * Real.pi * (M : Real) ^ 4 / 16 <
      eta / 4 := by
    have hD1 : D + 1 ≠ 0 := ne_of_gt (by linarith : 0 < D + 1)
    have hfrac : D / (D + 1) < 1 :=
      (div_lt_one (by linarith : 0 < D + 1)).2 (by linarith)
    have hmul : eta / 8 * (D / (D + 1)) < eta / 8 := by
      simpa using
        (mul_lt_mul_of_pos_left hfrac (by positivity : 0 < eta / 8))
    calc
      epsilon * C * Real.pi * (M : Real) ^ 4 / 16 =
          epsilon * D := by
        dsimp [D]
        ring
      _ =
          eta / 8 * (D / (D + 1)) := by
        dsimp [epsilon]
        field_simp [hD1] <;> ring
      _ < eta / 8 := hmul
      _ < eta / 4 := by linarith
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto
      (fun k : Nat => 2 * Real.pi * C /
        (sixVertexFourWidth (2 * s) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hwidthSmall : ∀ᶠ k : Nat in atTop,
      2 * Real.pi * C *
          (1 / (sixVertexFourWidth (2 * s) k : Real)) < eta / 4 := by
    rw [Metric.tendsto_atTop] at hzero
    obtain ⟨K, hK⟩ := hzero (eta / 4) (by positivity)
    filter_upwards [eventually_ge_atTop K] with k hk
    have hz := hK k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hz
    simpa [div_eq_mul_inv] using hz
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards
    [eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple
        hc hepsilon s hM,
      hwidthSmall] with k hk hsmall
  have hreg : epsilon * C * Real.pi * (M : Real) ^ 4 / 16 < eta / 4 :=
    hepsilonD
  calc
    |∑ j : Fin (s + k + 1),
        (sixVertexBetheLogRegularizationError c epsilon
            (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
          sixVertexBetheLogRegularizationError c epsilon
            (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| <=
        2 * Real.pi * C *
            (1 / (M : Real) +
              1 / (sixVertexFourWidth (2 * s) k : Real)) +
          epsilon * C * Real.pi * (M : Real) ^ 4 / 16 := hk
    _ < eta := by
      rw [mul_add]
      nlinarith

end

end StatMech.FrontierD
