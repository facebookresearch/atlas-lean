/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootDensityFinite
import Code.FrontierD.SixVertexBetheQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds










namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaLeftKernelLipschitzBound (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  4 * d * (d + 1) * (4 * (d + 1) + 2) /
    (16 * (d - 1) ^ 4)

theorem sixVertexThetaLeftKernelLipschitzBound_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexThetaLeftKernelLipschitzBound c := by
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  dsimp [sixVertexThetaLeftKernelLipschitzBound]
  positivity

theorem sixVertexThetaDerivativeDenominator_uniform_lower
    {c : Real} (hc : 2 < c) (x y : Real) :
    4 * (sixVertexAnisotropyMagnitude c - 1) ^ 2 <=
      sixVertexThetaDerivativeDenominator c x y := by
  let d := sixVertexAnisotropyMagnitude c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hFx := (sixVertexBetheIntegratingFactor_bounds hc x).1
  have hFy := (sixVertexBetheIntegratingFactor_bounds hc y).1
  have hbase : 0 <= d - 1 := sub_nonneg.mpr hd.le
  have hprod : (d - 1) ^ 2 <= Fx * Fy := by
    nlinarith [mul_le_mul hFx hFy hbase
      (sixVertexBetheIntegratingFactor_pos hc x).le]
  rw [sixVertexThetaDerivativeDenominator_eq]
  have hcos := Real.cos_le_one (x - y)
  dsimp [d, Fx, Fy] at hprod ⊢
  nlinarith

theorem sixVertexThetaDerivativeDenominator_lipschitz_left
    {c : Real} (hc : 2 < c) (x z y : Real) :
    |sixVertexThetaDerivativeDenominator c x y -
        sixVertexThetaDerivativeDenominator c z y| <=
      (4 * (sixVertexAnisotropyMagnitude c + 1) + 2) * |x - z| := by
  let d := sixVertexAnisotropyMagnitude c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fz := sixVertexBetheIntegratingFactor c z
  let Fy := sixVertexBetheIntegratingFactor c y
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hFyPos : 0 <= Fy := (sixVertexBetheIntegratingFactor_pos hc y).le
  have hFyUpper : Fy <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hF : |Fx - Fz| <= |x - z| := by
    simpa [Fx, Fz, sixVertexBetheIntegratingFactor] using
      Real.abs_cos_sub_cos_le x z
  have hcos : |Real.cos (z - y) - Real.cos (x - y)| <= |x - z| := by
    have h := Real.abs_cos_sub_cos_le (z - y) (x - y)
    simpa [abs_sub_comm] using h
  rw [sixVertexThetaDerivativeDenominator_eq,
    sixVertexThetaDerivativeDenominator_eq]
  have heq :
      4 * Fx * Fy + 2 * (1 - Real.cos (x - y)) -
          (4 * Fz * Fy + 2 * (1 - Real.cos (z - y))) =
        4 * (Fx - Fz) * Fy +
          2 * (Real.cos (z - y) - Real.cos (x - y)) := by ring
  rw [show sixVertexBetheIntegratingFactor c x = Fx by rfl,
    show sixVertexBetheIntegratingFactor c z = Fz by rfl,
    show sixVertexBetheIntegratingFactor c y = Fy by rfl,
    heq]
  calc
    |4 * (Fx - Fz) * Fy +
        2 * (Real.cos (z - y) - Real.cos (x - y))| <=
        |4 * (Fx - Fz) * Fy| +
          |2 * (Real.cos (z - y) - Real.cos (x - y))| :=
      abs_add_le _ _
    _ = 4 * |Fx - Fz| * Fy +
        2 * |Real.cos (z - y) - Real.cos (x - y)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hFyPos]
      norm_num
    _ <= (4 * (d + 1) + 2) * |x - z| := by
      have hxz : 0 <= |x - z| := abs_nonneg _
      have h1 := mul_le_mul hF hFyUpper hFyPos hxz
      nlinarith
    _ = (4 * (sixVertexAnisotropyMagnitude c + 1) + 2) *
        |x - z| := by rfl



theorem sixVertexThetaLeftKernel_lipschitz
    {c : Real} (hc : 2 < c) (x z y : Real) :
    |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y -
        4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c z y| <=
      sixVertexThetaLeftKernelLipschitzBound c * |x - z| := by
  let d := sixVertexAnisotropyMagnitude c
  let Fy := sixVertexBetheIntegratingFactor c y
  let Dx := sixVertexThetaDerivativeDenominator c x y
  let Dz := sixVertexThetaDerivativeDenominator c z y
  let L := 4 * (d + 1) + 2
  let q := d - 1
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hq : 0 < q := sub_pos.mpr hd
  have hFyPos : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hFyUpper : Fy <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hDxPos : 0 < Dx := sixVertexThetaDerivativeDenominator_pos hc x y
  have hDzPos : 0 < Dz := sixVertexThetaDerivativeDenominator_pos hc z y
  have hDxLower : 4 * q ^ 2 <= Dx := by
    exact sixVertexThetaDerivativeDenominator_uniform_lower hc x y
  have hDzLower : 4 * q ^ 2 <= Dz := by
    exact sixVertexThetaDerivativeDenominator_uniform_lower hc z y
  have hDdiff : |Dx - Dz| <= L * |x - z| := by
    exact sixVertexThetaDerivativeDenominator_lipschitz_left hc x z y
  have hnum : |4 * sixVertexDelta c * Fy| = 4 * d * Fy := by
    have hdelta : sixVertexDelta c = -d := by
      dsimp [d, sixVertexAnisotropyMagnitude]
      ring
    rw [hdelta]
    have hd0 : 0 <= d := hd.le.trans' zero_le_one
    rw [show 4 * -d * Fy = -(4 * d * Fy) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd0) hFyPos.le)]
  have hdenprod : 16 * q ^ 4 <= Dx * Dz := by
    have hmul := mul_le_mul hDxLower hDzLower
      (by positivity : 0 <= 4 * q ^ 2) hDxPos.le
    nlinarith [sq_nonneg (q ^ 2)]
  have hformula :
      4 * sixVertexDelta c * Fy / Dx -
          4 * sixVertexDelta c * Fy / Dz =
        (4 * sixVertexDelta c * Fy) * (Dz - Dx) / (Dx * Dz) := by
    field_simp [hDxPos.ne', hDzPos.ne']
  rw [show sixVertexBetheIntegratingFactor c y = Fy by rfl,
    show sixVertexThetaDerivativeDenominator c x y = Dx by rfl,
    show sixVertexThetaDerivativeDenominator c z y = Dz by rfl,
    hformula, abs_div, abs_mul, abs_of_pos (mul_pos hDxPos hDzPos),
    abs_sub_comm, hnum]
  rw [div_le_iff₀ (mul_pos hDxPos hDzPos)]
  have hleft :
      4 * d * Fy * |Dx - Dz| <=
        4 * d * (d + 1) * L * |x - z| := by
    have hnonneg : 0 <= 4 * d := by positivity
    have hLnonneg : 0 <= L * |x - z| := by
      apply mul_nonneg
      · dsimp [L]
        positivity
      · exact abs_nonneg _
    have hprod := mul_le_mul hDdiff hFyUpper hFyPos.le hLnonneg
    nlinarith
  have hright :
      (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (16 * q ^ 4) <=
        (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (Dx * Dz) := by
    exact mul_le_mul_of_nonneg_left hdenprod (by positivity)
  have hcancel :
      (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (16 * q ^ 4) =
        4 * d * (d + 1) * L * |x - z| := by
    have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq.ne'
    field_simp
  dsimp [sixVertexThetaLeftKernelLipschitzBound, L, q, d]
  exact hleft.trans (hcancel.symm.trans_le hright)


def sixVertexFiniteRootDensityLipschitzConstant (c : Real) : NNReal :=
  Real.toNNReal
    (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi))



theorem lipschitzWith_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) (p : Fin n → Real) :
    LipschitzWith (sixVertexFiniteRootDensityLipschitzConstant c)
      (sixVertexFiniteRootDensity c N n p) := by
  let B := sixVertexThetaLeftKernelLipschitzBound c
  let K : Real → Fin n → Real := fun x k =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)
  have hB : 0 <= B := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnreal : (n : Real) <= (N : Real) := by exact_mod_cast hn
  have hC : ((sixVertexFiniteRootDensityLipschitzConstant c : NNReal) : Real) =
      B / (2 * Real.pi) := by
    simp only [sixVertexFiniteRootDensityLipschitzConstant,
      Real.coe_toNNReal, B]
    exact max_eq_left (div_nonneg hB (by positivity))
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, Real.dist_eq]
  have hsum :
      |∑ k, K x k - ∑ k, K z k| <=
        (n : Real) * B * |x - z| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k, (K x k - K z k)| <=
          ∑ k, |K x k - K z k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _k : Fin n, B * |x - z| := by
        apply Finset.sum_le_sum
        intro k _
        exact sixVertexThetaLeftKernel_lipschitz hc x z (p k)
      _ = (n : Real) * B * |x - z| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fin, Nat.cast_ofNat]
        ring
  have hdensity :
      sixVertexFiniteRootDensity c N n p x -
          sixVertexFiniteRootDensity c N n p z =
        ((∑ k, K x k) - ∑ k, K z k) /
          ((N : Real) * (2 * Real.pi)) := by
    unfold sixVertexFiniteRootDensity
    dsimp [K]
    field_simp [hNreal.ne', Real.pi_ne_zero]
    ring
  rw [hdensity, abs_div,
    abs_of_pos (mul_pos hNreal (by positivity : 0 < 2 * Real.pi))]
  rw [div_le_iff₀ (mul_pos hNreal (by positivity : 0 < 2 * Real.pi))]
  rw [hC]
  change |(∑ k, K x k) - ∑ k, K z k| <=
    (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi)) *
      |x - z| * ((N : Real) * (2 * Real.pi))
  calc
    |(∑ k, K x k) - ∑ k, K z k| <=
        (n : Real) * B * |x - z| := hsum
    _ <= (N : Real) * B * |x - z| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnreal hB) (abs_nonneg _)
    _ = (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi)) *
        |x - z| * ((N : Real) * (2 * Real.pi)) := by
      dsimp [B]
      field_simp [Real.pi_ne_zero]


def sixVertexFiniteRootDensityUniformBound (c : Real) : Real :=
  (1 + sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) / (2 * Real.pi)

theorem abs_sixVertexFiniteRootDensity_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n <= N) (p : Fin n → Real) (x : Real) :
    |sixVertexFiniteRootDensity c N n p x| <=
      sixVertexFiniteRootDensityUniformBound c := by
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  let K : Fin n → Real := fun k =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)
  have hR : 0 <= R := by
    exact (div_pos
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))).le
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnreal : (n : Real) <= (N : Real) := by exact_mod_cast hn
  have hsum : |∑ k, K k| <= (N : Real) * R := by
    calc
      |∑ k, K k| <= ∑ k, |K k| := Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _k : Fin n, R := by
        apply Finset.sum_le_sum
        intro k _
        rw [← Real.norm_eq_abs]
        exact norm_sixVertexTheta_leftDerivative_le hc x (p k)
      _ = (n : Real) * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
      _ <= (N : Real) * R := mul_le_mul_of_nonneg_right hnreal hR
  unfold sixVertexFiniteRootDensity sixVertexFiniteRootDensityUniformBound
  change |(1 + (∑ k, K k) / (N : Real)) / (2 * Real.pi)| <= _
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 <= 2 * Real.pi)
  calc
    |1 + (∑ k, K k) / (N : Real)| <=
        1 + |(∑ k, K k) / (N : Real)| := by
      simpa using abs_add_le (1 : Real) ((∑ k, K k) / (N : Real))
    _ = 1 + |∑ k, K k| / (N : Real) := by
      rw [abs_div, abs_of_pos hNreal]
    _ <= 1 + R := by
      gcongr
      exact (div_le_iff₀ hNreal).2 (by simpa [mul_comm] using hsum)
    _ = 1 + sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by rfl





theorem abs_gap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    |(p j.succ - p j.castSucc) *
          sixVertexFiniteRootDensity c N (n + 1) p (p j.castSucc) -
        1 / N| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (p j.succ - p j.castSucc) ^ 2 := by
  have horder : p j.castSucc <= p j.succ := by
    exact (hopen.1 (by simp)).le
  have hquad := abs_gap_mul_left_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N (n + 1) p)
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hn p) horder
  rw [intervalIntegral_sixVertexFiniteRootDensity_adjacent
    hc hN hsol j] at hquad
  exact hquad



theorem abs_gap_mul_finiteRootDensity_right_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hn : n + 1 <= N) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    |(p j.succ - p j.castSucc) *
          sixVertexFiniteRootDensity c N (n + 1) p (p j.succ) -
        1 / N| <=
      2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (p j.succ - p j.castSucc) ^ 2 := by
  let gap := p j.succ - p j.castSucc
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  have hgap : 0 <= gap := sub_nonneg.mpr (hopen.1 (by simp)).le
  have hleft := abs_gap_mul_finiteRootDensity_sub_inv_width_le
    hc hN hn hopen hsol j
  have hlip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  have hrho : |rho (p j.succ) - rho (p j.castSucc)| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap := by
    calc
      |rho (p j.succ) - rho (p j.castSucc)| =
          dist (rho (p j.succ)) (rho (p j.castSucc)) := by
            rw [Real.dist_eq]
      _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          dist (p j.succ) (p j.castSucc) :=
        hlip.dist_le_mul _ _
      _ = (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap := by
        rw [Real.dist_eq, abs_of_nonneg hgap]
  have hmove :
      |gap * rho (p j.succ) - gap * rho (p j.castSucc)| <=
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hgap]
    nlinarith
  change |gap * rho (p j.succ) - 1 / N| <= _
  calc
    |gap * rho (p j.succ) - 1 / N| <=
        |gap * rho (p j.succ) - gap * rho (p j.castSucc)| +
          |gap * rho (p j.castSucc) - 1 / N| := by
      exact abs_sub_le _ _ _
    _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 +
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 :=
      add_le_add hmove hleft
    _ = 2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) * gap ^ 2 := by
      ring



theorem intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) (a b : Real) :
    ∫ x in a..b, sixVertexFiniteRootDensity c N n p x =
      sixVertexBetheCountingFunction c N n p b -
        sixVertexBetheCountingFunction c N n p a := by
  let f := sixVertexBetheCountingFunction c N n p
  let f' := sixVertexFiniteRootDensity c N n p
  have hderiv : deriv f = f' := by
    funext x
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).deriv
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt Real f x := by
    intro x _
    exact (hasDerivAt_sixVertexBetheCountingFunction hc hN p x).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc a b) :=
    (continuous_sixVertexFiniteRootDensity hc N n p).continuousOn
  exact intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff hcont



theorem intervalIntegral_sixVertexFiniteRootDensity_boundary
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∫ x in p (Fin.last n) - 2 * Real.pi..p 0,
        sixVertexFiniteRootDensity c N (n + 1) p x =
      ((N : Real) - 2 * (n + 1 : Real) + 1) / N := by
  let a := p (Fin.last n) - 2 * Real.pi
  have hshift : a + 2 * Real.pi = p (Fin.last n) := by
    dsimp [a]
    ring
  have hperiod := sixVertexBetheCountingFunction_add_two_pi
    hN c p a
  rw [hshift] at hperiod
  have hfirst := sixVertexBetheCountingFunction_at_root
    hN hsol (0 : Fin (n + 1))
  have hlast := sixVertexBetheCountingFunction_at_root
    hN hsol (Fin.last n)
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p a (p 0)]
  rw [hfirst]
  have hquantumFirst :
      sixVertexCentralQuantumNumber (0 : Fin (n + 1)) = -(n : Real) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    simp
    ring
  have hquantumLast :
      sixVertexCentralQuantumNumber (Fin.last n) = (n : Real) / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    simp
    ring
  rw [hquantumFirst]
  rw [hquantumLast] at hlast
  rw [hlast] at hperiod
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hN0 : (N : Real) ≠ 0 := hNreal.ne'
  dsimp [a]
  dsimp [a] at hperiod
  push_cast at hperiod ⊢
  field_simp [hN0] at hperiod ⊢
  linarith

end

end StatMech.FrontierD
