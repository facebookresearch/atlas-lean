/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFiniteDensityLipschitz











namespace StatMech.FrontierD

noncomputable section

def sixVertexTailFiniteDensityFloor (c : Real) : Real :=
  (1 - (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) / 2) / (2 * Real.pi)

theorem sixVertexFiniteRootDensity_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (p : Fin n → Real) (x : Real) :
    (1 - (n : Real) *
        (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) / N) /
        (2 * Real.pi) <=
      sixVertexFiniteRootDensity c N n p x := by
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  let K : Fin n → Real := fun k =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hterm (k : Fin n) : -R <= K k := by
    have hnorm : ‖K k‖ <= R := by
      exact norm_sixVertexTheta_leftDerivative_le hc x (p k)
    calc
      -R <= -‖K k‖ := neg_le_neg hnorm
      _ = -|K k| := by rw [Real.norm_eq_abs]
      _ <= K k := neg_abs_le _
  have hsum : -(n : Real) * R <= ∑ k, K k := by
    calc
      -(n : Real) * R = ∑ _k : Fin n, -R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
      _ <= ∑ k, K k := Finset.sum_le_sum fun k _ => hterm k
  unfold sixVertexFiniteRootDensity
  change (1 - (n : Real) * R / N) / (2 * Real.pi) <=
    (1 + (∑ k, K k) / N) / (2 * Real.pi)
  apply div_le_div_of_nonneg_right _ (by positivity : 0 <= 2 * Real.pi)
  have hsumDiv := (div_le_div_iff_of_pos_right hNreal).2 hsum
  calc
    1 - (n : Real) * R / N =
        1 + (-(n : Real) * R) / N := by ring
    _ <= 1 + (∑ k, K k) / N := by
      simpa [add_comm] using add_le_add_left hsumDiv 1

theorem sixVertexTailFiniteDensityFloor_pos
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    0 < sixVertexTailFiniteDensityFloor c := by
  let d := sixVertexAnisotropyMagnitude c
  have hd1 : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hratio : d / (d - 1) < 2 := by
    rw [div_lt_iff₀ (sub_pos.mpr hd1)]
    linarith
  unfold sixVertexTailFiniteDensityFloor
  apply div_pos
  · nlinarith
  · positivity

theorem sixVertexTailFiniteDensityFloor_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n <= N) (p : Fin n → Real) (x : Real) :
    sixVertexTailFiniteDensityFloor c <=
      sixVertexFiniteRootDensity c N n p x := by
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hR : 0 <= R := by
    exact (div_pos
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))).le
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hhalfReal : 2 * (n : Real) <= (N : Real) := by exact_mod_cast hhalf
  have hratio : (n : Real) * R / N <= R / 2 := by
    rw [div_le_div_iff₀ hNreal (by norm_num : (0 : Real) < 2)]
    nlinarith
  calc
    sixVertexTailFiniteDensityFloor c <=
        (1 - (n : Real) * R / N) / (2 * Real.pi) := by
      unfold sixVertexTailFiniteDensityFloor
      apply div_le_div_of_nonneg_right _ (by positivity : 0 <= 2 * Real.pi)
      linarith
    _ <= sixVertexFiniteRootDensity c N n p x :=
      sixVertexFiniteRootDensity_lower hc hN p x


theorem sixVertexBetheSolution_adjacentSpacing_upper_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * (n + 1) <= N)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (j : Fin n) :
    p j.succ - p j.castSucc <=
      1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
  let floor := sixVertexTailFiniteDensityFloor c
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have horder : p j.castSucc <= p j.succ := (hopen.1 (by simp)).le
  have hconst : IntervalIntegrable (fun _ : Real => floor)
      MeasureTheory.volume (p j.castSucc) (p j.succ) :=
    continuous_const.intervalIntegrable _ _
  have hdensity : IntervalIntegrable
      (sixVertexFiniteRootDensity c N (n + 1) p)
      MeasureTheory.volume (p j.castSucc) (p j.succ) :=
    (continuous_sixVertexFiniteRootDensity
      hc N (n + 1) p).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on horder hconst hdensity
    (fun x _ => sixVertexTailFiniteDensityFloor_le hc hN hhalf p x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_adjacent
    hc hN hsol j] at hmono
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hfloor)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith


theorem sixVertexBetheSolution_boundarySpacing_upper_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    p 0 - (p (Fin.last n) - 2 * Real.pi) <=
      1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
  let floor := sixVertexTailFiniteDensityFloor c
  let a := p (Fin.last n) - 2 * Real.pi
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hhalfLe : 2 * (n + 1) <= N := hhalf.ge
  have horder : a <= p 0 := by
    have hfirst := (hopen.2.2 (0 : Fin (n + 1))).1
    have hlast := (hopen.2.2 (Fin.last n)).2
    dsimp [a]
    linarith [Real.pi_pos]
  have hconst : IntervalIntegrable (fun _ : Real => floor)
      MeasureTheory.volume a (p 0) := continuous_const.intervalIntegrable _ _
  have hdensity : IntervalIntegrable
      (sixVertexFiniteRootDensity c N (n + 1) p)
      MeasureTheory.volume a (p 0) :=
    (continuous_sixVertexFiniteRootDensity
      hc N (n + 1) p).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on horder hconst hdensity
    (fun x _ => sixVertexTailFiniteDensityFloor_le hc hN hhalfLe p x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hboundary := intervalIntegral_sixVertexFiniteRootDensity_boundary
    hc hN hsol
  have hmass : ((N : Real) - 2 * (n + 1 : Real) + 1) / N =
      1 / (N : Real) := by
    have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by
      exact_mod_cast hhalf
    rw [hhalfReal]
    ring
  rw [hmass] at hboundary
  change (∫ x in a..p 0,
    sixVertexFiniteRootDensity c N (n + 1) p x) = 1 / N at hboundary
  rw [hboundary] at hmono
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  change p 0 - a <= 1 / ((N : Real) * floor)
  rw [le_div_iff₀ (mul_pos hNreal hfloor)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

end

end StatMech.FrontierD
