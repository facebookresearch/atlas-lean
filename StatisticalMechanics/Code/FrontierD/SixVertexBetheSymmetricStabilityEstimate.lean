/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricOffDiagonal
import Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic





namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFiniteRootDensity_lower_of_weighted_close
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    {rho : Real → Real} {rhoLower eta : Real}
    (hrhoLower : ∀ x, rhoLower ≤ rho x)
    (hclose : ∀ x,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
    ∀ x, rhoLower -
        eta / ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤
      sixVertexFiniteRootDensity c N n p x := by
  intro x
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hw := sixVertexRootDensityWeight_lower hc x
  have hweight := sixVertexRootDensityWeight_pos hc x
  have hdiff :
      |sixVertexFiniteRootDensity c N n p x - rho x| ≤ eta / wmin := by
    have heta : 0 ≤ eta := le_trans (abs_nonneg _) (hclose x)
    have hcx := hclose x
    apply (le_div_iff₀ hwmin).2
    calc
      |sixVertexFiniteRootDensity c N n p x - rho x| * wmin ≤
          sixVertexRootDensityWeight c x *
            |sixVertexFiniteRootDensity c N n p x - rho x| :=
        by simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hw (abs_nonneg
            (sixVertexFiniteRootDensity c N n p x - rho x))
      _ = |sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x)| := by
        rw [abs_mul, abs_of_pos hweight]
      _ ≤ eta := hcx
  have hlower := hrhoLower x
  rw [abs_le] at hdiff
  change rhoLower - eta / wmin ≤ _
  linarith

theorem sixVertexFiniteRootDensity_lower_at_of_weighted_close
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    {rho : Real → Real} {rhoLower eta x : Real}
    (hrhoLower : rhoLower ≤ rho x)
    (hclose :
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ eta) :
    rhoLower - eta /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤
      sixVertexFiniteRootDensity c N n p x := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hw := sixVertexRootDensityWeight_lower hc x
  have hweight := sixVertexRootDensityWeight_pos hc x
  have hdiff :
      |sixVertexFiniteRootDensity c N n p x - rho x| ≤ eta / wmin := by
    have heta : 0 ≤ eta := le_trans (abs_nonneg _) hclose
    apply (le_div_iff₀ hwmin).2
    calc
      |sixVertexFiniteRootDensity c N n p x - rho x| * wmin ≤
          sixVertexRootDensityWeight c x *
            |sixVertexFiniteRootDensity c N n p x - rho x| :=
        by simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hw (abs_nonneg
            (sixVertexFiniteRootDensity c N n p x - rho x))
      _ = |sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x)| := by
        rw [abs_mul, abs_of_pos hweight]
      _ ≤ eta := hclose
  rw [abs_le] at hdiff
  change rhoLower - eta / wmin ≤ _
  linarith

theorem sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) (j : Fin n) :
    p j.succ - p j.castSucc ≤ 1 / ((N : Real) * lower) := by
  have horder : p j.castSucc ≤ p j.succ := (hopen.1 (by simp)).le
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (n + 1) p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_adjacent hc hN hsol j] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

theorem sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    p 0 - (p (Fin.last n) - 2 * Real.pi) ≤
      1 / ((N : Real) * lower) := by
  let a := p (Fin.last n) - 2 * Real.pi
  have horder : a ≤ p 0 := by
    have hfirst := (hopen.2.2 (0 : Fin (n + 1))).1
    have hlast := (hopen.2.2 (Fin.last n)).2
    dsimp [a]
    linarith [Real.pi_pos]
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (n + 1) p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hboundary := intervalIntegral_sixVertexFiniteRootDensity_boundary
    hc hN hsol
  have hmass : ((N : Real) - 2 * (n + 1 : Real) + 1) / N =
      1 / (N : Real) := by
    have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by exact_mod_cast hhalf
    rw [hhalfReal]
    ring
  rw [hboundary, hmass] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  change p 0 - a ≤ 1 / ((N : Real) * lower)
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

theorem sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤
      sixVertexFiniteRootDensity c N (n + 1) p x) :
    ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤
        1 / ((N : Real) * lower) := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      exact sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower
        hc hN hhalf hopen hsol hlower hdensity
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      rw [sixVertexCyclicRootPartition_succ p (by omega),
        sixVertexCyclicRootPartition_succ p (by omega)]
      simpa [jf] using
        sixVertexBetheSolution_adjacentSpacing_upper_of_finiteDensityLower
          hc hN hopen hsol hlower hdensity jf



theorem abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : 0 < n)
    (hhalf : N = 2 * n) {p : Fin n → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N n p x)
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N n p y| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        (1 / ((N : Real) * lower)) * (2 * Real.pi) := by
  cases n with
  | zero => omega
  | succ n =>
      have hcount : n + 1 ≤ N := by omega
      have hmesh := sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
        hc hN hhalf hopen hsol hlower hdensity
      have hquad := abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh
        hc hN hcount hhalf hopen hsol hmesh hf hlip
      have hsum := sum_cyclicRootPartition_eq_sum_roots_of_periodic p hperiodic
      have hsumScaled :
          ∑ k ∈ Finset.range (n + 1),
              (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) =
            (∑ j, f (p j)) / N := by
        rw [← Finset.mul_sum, hsum]
        ring
      have hint := intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle
        (N := N) c p hperiodic
      rw [hsumScaled, hint] at hquad
      exact hquad

def sixVertexFiniteDensityContinuumErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  (sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * lower)) * (2 * Real.pi)) / (2 * Real.pi)

theorem abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {rho : Real → Real} (hrho : Continuous rho)
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N (n + 1) p y - rho y)| ≤ E)
    (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
  let rhoN := sixVertexFiniteRootDensity c N (n + 1) p
  let e : Real → Real := fun y =>
    sixVertexRootDensityWeight c y * (rhoN y - rho y)
  let D := sixVertexFiniteConvolutionDefect c N (n + 1) p
  let IN : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rhoN y
  let IR : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c z y * rho y
  let Q := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * lower)) * (2 * Real.pi)
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hrhoN : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have he : Continuous e := hweightCont.mul (hrhoN.sub hrho)
  have hrhoNInt : IntervalIntegrable rhoN MeasureTheory.volume
      (-Real.pi) Real.pi := hrhoN.intervalIntegrable _ _
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := hrho.intervalIntegrable _ _
  have heMass : ∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y = 0 := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rhoN y - rho y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoNInt hrhoInt,
      intervalIntegral_halfFilledFiniteRootDensity hc hN hhalf p, hrhoMass]
    ring
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE heMass
    (by simpa [e, rhoN] using hbound) x
  have hmesh := sixVertexCyclicRootPartition_mesh_of_finiteDensityLower
    hc hN hhalf hopen hsol hlower hdensity
  have hD : |D x| ≤ Q := by
    exact abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh
      hc hN hcount hhalf hopen hsol hmesh x
  have hkernel : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hNInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rhoN y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrhoN).intervalIntegrable _ _
  have hRInt : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hkernel.mul hrho).intervalIntegrable _ _
  have hJ : (∫ y in -Real.pi..Real.pi,
      (sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) * e y) = IN x - IR x := by
    rw [show (fun y =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y) by
        funext y
        dsimp [e]
        field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
    rw [show (fun y => sixVertexRootDensityKernel c x y * (rhoN y - rho y)) =
      fun y => sixVertexRootDensityKernel c x y * rhoN y -
        sixVertexRootDensityKernel c x y * rho y by funext y; ring]
    exact intervalIntegral.integral_sub hNInt hRInt
  have hNEq : sixVertexRootDensityWeight c x * rhoN x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IN x - (1 / (2 * Real.pi)) * D x := by
    have hfinite := sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x
    dsimp [rhoN, IN, D, sixVertexFiniteConvolutionDefect]
    rw [hfinite]
    field_simp [Real.pi_ne_zero,
      (by exact_mod_cast hN.ne' : (N : Real) ≠ 0)]
    ring
  have hREq : sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IR x := hrhoEq x hx
  have heqPoint : e x =
      -(1 / (2 * Real.pi)) * (IN x - IR x) -
        (1 / (2 * Real.pi)) * D x := by
    dsimp [e]
    rw [mul_sub, hNEq, hREq]
    ring
  change |e x| ≤ _
  rw [heqPoint, ← hJ]
  calc
    |-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y) -
        (1 / (2 * Real.pi)) * D x| ≤
      |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y)| +
        |(1 / (2 * Real.pi)) * D x| := by
      simpa [abs_neg] using abs_add_le
        (-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y))
        (-(1 / (2 * Real.pi)) * D x)
    _ ≤ sixVertexRootDensityContractionRate c * E + Q / (2 * Real.pi) := by
      apply add_le_add hcontract
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      calc
        (1 / (2 * Real.pi)) * |D x| ≤
            (1 / (2 * Real.pi)) * Q :=
          mul_le_mul_of_nonneg_left hD (by positivity)
        _ = Q / (2 * Real.pi) := by ring
    _ = sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by rfl

def sixVertexWeightedFiniteDensityDifference
    {c : Real} (hc : 2 < c) (N n : Nat) (p : Fin n → Real)
    (rho : C(Real, Real)) : C(Set.Icc (-Real.pi) Real.pi, Real) :=
  ⟨fun x : Set.Icc (-Real.pi) Real.pi =>
      sixVertexRootDensityWeight c x.1 *
        (sixVertexFiniteRootDensity c N n p x.1 - rho x.1), by
    apply Continuous.mul
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · apply Continuous.sub
      · exact (continuous_sixVertexFiniteRootDensity hc N n p).comp
          continuous_subtype_val
      · exact rho.continuous.comp continuous_subtype_val⟩

def sixVertexWeightedFiniteDensityGauge
    {c : Real} (hc : 2 < c) (N n : Nat) (p : Fin n → Real)
    (rho : C(Real, Real)) : Real :=
  ‖sixVertexWeightedFiniteDensityDifference hc N n p rho‖

theorem abs_weightedFiniteDensity_sub_le_gauge
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    (rho : C(Real, Real))
    (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤
      sixVertexWeightedFiniteDensityGauge hc N n p rho := by
  simpa only [sixVertexWeightedFiniteDensityGauge,
    sixVertexWeightedFiniteDensityDifference, Real.norm_eq_abs] using
    (sixVertexWeightedFiniteDensityDifference hc N n p rho).norm_coe_le_norm
      ⟨x, hx⟩

theorem sixVertexWeightedFiniteDensityGauge_le_of_pointwise
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    (rho : C(Real, Real)) {E : Real} (hE : 0 ≤ E)
    (hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N n p rho ≤ E := by
  rw [sixVertexWeightedFiniteDensityGauge,
    ContinuousMap.norm_le _ hE]
  intro x
  simpa only [sixVertexWeightedFiniteDensityDifference, Real.norm_eq_abs] using
    hbound x x.2

theorem sixVertexWeightedFiniteDensityGauge_selfImproves
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hkernel : 0 < sixVertexRootDensityKernelLipschitzBound c :=
    sixVertexRootDensityKernelLipschitzBound_pos hc
  have huniform : 0 < sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have herror : 0 ≤ sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    unfold sixVertexFiniteDensityContinuumErrorOfLower
    positivity
  apply sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho
    (add_nonneg (mul_nonneg hrate.1 hE) herror)
  intro x hx
  apply abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower
    hc hN hcount hhalf hopen hsol rho.continuous hrhoEq hrhoMass hlower
    hdensity hE _ x hx
  intro y hy
  exact (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy).trans hgauge

theorem sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ x, rhoLower ≤ rho x)
    (houter : outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hinner : sixVertexRootDensityContractionRate c * outer +
        sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤
      inner) :
    ¬(inner < sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ∧
      sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho < outer) := by
  rintro ⟨hinnerGauge, hgaugeOuter⟩
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      outer := hgaugeOuter.le
  have houterNonneg : 0 ≤ outer :=
    (norm_nonneg (sixVertexWeightedFiniteDensityDifference
      hc N (n + 1) p rho)).trans hgauge
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N (n + 1) p x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N (n + 1) p).exists_mem_Ioc
        (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc
          y ≤ -Real.pi + 2 * Real.pi := hy.2
          _ = Real.pi := by ring
    have hyclose :=
      (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy').trans hgauge
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc p (hrho y) hyclose
    change rhoLower - outer / wmin ≤ _ at hx
    have houter' : outer ≤ rhoLower * wmin / 2 := by
      simpa [wmin] using houter
    have hquot : outer / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      nlinarith
    rw [hxy]
    linarith
  have himprove := sixVertexWeightedFiniteDensityGauge_selfImproves
    hc hN hcount hhalf hopen hsol rho hrhoEq hrhoMass
      (by linarith : 0 < rhoLower / 2) hdensity houterNonneg hgauge
  linarith

def sixVertexContinuumDensityAt
    {a b : Real}
    (rho : C(Set.Icc a b × Real, Real))
    (t : Set.Icc a b) : C(Real, Real) :=
  rho.comp ⟨fun x => (t, x),
    continuous_const.prodMk continuous_id⟩

def sixVertexContinuumDensitySection
    {a b : Real} {N n : Nat}
    (rho : C(Set.Icc a b × Real, Real))
    (z : SixVertexBetheContinuationSpace a b N n) : C(Real, Real) :=
  sixVertexContinuumDensityAt rho ⟨z.1.1, z.2.1⟩

def sixVertexContinuationWeightedFiniteDensityGauge
    {a b : Real} (ha : 2 < a) (N n : Nat)
    (rho : C(Set.Icc a b × Real, Real))
    (z : SixVertexBetheContinuationSpace a b N n) : Real :=
  sixVertexWeightedFiniteDensityGauge (ha.trans_le z.2.1.1)
    N n z.1.2 (sixVertexContinuumDensitySection rho z)

theorem continuous_sixVertexContinuationWeightedFiniteDensityGauge
    {a b : Real} (ha : 2 < a) (N n : Nat)
    (rho : C(Set.Icc a b × Real, Real)) :
    Continuous
      (sixVertexContinuationWeightedFiniteDensityGauge ha N n rho) := by
  let X := SixVertexBetheContinuationSpace a b N n
  let K := Set.Icc (-Real.pi) Real.pi
  have hweight : Continuous (fun zx : X × K =>
      sixVertexRootDensityWeight zx.1.1.1 zx.2.1) := by
    unfold sixVertexRootDensityWeight
    apply Continuous.div
    · unfold sixVertexBetheIntegratingFactor sixVertexDelta
      fun_prop
    · unfold sixVertexRootDensityScale sixVertexAnisotropyMagnitude
        sixVertexDelta
      fun_prop
    · intro zx
      exact (sixVertexRootDensityScale_pos
        (ha.trans_le zx.1.2.1.1)).ne'
  have hfinite : Continuous (fun zx : X × K =>
      sixVertexFiniteRootDensity zx.1.1.1 N n zx.1.1.2 zx.2.1) := by
    unfold sixVertexFiniteRootDensity
    apply Continuous.div_const
    apply Continuous.add continuous_const
    apply Continuous.div_const
    apply continuous_finsetSum
    intro k _
    apply Continuous.div
    · simp only [sixVertexDelta, sixVertexBetheIntegratingFactor]
      fun_prop
    · simp only [sixVertexThetaDerivativeDenominator,
        sixVertexThetaDenominator, sixVertexDelta]
      fun_prop
    · intro zx
      exact (sixVertexThetaDerivativeDenominator_pos
        (ha.trans_le zx.1.2.1.1) zx.2.1 (zx.1.1.2 k)).ne'
  have hrho : Continuous (fun zx : X × K =>
      rho (⟨zx.1.1.1, zx.1.2.1⟩, zx.2.1)) := by
    fun_prop
  have huncurry : Continuous (fun zx : X × K =>
      sixVertexRootDensityWeight zx.1.1.1 zx.2.1 *
        (sixVertexFiniteRootDensity zx.1.1.1 N n zx.1.1.2 zx.2.1 -
          rho (⟨zx.1.1.1, zx.1.2.1⟩, zx.2.1))) :=
    hweight.mul (hfinite.sub hrho)
  have hmap : Continuous (fun z : X =>
      sixVertexWeightedFiniteDensityDifference (ha.trans_le z.2.1.1)
        N n z.1.2 (sixVertexContinuumDensitySection rho z)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    simpa only [sixVertexWeightedFiniteDensityDifference,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply,
      ContinuousMap.coe_mk] using huncurry
  exact continuous_norm.comp hmap

theorem sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus
    {a b : Real} (ha : 2 < a) {N n r : Nat} (hN : 0 < N)
    (hr : r = n + 1)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFiniteDensityContinuumErrorOfLower
            t.1 N (rhoLower / 2) ≤ inner) :
    ∀ z : SixVertexBetheContinuationSpace a b N r,
      ¬(inner <
          sixVertexContinuationWeightedFiniteDensityGauge
            ha N r rho z ∧
        sixVertexContinuationWeightedFiniteDensityGauge
            ha N r rho z < outer) := by
  subst r
  intro z
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have htwo : 2 * (n + 1) ≤ N := by omega
  have hopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha htwo z.2
  have hsol : SixVertexSatisfiesBetheEquations
      z.1.1 N (n + 1) z.1.2 :=
    (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
    sixVertexContinuumDensitySection, t] using
    sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus
      hc hN hcount hhalf hopen hsol
      (sixVertexContinuumDensityAt rho t) (hrhoEq t) (hrhoMass t)
      hrhoLower (hrho t) (houter t) (hinner t)

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {rho : Real → Real} {rhoLower eta : Real}
    (hrhoLower : 0 < rhoLower)
    (hrho : ∀ x, rhoLower ≤ rho x)
    (heta : eta ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (m + m)
          (sixVertexEvenSymmetricLift m q) x - rho x)| ≤ eta)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N
        (rhoLower / 2) < 2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hdensityHalf : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N (m + m)
        (sixVertexEvenSymmetricLift m q) x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N (m + m)
        (sixVertexEvenSymmetricLift m q)).exists_mem_Ioc
          (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc
          y ≤ -Real.pi + 2 * Real.pi := hy.2
          _ = Real.pi := by ring
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc (sixVertexEvenSymmetricLift m q) (hrho y) (hclose y hy')
    dsimp [wmin] at hwmin
    change rhoLower - eta / wmin ≤ _ at hx
    have heta' : eta / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      calc
        eta ≤ rhoLower * wmin / 2 := by simpa [wmin] using heta
        _ = rhoLower / 2 * wmin := by ring
    rw [hxy]
    linarith
  exact sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    hc hm hN hcount hopen hsol (by linarith) hdensityHalf hmargin

theorem sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
    {a b : Real} (ha : 2 < a) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N) (hcount : m + m ≤ N)
    (rho : C(Set.Icc a b × Real, Real))
    {rhoLower outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z : SixVertexBetheContinuationSpace a b N (m + m))
    (hgauge : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z < outer) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  let q : Fin m → Real := sixVertexEvenPositiveHalfProjection m z.1.2
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have hpopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha hhalf z.2
  have hlift : sixVertexEvenSymmetricLift m q = z.1.2 :=
    sixVertexEvenSymmetricLift_projection m hpopen.2.1
  have hsol : SixVertexSatisfiesBetheEquations z.1.1 N (m + m) z.1.2 :=
    (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  have hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight z.1.1 x *
        (sixVertexFiniteRootDensity z.1.1 N (m + m)
          (sixVertexEvenSymmetricLift m q) x -
            sixVertexContinuumDensityAt rho t x)| ≤ outer := by
    intro x hx
    have hpoint := abs_weightedFiniteDensity_sub_le_gauge
      hc (N := N) z.1.2 (sixVertexContinuumDensitySection rho z) x hx
    have hle := hpoint.trans hgauge.le
    simpa only [hlift, sixVertexContinuumDensitySection, t] using hle
  have hopenLift : SixVertexOpenRootSimplex
      (sixVertexEvenSymmetricLift m q) := by
    rw [hlift]
    exact hpopen
  have hsolLift : SixVertexSatisfiesBetheEquations z.1.1 N (m + m)
      (sixVertexEvenSymmetricLift m q) := by
    rw [hlift]
    exact hsol
  change Function.Injective
    (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 q)
  exact sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    hc hm hN hcount hopenLift hsolLift hrhoLower (hrho t) (houter t)
      hclose (hmargin t)

theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_densityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : N = 2 * (m + m))
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (hio : inner < outer)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFiniteDensityContinuumErrorOfLower
            t.1 N (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
  let k := m + m - 1
  have hk : k + 1 = m + m := by
    dsimp [k]
    omega
  have hrootCount : m + m ≤ N := by omega
  have hcover : 2 * (m + m) ≤ N := by omega
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus
        ha hN (n := k) (r := m + m) hk.symm (by omega) (by omega)
          rho hrhoEq hrhoMass
          hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hrootCount rho hrhoLower hrho houter hmargin z hzg
  exact exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

end

end StatMech.FrontierD
