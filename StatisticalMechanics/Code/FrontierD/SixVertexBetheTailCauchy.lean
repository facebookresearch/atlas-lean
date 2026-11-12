/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailConvolution









namespace StatMech.FrontierD

noncomputable section

def sixVertexTailConvolutionError (c : Real) (N : Nat) : Real :=
  sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
        (2 * Real.pi)

def sixVertexFiniteConvolutionDefect
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (∑ j, sixVertexRootDensityKernel c x (p j)) / N -
    ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c x y *
        sixVertexFiniteRootDensity c N n p y

theorem abs_sixVertexFiniteConvolutionDefect_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (x : Real) :
    |sixVertexFiniteConvolutionDefect c N (n + 1) p x| <=
      sixVertexTailConvolutionError c N := by
  exact abs_empiricalKernel_sub_finiteDensityIntegral_le_tail
    hc htail hN hhalf hopen hsol x

theorem intervalIntegral_halfFilledFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) (p : Fin (n + 1) → Real) :
    ∫ x in -Real.pi..Real.pi,
        sixVertexFiniteRootDensity c N (n + 1) p x = 1 / 2 := by
  rw [intervalIntegral_sixVertexFiniteRootDensity hc hN p]
  have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by
    exact_mod_cast hhalf
  rw [hhalfReal]
  have hn : (0 : Real) < n + 1 := by positivity
  push_cast
  field_simp [hn.ne']
  ring



theorem sixVertexFiniteRootDensity_weighted_sub_le_of_bound_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n M m : Nat} (hN : 0 < N) (hM : 0 < M)
    (hhalfN : N = 2 * (n + 1)) (hhalfM : M = 2 * (m + 1))
    {p : Fin (n + 1) → Real} {q : Fin (m + 1) → Real}
    (hpopen : SixVertexOpenRootSimplex p)
    (hqopen : SixVertexOpenRootSimplex q)
    (hpsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (hqsol : SixVertexSatisfiesBetheEquations c M (m + 1) q)
    {E : Real} (hE : 0 <= E)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c N (n + 1) p y -
          sixVertexFiniteRootDensity c M (m + 1) q y)| <= E)
    (x : Real) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x -
          sixVertexFiniteRootDensity c M (m + 1) q x)| <=
      sixVertexRootDensityContractionRate c * E +
        (sixVertexTailConvolutionError c N +
          sixVertexTailConvolutionError c M) / (2 * Real.pi) := by
  let rhoP := sixVertexFiniteRootDensity c N (n + 1) p
  let rhoQ := sixVertexFiniteRootDensity c M (m + 1) q
  let e : Real → Real := fun y =>
    sixVertexRootDensityWeight c y * (rhoP y - rhoQ y)
  let DP := sixVertexFiniteConvolutionDefect c N (n + 1) p
  let DQ := sixVertexFiniteConvolutionDefect c M (m + 1) q
  let IP : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c z y * rhoP y
  let IQ : Real → Real := fun z =>
    ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c z y * rhoQ y
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hrhoP : Continuous rhoP :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hrhoQ : Continuous rhoQ :=
    continuous_sixVertexFiniteRootDensity hc M (m + 1) q
  have he : Continuous e := hweightCont.mul (hrhoP.sub hrhoQ)
  have hrhoPInt : IntervalIntegrable rhoP MeasureTheory.volume
      (-Real.pi) Real.pi := hrhoP.intervalIntegrable _ _
  have hrhoQInt : IntervalIntegrable rhoQ MeasureTheory.volume
      (-Real.pi) Real.pi := hrhoQ.intervalIntegrable _ _
  have hmass :
      ∫ y in -Real.pi..Real.pi,
        e y / sixVertexRootDensityWeight c y = 0 := by
    have heq : (fun y => e y / sixVertexRootDensityWeight c y) =
        fun y => rhoP y - rhoQ y := by
      funext y
      dsimp [e]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    rw [heq, intervalIntegral.integral_sub hrhoPInt hrhoQInt]
    rw [show (∫ y in -Real.pi..Real.pi, rhoP y) = 1 / 2 by
      exact intervalIntegral_halfFilledFiniteRootDensity hc hN hhalfN p]
    rw [show (∫ y in -Real.pi..Real.pi, rhoQ y) = 1 / 2 by
      exact intervalIntegral_halfFilledFiniteRootDensity hc hM hhalfM q]
    ring
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE hmass
    (by simpa [e, rhoP, rhoQ] using hbound) x
  have hDP : |DP x| <= sixVertexTailConvolutionError c N :=
    abs_sixVertexFiniteConvolutionDefect_le_tail
      hc htail hN hhalfN hpopen hpsol x
  have hDQ : |DQ x| <= sixVertexTailConvolutionError c M :=
    abs_sixVertexFiniteConvolutionDefect_le_tail
      hc htail hM hhalfM hqopen hqsol x
  have hIPint : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rhoP y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.mul
      hrhoP).intervalIntegrable _ _
  have hIQint : IntervalIntegrable
      (fun y => sixVertexRootDensityKernel c x y * rhoQ y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.mul
      hrhoQ).intervalIntegrable _ _
  have hJ :
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) = IP x - IQ x := by
    rw [show (fun y =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      fun y => sixVertexRootDensityKernel c x y * (rhoP y - rhoQ y) by
        funext y
        dsimp [e]
        field_simp [(sixVertexRootDensityWeight_pos hc y).ne']]
    rw [show (fun y =>
        sixVertexRootDensityKernel c x y * (rhoP y - rhoQ y)) =
      fun y => sixVertexRootDensityKernel c x y * rhoP y -
        sixVertexRootDensityKernel c x y * rhoQ y by
          funext y
          ring]
    rw [intervalIntegral.integral_sub hIPint hIQint]
  have hpEq : sixVertexRootDensityWeight c x * rhoP x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IP x -
          (1 / (2 * Real.pi)) * DP x := by
    have hp := sixVertexRootDensityWeight_mul_finiteRootDensity
      hc hN p x
    dsimp [rhoP, IP, DP, sixVertexFiniteConvolutionDefect]
    rw [hp]
    field_simp [Real.pi_ne_zero, (by exact_mod_cast hN.ne' : (N : Real) ≠ 0)]
    ring
  have hqEq : sixVertexRootDensityWeight c x * rhoQ x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) * IQ x -
          (1 / (2 * Real.pi)) * DQ x := by
    have hq := sixVertexRootDensityWeight_mul_finiteRootDensity
      hc hM q x
    dsimp [rhoQ, IQ, DQ, sixVertexFiniteConvolutionDefect]
    rw [hq]
    field_simp [Real.pi_ne_zero, (by exact_mod_cast hM.ne' : (M : Real) ≠ 0)]
    ring
  have heqPoint : e x =
      -(1 / (2 * Real.pi)) * (IP x - IQ x) -
        (1 / (2 * Real.pi)) * (DP x - DQ x) := by
    dsimp [e]
    rw [mul_sub, hpEq, hqEq]
    ring
  change |e x| <= _
  rw [heqPoint, ← hJ]
  calc
    |-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y) -
        (1 / (2 * Real.pi)) * (DP x - DQ x)| <=
        |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y)| +
        |(1 / (2 * Real.pi)) * (DP x - DQ x)| := by
      simpa [abs_neg] using abs_add_le
        (-(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e y))
        (-(1 / (2 * Real.pi)) * (DP x - DQ x))
    _ <= sixVertexRootDensityContractionRate c * E +
        (sixVertexTailConvolutionError c N +
          sixVertexTailConvolutionError c M) / (2 * Real.pi) := by
      apply add_le_add hcontract
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      calc
        (1 / (2 * Real.pi)) * |DP x - DQ x| <=
            (1 / (2 * Real.pi)) * (|DP x| + |DQ x|) := by
          gcongr
          exact abs_sub _ _
        _ <= (1 / (2 * Real.pi)) *
            (sixVertexTailConvolutionError c N +
              sixVertexTailConvolutionError c M) := by
          gcongr
        _ = (sixVertexTailConvolutionError c N +
            sixVertexTailConvolutionError c M) / (2 * Real.pi) := by ring



theorem sixVertexFiniteRootDensity_weighted_cauchy_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n M m : Nat} (hN : 0 < N) (hM : 0 < M)
    (hhalfN : N = 2 * (n + 1)) (hhalfM : M = 2 * (m + 1))
    {p : Fin (n + 1) → Real} {q : Fin (m + 1) → Real}
    (hpopen : SixVertexOpenRootSimplex p)
    (hqopen : SixVertexOpenRootSimplex q)
    (hpsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (hqsol : SixVertexSatisfiesBetheEquations c M (m + 1) q) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (n + 1) p x -
          sixVertexFiniteRootDensity c M (m + 1) q x)| <=
      ((sixVertexTailConvolutionError c N +
          sixVertexTailConvolutionError c M) / (2 * Real.pi)) /
        (1 - sixVertexRootDensityContractionRate c) := by
  let e : Real → Real := fun x =>
    sixVertexRootDensityWeight c x *
      (sixVertexFiniteRootDensity c N (n + 1) p x -
        sixVertexFiniteRootDensity c M (m + 1) q x)
  have he : Continuous e := by
    dsimp [e]
    apply Continuous.mul
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · exact (continuous_sixVertexFiniteRootDensity hc N (n + 1) p).sub
        (continuous_sixVertexFiniteRootDensity hc M (m + 1) q)
  have hnonempty : (Set.Icc (-Real.pi) Real.pi).Nonempty :=
    Set.nonempty_Icc.2 (by linarith [Real.pi_pos])
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty
    he.abs.continuousOn
  let E := |e x0|
  have hE : 0 <= E := abs_nonneg _
  have hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| <= E :=
    fun y hy => hmax hy
  have hpoint := sixVertexFiniteRootDensity_weighted_sub_le_of_bound_tail
    hc htail hN hM hhalfN hhalfM hpopen hqopen hpsol hqsol hE
    (by simpa [e] using hbound) x0
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hden : 0 < 1 - sixVertexRootDensityContractionRate c := by
    linarith [hrate.2]
  have hEbound : E <=
      ((sixVertexTailConvolutionError c N +
          sixVertexTailConvolutionError c M) / (2 * Real.pi)) /
        (1 - sixVertexRootDensityContractionRate c) := by
    change E <= _
    rw [le_div_iff₀ hden]
    change |e x0| * (1 - sixVertexRootDensityContractionRate c) <= _
    change |e x0| <= _ at hpoint
    dsimp [E] at hpoint
    nlinarith
  intro x hx
  exact (hbound x hx).trans hEbound




theorem sixVertexFiniteRootDensity_weighted_cauchy_of_pos_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n M m : Nat} (hN : 0 < N) (hM : 0 < M)
    (hn : 0 < n) (hm : 0 < m)
    (hhalfN : N = 2 * n) (hhalfM : M = 2 * m)
    {p : Fin n -> Real} {q : Fin m -> Real}
    (hpopen : SixVertexOpenRootSimplex p)
    (hqopen : SixVertexOpenRootSimplex q)
    (hpsol : SixVertexSatisfiesBetheEquations c N n p)
    (hqsol : SixVertexSatisfiesBetheEquations c M m q) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x -
          sixVertexFiniteRootDensity c M m q x)| <=
      ((sixVertexTailConvolutionError c N +
          sixVertexTailConvolutionError c M) / (2 * Real.pi)) /
        (1 - sixVertexRootDensityContractionRate c) := by
  cases n with
  | zero => omega
  | succ n =>
      cases m with
      | zero => omega
      | succ m =>
          exact sixVertexFiniteRootDensity_weighted_cauchy_tail
            hc htail hN hM hhalfN hhalfM hpopen hqopen hpsol hqsol

end

end StatMech.FrontierD
