/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetTestQuadrature










open scoped BigOperators
open Finset

namespace StatMech.FrontierD

noncomputable section

theorem sum_cyclicRootPartition_eq_sum_roots_add_boundary
    {n : Nat} (p : Fin (n + 1) -> Real) (f : Real -> Real) :
    (∑ k ∈ range (n + 1), f (sixVertexCyclicRootPartition p k)) =
      (∑ j, f (p j)) +
        f (p (Fin.last n) - 2 * Real.pi) - f (p (Fin.last n)) := by
  rw [Finset.sum_range_succ', sixVertexCyclicRootPartition_zero]
  have hmid :
      (∑ k ∈ range n, f (sixVertexCyclicRootPartition p (k + 1))) =
        ∑ j : Fin n, f (p j.castSucc) := by
    apply Finset.sum_bij
      (fun k hk => ⟨k, Finset.mem_range.mp hk⟩ :
        (k : Nat) -> k ∈ Finset.range n -> Fin n)
    · intro k hk
      exact Finset.mem_univ _
    · intro a ha b hb hab
      exact congrArg Fin.val hab
    · intro j _
      refine ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
      exact Fin.ext rfl
    · intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      rw [sixVertexCyclicRootPartition_succ p hklt.le]
      rfl
  rw [hmid, Fin.sum_univ_castSucc]
  ring

private theorem abs_intervalIntegral_le_const_mul_length
    {f : Real -> Real} {a b H : Real} (hab : a <= b)
    (hbound : forall x, |f x| <= H) :
    |∫ x in a..b, f x| <= H * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := H) (f := f) (fun x _ => by
      simpa only [Real.norm_eq_abs] using hbound x)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h




theorem abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
    {c : Real} (hc : 2 < c) {N n r : Nat} (hN : 0 < N)
    (hcharge : N = 2 * (n + 1) + 2 * r)
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x,
      lower <= sixVertexFiniteRootDensity c N (n + 1) p x)
    {f : Real -> Real} {C : NNReal} {F : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hfBound : forall x, |f x| <= F) :
    |(∑ j, f (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c N (n + 1) p y| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
            (2 * Real.pi) +
        (2 * (r : Real) / N) * F +
        2 * F / N +
        sixVertexFiniteRootDensityUniformBound c * F *
          ((2 * (r : Real) + 1) / ((N : Real) * lower)) := by
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let a := p (Fin.last n) - 2 * Real.pi
  let b := p (Fin.last n)
  let mesh := (2 * (r : Real) + 1) / ((N : Real) * lower)
  let U := (∑ j, f (p j)) / (N : Real)
  let V := ∑ k ∈ range (n + 1),
    (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k)
  let Ic := ∫ y in a..b, f y * rho y
  let I := ∫ y in -Real.pi..Real.pi, f y * rho y
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hF : 0 <= F := (abs_nonneg (f 0)).trans (hfBound 0)
  have hB : 0 <= sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hmesh : 0 <= mesh := by
    dsimp [mesh]
    positivity
  have hmeshBound := sixVertexCyclicRootPartition_mesh_fixedCharge
    hc hN hcharge hopen hsol hlower hdensity
  have hquad :=
    abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_fixedCharge
      hc hN hcharge hopen hsol hmeshBound hf hlip hfBound
  have hquad' : |V - Ic| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh *
          (2 * Real.pi) + (2 * (r : Real) / N) * F := by
    simpa [V, Ic, a, b, mesh, sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_end] using hquad
  have hsymm : p 0 = -p (Fin.last n) := by
    simpa using hopen.2.1 (Fin.last n)
  have hbpi : b < Real.pi := by
    dsimp [b]
    exact (hopen.2.2 (Fin.last n)).2
  have hapi : a < -Real.pi := by
    dsimp [a]
    linarith [hbpi]
  have hgap : 2 * (Real.pi - b) <= mesh := by
    have hboundary := hmeshBound 0 (by omega)
    rw [sixVertexCyclicRootPartition_zero,
      sixVertexCyclicRootPartition_succ p (Nat.zero_le n)] at hboundary
    dsimp [a, b, mesh] at hboundary ⊢
    rw [hsymm] at hboundary
    linarith
  have hrhoCont : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hgCont : Continuous (fun y => f y * rho y) := hf.mul hrhoCont
  have hgBound : forall y,
      |f y * rho y| <= sixVertexFiniteRootDensityUniformBound c * F := by
    intro y
    rw [abs_mul]
    calc
      |f y| * |rho y| <= F * sixVertexFiniteRootDensityUniformBound c :=
        mul_le_mul (hfBound y)
          (abs_sixVertexFiniteRootDensity_le hc hN (by omega) p y)
          (abs_nonneg _) hF
      _ = sixVertexFiniteRootDensityUniformBound c * F := mul_comm _ _
  have hleft := abs_intervalIntegral_le_const_mul_length
    hapi.le hgBound
  have hright := abs_intervalIntegral_le_const_mul_length
    hbpi.le hgBound
  have hIcI : |Ic - I| <=
      sixVertexFiniteRootDensityUniformBound c * F * mesh := by
    have hsplitC := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (b := -Real.pi)
      (hgCont.intervalIntegrable a (-Real.pi))
      (hgCont.intervalIntegrable (-Real.pi) b)
    have hsplitI := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (b := b)
      (hgCont.intervalIntegrable (-Real.pi) b)
      (hgCont.intervalIntegrable b Real.pi)
    have hid : Ic - I =
        (∫ y in a..-Real.pi, f y * rho y) -
          ∫ y in b..Real.pi, f y * rho y := by
      dsimp [Ic, I]
      rw [← hsplitC, ← hsplitI]
      ring
    rw [hid]
    calc
      _ <= |∫ y in a..-Real.pi, f y * rho y| +
          |∫ y in b..Real.pi, f y * rho y| := abs_sub _ _
      _ <= (sixVertexFiniteRootDensityUniformBound c * F) *
              (-Real.pi - a) +
            (sixVertexFiniteRootDensityUniformBound c * F) *
              (Real.pi - b) := add_le_add hleft hright
      _ = sixVertexFiniteRootDensityUniformBound c * F *
            (2 * (Real.pi - b)) := by
          dsimp [a]
          ring
      _ <= sixVertexFiniteRootDensityUniformBound c * F * mesh := by
          exact mul_le_mul_of_nonneg_left hgap (mul_nonneg hB hF)
  have hVU : |V - U| <= 2 * F / N := by
    have hsum := sum_cyclicRootPartition_eq_sum_roots_add_boundary p f
    have hdiff : V - U =
        (f a - f b) / (N : Real) := by
      dsimp [V, U, a, b]
      rw [← Finset.mul_sum, hsum]
      ring
    rw [hdiff, abs_div, abs_of_pos hNreal]
    calc
      |f a - f b| / (N : Real) <=
          (|f a| + |f b|) / (N : Real) :=
        div_le_div_of_nonneg_right (abs_sub _ _) hNreal.le
      _ <= (F + F) / (N : Real) :=
        div_le_div_of_nonneg_right
          (add_le_add (hfBound a) (hfBound b)) hNreal.le
      _ = 2 * F / (N : Real) := by ring
  change |U - I| <= _
  calc
    |U - I| = |-(V - U) + (V - Ic) + (Ic - I)| := by ring_nf
    _ <= |V - U| + |V - Ic| + |Ic - I| := by
      calc
        _ <= |-(V - U)| + |V - Ic| + |Ic - I| :=
          (abs_add_three _ _ _)
        _ = _ := by rw [abs_neg]
    _ <= 2 * F / N +
          ((C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh *
            (2 * Real.pi) + (2 * (r : Real) / N) * F) +
          sixVertexFiniteRootDensityUniformBound c * F * mesh :=
      add_le_add (add_le_add hVU hquad') hIcI
    _ = _ := by
      dsimp [mesh]
      ring

def sixVertexFixedChargeNonperiodicOffsetTestError
    (c : Real) (N r : Nat) (lower G : Real) (D : NNReal) : Real :=
  sixVertexFixedChargeOffsetTestError c N r lower G D +
    2 * ((sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) * G / lower) / N +
    sixVertexFiniteRootDensityUniformBound c *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * G / lower) *
      ((2 * (r : Real) + 1) / ((N : Real) * lower))



theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
    {c : Real} (hc : 2 < c) {N m r : Nat} (hN : 0 < N) (hm : 0 < m)
    (hcharge : N = 2 * m + 2 * r) {p : Fin m -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N m p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N m p y)
    (x : Real) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) /
          sixVertexFiniteRootDensity c N m p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y| <=
      sixVertexFixedChargeNonperiodicOffsetTestError c N r lower G D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let f : Real -> Real := fun y =>
    sixVertexContinuousOffsetKernel c x y * tau y / rho y
  let F := (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) * G / lower
  have hrho : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hkernel : Continuous (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      (by
        unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
          sixVertexRootDensityScale
        fun_prop)
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hf : Continuous f :=
    (hkernel.mul htauLip.continuous).div hrho
      (fun y => (hlower.trans_le (hdensity y)).ne')
  have hfLip : LipschitzWith
      (sixVertexOffsetQuotientLipschitzNNReal c lower G D) f := by
    exact lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity
      hc hN (by omega) p hlower hdensity htauLip htauBound x
  have hfBound : forall y, |f y| <= F := by
    intro y
    have hkernelBound := abs_sixVertexRootDensityKernel_div_weight_le hc x y
    have hrhoLower := hdensity y
    have hrhoPos : 0 < rho y := hlower.trans_le hrhoLower
    have hG : 0 <= G := (abs_nonneg (tau 0)).trans (htauBound 0)
    have hratio : 0 <= sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      positivity
    dsimp [f, F]
    rw [abs_div, abs_mul, abs_of_pos hrhoPos]
    have hprod := mul_le_mul hkernelBound (htauBound y)
      (abs_nonneg _) hratio
    calc
      |sixVertexContinuousOffsetKernel c x y| * |tau y| / rho y <=
          ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / rho y :=
        div_le_div_of_nonneg_right hprod hrhoPos.le
      _ <= ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / lower :=
        div_le_div_of_nonneg_left (mul_nonneg hratio hG) hlower hrhoLower
  have hquad :=
    abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hopen hsol hlower hdensity hf hfLip hfBound
  change |(∑ j, f (p j)) / N -
      ∫ y in -Real.pi..Real.pi, f y * rho y| <= _ at hquad
  have hintegral :
      (∫ y in -Real.pi..Real.pi, f y * rho y) =
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [f, rho]
    field_simp [(hlower.trans_le (hdensity y)).ne']
  rw [hintegral] at hquad
  simpa [f, F, sixVertexFixedChargeNonperiodicOffsetTestError,
    sixVertexFixedChargeOffsetTestError] using hquad

theorem tendsto_sixVertexFixedChargeNonperiodicOffsetTestError
    (c : Real) (r : Nat) {lower : Real} (hlower : 0 < lower)
    (G : Real) (D : NNReal) :
    Filter.Tendsto (fun k => sixVertexFixedChargeNonperiodicOffsetTestError c
      (sixVertexFourWidth r k) r lower G D) Filter.atTop (nhds 0) := by
  let F := (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) * G / lower
  let E := 2 * F +
    sixVertexFiniteRootDensityUniformBound c * F *
      ((2 * (r : Real) + 1) / lower)
  have hwidthNat : Filter.Tendsto (sixVertexFourWidth r)
      Filter.atTop Filter.atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Filter.Tendsto
      (fun k : Nat => (sixVertexFourWidth r k : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hbase := tendsto_sixVertexFixedChargeOffsetTestError
    c r hlower G D
  have hextra : Filter.Tendsto
      (fun k : Nat => E / (sixVertexFourWidth r k : Real))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  have hadd := hbase.add hextra
  have hfun :
      (fun k => sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth r k) r lower G D) =
      (fun k => sixVertexFixedChargeOffsetTestError c
          (sixVertexFourWidth r k) r lower G D +
        E / (sixVertexFourWidth r k : Real)) := by
    funext k
    dsimp [E, F]
    unfold sixVertexFixedChargeNonperiodicOffsetTestError
    field_simp [hlower.ne']
    ring
  rw [hfun]
  simpa only [add_zero] using hadd

end

end StatMech.FrontierD
