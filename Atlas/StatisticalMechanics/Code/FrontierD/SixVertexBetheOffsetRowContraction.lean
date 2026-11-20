/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetSymmetry
import Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature
import Code.FrontierD.SixVertexBetheEvenRootOffsetBound





namespace StatMech.FrontierD

open Finset
open Filter Topology

noncomputable section



def sixVertexFixedChargeOffsetRowError
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  (sixVertexOffsetQuotientLipschitzNNReal c lower 1 0 : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) / lower)



def sixVertexFixedChargeOffsetContractionMargin (c : Real) : Real :=
  sixVertexRootDensityKernelFloor c * sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)

theorem sixVertexFixedChargeOffsetContractionMargin_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexFixedChargeOffsetContractionMargin c := by
  unfold sixVertexFixedChargeOffsetContractionMargin
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    positivity
  exact div_pos
    (mul_pos (sixVertexRootDensityKernelFloor_pos hc)
      (sixVertexRootDensityScale_pos hc))
    (mul_pos (mul_pos (by norm_num)
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])) hU)

theorem tendsto_sixVertexFixedChargeOffsetRowError
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    Tendsto (fun k => sixVertexFixedChargeOffsetRowError c
      (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c))
      atTop (nhds 0) := by
  let lower := sixVertexTailFiniteDensityFloor c
  let C := (sixVertexOffsetQuotientLipschitzNNReal c lower 1 0 : Real) *
      sixVertexFiniteRootDensityUniformBound c *
        ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
    2 * (r : Real) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) / lower)
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  convert hzero using 1
  funext k
  dsimp [C, lower]
  unfold sixVertexFixedChargeOffsetRowError
  field_simp [hlower.ne']

theorem eventually_sixVertexFixedChargeOffsetRowError_le_halfMargin
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexFixedChargeOffsetRowError c (sixVertexFourWidth r k) r
          (sixVertexTailFiniteDensityFloor c) ≤
        sixVertexFixedChargeOffsetContractionMargin c / 2 := by
  have hmargin := sixVertexFixedChargeOffsetContractionMargin_pos hc
  exact (tendsto_sixVertexFixedChargeOffsetRowError hc htail r).eventually
    (Iic_mem_nhds (half_pos hmargin))



theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos
    {c : Real} (hc : 2 < c) {N m r : Nat} (hN : 0 < N) (hm : 0 < m)
    (hcharge : N = 2 * m + 2 * r) {p : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N m p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N m p y)
    (x : Real) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) /
          sixVertexFiniteRootDensity c N m p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y| ≤
      sixVertexFixedChargeOffsetRowError c N r lower := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_of_lipschitz
      hc hN hcharge hopen hsol hlower hdensity x
      (tau := fun _ : Real => 1) (D := 0) (G := 1)
      (LipschitzWith.const 1) (by intro y; rfl) (by simp)
  simpa [sixVertexFixedChargeOffsetRowError] using h



theorem empiricalContinuousOffsetKernel_fixedCharge_le
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r k : Nat)
    (i : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    (1 / (sixVertexFourWidth r k : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc r k i)
            (sixVertexFixedChargeBetheRoots hc r k j) /
          sixVertexFiniteRootDensity c (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k)
            (sixVertexFixedChargeBetheRoots hc r k)
            (sixVertexFixedChargeBetheRoots hc r k j) ≤
      2 * Real.pi + sixVertexFixedChargeOffsetRowError c
        (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c) := by
  let N := sixVertexFourWidth r k
  let m := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let lower := sixVertexTailFiniteDensityFloor c
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hm : 0 < m := sixVertexFixedChargeBetheParticleCount_pos r k
  have hcharge : N = 2 * m + 2 * r := by
    dsimp [N, m]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hdensity : ∀ y, lower ≤ sixVertexFiniteRootDensity c N m p y := by
    intro y
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le r k) p y
  have hquad := abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos
    hc hN hm hcharge (sixVertexFixedChargeBetheRoots_mem_open hc r k)
      (sixVertexFixedChargeBetheRoots_is_solution hc r k) hlower hdensity
      (p i)
  have hint : (∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c (p i) y) = 2 * Real.pi := by
    unfold sixVertexContinuousOffsetKernel
    exact intervalIntegral_sixVertexRootDensityKernel_div_weight hc (p i)
  rw [hint] at hquad
  change |(∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
      sixVertexFiniteRootDensity c N m p (p j)) / N - 2 * Real.pi| ≤ _
    at hquad
  have hle := (le_abs_self
    ((∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
      sixVertexFiniteRootDensity c N m p (p j)) / N - 2 * Real.pi)).trans
      hquad
  change (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N m p (p j) ≤ _
  rw [show (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N m p (p j) =
      (∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N m p (p j)) / N by ring]
  linarith



theorem reciprocalWeightDensityMass_fixedCharge_le
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r k : Nat) :
    sixVertexRootDensityScale c /
        (4 * (sixVertexAnisotropyMagnitude c + 1) *
          sixVertexFiniteRootDensityUniformBound c) ≤
      (1 / (sixVertexFourWidth r k : Real)) * ∑ j,
        1 / (sixVertexRootDensityWeight c
            (sixVertexFixedChargeBetheRoots hc r k j) *
          sixVertexFiniteRootDensity c (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k)
            (sixVertexFixedChargeBetheRoots hc r k)
            (sixVertexFixedChargeBetheRoots hc r k j)) := by
  let N := sixVertexFourWidth r k
  let m := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let U := sixVertexFiniteRootDensityUniformBound c
  let A := sixVertexRootDensityScale c /
    (sixVertexAnisotropyMagnitude c + 1)
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hU : 0 < U := by
    dsimp [U, sixVertexFiniteRootDensityUniformBound]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (sixVertexRootDensityScale_pos hc)
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc])
  have hdensityPos (j : Fin m) : 0 <
      sixVertexFiniteRootDensity c N m p (p j) :=
    (sixVertexTailFiniteDensityFloor_pos hc htail).trans_le
      (sixVertexTailFiniteDensityFloor_le hc hN
        (sixVertexFixedChargeBetheParticleCount_twice_le r k) p (p j))
  have hdensityUpper (j : Fin m) :
      sixVertexFiniteRootDensity c N m p (p j) ≤ U := by
    have hmN : m ≤ N := by
      have htwice := sixVertexFixedChargeBetheParticleCount_twice_le r k
      dsimp [m, N]
      omega
    exact (le_abs_self _).trans
      (abs_sixVertexFiniteRootDensity_le hc hN hmN p (p j))
  have hterm (j : Fin m) : A / U ≤
      1 / (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N m p (p j)) := by
    have hw := sixVertexRootDensity_reciprocalWeight_lower hc (p j)
    change A ≤ 1 / sixVertexRootDensityWeight c (p j) at hw
    have hrho : 1 / U ≤
        1 / sixVertexFiniteRootDensity c N m p (p j) := by
      exact one_div_le_one_div_of_le (hdensityPos j) (hdensityUpper j)
    have hInvU : 0 ≤ 1 / U := (one_div_pos.mpr hU).le
    have hInvW : 0 ≤ 1 / sixVertexRootDensityWeight c (p j) :=
      (one_div_pos.mpr (sixVertexRootDensityWeight_pos hc (p j))).le
    have hmul := mul_le_mul hw hrho hInvU hInvW
    calc
      A / U = A * (1 / U) := by ring
      _ ≤ (1 / sixVertexRootDensityWeight c (p j)) *
          (1 / sixVertexFiniteRootDensity c N m p (p j)) := hmul
      _ = 1 / (sixVertexRootDensityWeight c (p j) *
          sixVertexFiniteRootDensity c N m p (p j)) := by
        field_simp [(sixVertexRootDensityWeight_pos hc (p j)).ne',
          (hdensityPos j).ne']
  have hsum : (m : Real) * (A / U) ≤ ∑ j : Fin m,
      1 / (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N m p (p j)) := by
    calc
      (m : Real) * (A / U) = ∑ _j : Fin m, A / U := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j
  have hratio : (1 / 4 : Real) ≤ (m : Real) / N := by
    apply (le_div_iff₀ hNreal).2
    have hnat : N ≤ 4 * m := by
      dsimp [m, N]
      rw [sixVertexFixedChargeBetheParticleCount_eq]
      unfold sixVertexFourWidth
      omega
    have hnatR : (N : Real) ≤ 4 * (m : Real) := by exact_mod_cast hnat
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity :
    0 ≤ (1 / (N : Real)))
  rw [show sixVertexRootDensityScale c /
      (4 * (sixVertexAnisotropyMagnitude c + 1) *
        sixVertexFiniteRootDensityUniformBound c) = A / (4 * U) by
    dsimp [A, U]
    field_simp [hU.ne',
      (by linarith [one_lt_sixVertexAnisotropyMagnitude hc] :
        sixVertexAnisotropyMagnitude c + 1 ≠ 0)]]
  change A / (4 * U) ≤ (1 / (N : Real)) * ∑ j,
      1 / (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N m p (p j))
  calc
    A / (4 * U) = (1 / 4 : Real) * (A / U) := by ring
    _ ≤ ((m : Real) / N) * (A / U) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = (1 / (N : Real)) * ((m : Real) * (A / U)) := by ring
    _ ≤ _ := hscaled



theorem abs_empiricalContinuousOffsetKernel_mul_fixedCharge_le
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r k : Nat)
    {e : Fin (sixVertexFixedChargeBetheParticleCount r k) → Real}
    {E : Real} (hE : 0 ≤ E) (he : ∀ j, |e j| ≤ E)
    (hmass : (1 / (sixVertexFourWidth r k : Real)) * ∑ j,
      e j / (sixVertexRootDensityWeight c
          (sixVertexFixedChargeBetheRoots hc r k j) *
        sixVertexFiniteRootDensity c (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheRoots hc r k)
          (sixVertexFixedChargeBetheRoots hc r k j)) = 0)
    (i : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    |(1 / (sixVertexFourWidth r k : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc r k i)
            (sixVertexFixedChargeBetheRoots hc r k j) /
          sixVertexFiniteRootDensity c (sixVertexFourWidth r k)
            (sixVertexFixedChargeBetheParticleCount r k)
            (sixVertexFixedChargeBetheRoots hc r k)
            (sixVertexFixedChargeBetheRoots hc r k j) * e j| ≤
      (2 * Real.pi + sixVertexFixedChargeOffsetRowError c
          (sixVertexFourWidth r k) r (sixVertexTailFiniteDensityFloor c) -
        sixVertexFixedChargeOffsetContractionMargin c) * E := by
  let N := sixVertexFourWidth r k
  let n := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let rho : Fin n → Real := fun j =>
    sixVertexFiniteRootDensity c N n p (p j)
  let L := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hrho : ∀ j, 0 < rho j := by
    intro j
    exact (sixVertexTailFiniteDensityFloor_pos hc htail).trans_le
      (sixVertexTailFiniteDensityFloor_le hc hN
        (sixVertexFixedChargeBetheParticleCount_twice_le r k) p (p j))
  have hrow := empiricalContinuousOffsetKernel_fixedCharge_le
    hc htail r k i
  have hreciprocal := reciprocalWeightDensityMass_fixedCharge_le
    hc htail r k
  have h := abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass
    hc hN (p := p) (rho := rho) (e := e) (i := i) hrho hE he hmass
      hrow hreciprocal
  have hmargin : sixVertexRootDensityKernelFloor c * L =
      sixVertexFixedChargeOffsetContractionMargin c := by
    dsimp [L]
    unfold sixVertexFixedChargeOffsetContractionMargin
    ring
  rw [hmargin] at h
  simpa [N, n, p, rho, L,
    sixVertexFixedChargeOffsetContractionMargin, mul_assoc] using h

end

end StatMech.FrontierD
