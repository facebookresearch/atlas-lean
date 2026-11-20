/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensity
import Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddCountingAverage
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) : Real :=
  sixVertexBetheCountingFunction c
      (sixVertexFourWidth (2 * s + 1) k)
      ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x / x

theorem tendsto_sixVertexCanonicalOddCountingAverage_firstLeft
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => sixVertexCanonicalOddCountingAverage hc s k
      (sixVertexCanonicalOddLeftHalfRoot hc s k
        (0 : Fin (s + k + 1)))) atTop
      (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
  let C : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let first : Nat -> Real := fun k =>
    sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))
  let rho0 : Nat -> Real := fun k =>
    sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
      ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) 0
  have hfirst : Tendsto first atTop (nhds 0) :=
    tendsto_sixVertexCanonicalOddFirstLeftHalfRoot hc s
  have hmajor : Tendsto (fun k => C * first k) atTop (nhds 0) := by
    convert hfirst.const_mul C using 1 <;> ring
  have hdiff : Tendsto (fun k =>
      sixVertexCanonicalOddCountingAverage hc s k (first k) - rho0 k)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_
      hmajor
    apply Eventually.of_forall
    intro k
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    let F := sixVertexBetheCountingFunction c N n p
    let rho := sixVertexFiniteRootDensity c N n p
    have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
    have hn : n <= N := by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega
    have hpSymm : SixVertexRootSymmetric p :=
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
        (2 * s + 1 + k)).2.1
    have hF : ∀ x, HasDerivAt F (rho x) x := fun x =>
      hasDerivAt_sixVertexBetheCountingFunction hc hN p x
    have hF0 : F 0 = 0 :=
      sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
    have hrho : LipschitzWith (sixVertexFiniteRootDensityLipschitzConstant c)
        rho := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
    have hfirstPos : 0 < first k := by
      dsimp [first, sixVertexCanonicalOddLeftHalfRoot]
      exact (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
        (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))).1
    have hbound := abs_primitive_div_id_sub_deriv_zero_le
      hF hF0 hrho hfirstPos
    rw [Real.norm_eq_abs, sub_zero]
    simpa [sixVertexCanonicalOddCountingAverage, first, rho0,
      F, rho, N, n, p, C] using hbound
  have hrho0 : Tendsto rho0 atTop
      (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
    simpa [rho0] using
      tendsto_sixVertexCanonicalOddHalfFilledFiniteDensity_zero hc s
  have hsum := hdiff.add hrho0
  simpa [first, rho0] using hsum

theorem sixVertexCanonicalOddRightLast_eq_boundaryZero
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalOddRightHalfRoot hc s k (Fin.last (s + k)) =
      sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
  unfold sixVertexCanonicalOddRightHalfRoot
    sixVertexCanonicalOddBoundaryHalfRoot
  congr 1

theorem sixVertexCanonicalOddCountingAverage_boundaryZero_eq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))) =
      (((s + k : Nat) : Real) + 3 / 2) /
          (sixVertexFourWidth (2 * s + 1) k : Real) /
        sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
  have hroot := sixVertexCanonicalOddRightHalfRoot_countingFunction hc s k
    (Fin.last (s + k))
  rw [sixVertexCanonicalOddRightLast_eq_boundaryZero hc s k] at hroot
  unfold sixVertexCanonicalOddCountingAverage
  rw [hroot]
  simp

theorem tendsto_sixVertexCanonicalOddBoundaryQuantumRatio
    (s : Nat) :
    Tendsto (fun k => (((s + k : Nat) : Real) + 3 / 2) /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds (1 / 4)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (s + 3 / 2 : Real) (8 * s + 8 : Real) (1 : Real)
      (show (4 : Real) ≠ 0 by norm_num)
  convert h using 1
  funext k
  unfold sixVertexFourWidth
  push_cast
  ring

theorem tendsto_sixVertexCanonicalOddCountingAverage_boundaryZero
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => sixVertexCanonicalOddCountingAverage hc s k
      (sixVertexCanonicalOddBoundaryHalfRoot hc s k
        (0 : Fin (s + 1)))) atTop (nhds (1 / (4 * Real.pi))) := by
  have hnum := tendsto_sixVertexCanonicalOddBoundaryQuantumRatio s
  have hden := tendsto_sixVertexCanonicalOddBoundaryHalfRoot hc s
    (0 : Fin (s + 1))
  have hquot := hnum.div hden Real.pi_ne_zero
  convert hquot using 1
  · funext k
    exact sixVertexCanonicalOddCountingAverage_boundaryZero_eq hc s k
  · field_simp [Real.pi_ne_zero]

theorem tendsto_log_sixVertexCanonicalOddCountingAverage_firstLeft
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => Real.log (sixVertexCanonicalOddCountingAverage hc s k
      (sixVertexCanonicalOddLeftHalfRoot hc s k
        (0 : Fin (s + k + 1))))) atTop
      (nhds (Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
  exact (Real.continuousAt_log
    (sixVertexFourierPhysicalDensity_pos hc 0).ne').tendsto.comp
      (tendsto_sixVertexCanonicalOddCountingAverage_firstLeft hc s)

theorem tendsto_log_sixVertexCanonicalOddCountingAverage_boundaryZero
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => Real.log (sixVertexCanonicalOddCountingAverage hc s k
      (sixVertexCanonicalOddBoundaryHalfRoot hc s k
        (0 : Fin (s + 1))))) atTop
      (nhds (Real.log (1 / (4 * Real.pi)))) := by
  have hpos : 0 < (1 / (4 * Real.pi) : Real) := by positivity
  exact (Real.continuousAt_log hpos.ne').tendsto.comp
    (tendsto_sixVertexCanonicalOddCountingAverage_boundaryZero hc s)

theorem tendsto_log_sixVertexCanonicalOddCountingAverage_endpointDifference
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddBoundaryHalfRoot hc s k
          (0 : Fin (s + 1)))) -
      Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddLeftHalfRoot hc s k
          (0 : Fin (s + k + 1))))) atTop
      (nhds (Real.log (1 / (4 * Real.pi)) -
        Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
  exact (tendsto_log_sixVertexCanonicalOddCountingAverage_boundaryZero hc s).sub
    (tendsto_log_sixVertexCanonicalOddCountingAverage_firstLeft hc s)

theorem tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      2 * ∑ j : Fin (s + k + 1),
        (Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)))) atTop
      (nhds (Real.log (1 / (4 * Real.pi)) -
        Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
  have hend :=
    tendsto_log_sixVertexCanonicalOddCountingAverage_endpointDifference hc s
  have hrem : Tendsto (fun k =>
      ∑ j : Fin (s + k + 1),
        (2 * Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
          Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddRightHalfRoot hc s k j))))
      atTop (nhds 0) := by
    simpa [sixVertexCanonicalOddCountingAverage] using
      tendsto_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference
        hc s
  have hsum := hend.add hrem
  have hsum' : Tendsto (fun k =>
      (Real.log (sixVertexCanonicalOddCountingAverage hc s k
          (sixVertexCanonicalOddBoundaryHalfRoot hc s k
            (0 : Fin (s + 1)))) -
        Real.log (sixVertexCanonicalOddCountingAverage hc s k
          (sixVertexCanonicalOddLeftHalfRoot hc s k
            (0 : Fin (s + k + 1))))) +
      ∑ j : Fin (s + k + 1),
        (2 * Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
          Real.log (sixVertexCanonicalOddCountingAverage hc s k
            (sixVertexCanonicalOddRightHalfRoot hc s k j)))) atTop
      (nhds (Real.log (1 / (4 * Real.pi)) -
        Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards [] with k
  have htel :=
    two_sum_sixVertexCanonicalOddMidpoint_sub_eq_boundary_add_secondDifference
      (fun x => Real.log (sixVertexCanonicalOddCountingAverage hc s k x))
      hc s k
  exact htel.symm

end

end StatMech.FrontierD
