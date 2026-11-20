/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuousOffsetFourier
import Code.FrontierD.SixVertexBetheFourierEvaluation





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexOffsetLogBoundaryPartialSum
    (lam : Real) (N : Nat) : Real :=
  lam - ∑ n ∈ range N,
    (-1 : Real) ^ (n + 1) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)

def sixVertexOffsetLogDerivativePartialSum
    (lam : Real) (N : Nat) (alpha : Real) : Real :=
  ∑ n ∈ range N,
    (1 - Real.exp (-2 * (n + 1 : Real) * lam)) *
      Real.sin ((n + 1 : Real) * alpha)

theorem intervalIntegral_offsetProfile_mul_logDerivativePartialSum
    {lam : Real} (hlam : 0 < lam) (N : Nat) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexOffsetRapidityProfile lam alpha *
        sixVertexOffsetLogDerivativePartialSum lam N alpha) =
      -∑ n ∈ range N,
        (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
          (Real.exp (-2 * (n + 1 : Real) * lam) - 1) /
            (n + 1 : Real) := by
  have hmode (n : Nat) :
      (∫ alpha in -Real.pi..Real.pi,
        sixVertexOffsetRapidityProfile lam alpha *
          Real.sin ((n + 1 : Real) * alpha)) =
        (-1 : Real) ^ (n + 1) *
          Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real) := by
    have h := sixVertexOffsetRapidityProfile_sineCoefficient hlam
      (m := n + 1) (by omega)
    have hm : (n + 1 : Real) ≠ 0 := by positivity
    field_simp [Real.pi_ne_zero, hm] at h ⊢
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using h
  unfold sixVertexOffsetLogDerivativePartialSum
  rw [show (fun alpha => sixVertexOffsetRapidityProfile lam alpha *
      ∑ n ∈ range N,
        (1 - Real.exp (-2 * (n + 1 : Real) * lam)) *
          Real.sin ((n + 1 : Real) * alpha)) =
      fun alpha => ∑ n ∈ range N,
        (1 - Real.exp (-2 * (n + 1 : Real) * lam)) *
          (sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((n + 1 : Real) * alpha)) by
    funext alpha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, hmode]
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · intro n hn
    exact ((continuous_sixVertexOffsetRapidityProfile hlam).mul
      (by fun_prop : Continuous (fun alpha : Real =>
        Real.sin ((n + 1 : Real) * alpha)))).const_mul _ |>.intervalIntegrable _ _



theorem sixVertexOffsetLogBoundary_add_pairing_eq_fourierPartialSum
    {lam : Real} (hlam : 0 < lam) (N : Nat) :
    sixVertexOffsetLogBoundaryPartialSum lam N +
        (∫ alpha in -Real.pi..Real.pi,
          sixVertexOffsetRapidityProfile lam alpha *
            sixVertexOffsetLogDerivativePartialSum lam N alpha) =
      sixVertexOffsetFourierPartialSum lam N := by
  rw [intervalIntegral_offsetProfile_mul_logDerivativePartialSum hlam]
  unfold sixVertexOffsetLogBoundaryPartialSum
    sixVertexOffsetFourierPartialSum
  ring

theorem tendsto_sixVertexOffsetLogBoundary_add_pairing
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (fun N => sixVertexOffsetLogBoundaryPartialSum lam N +
      ∫ alpha in -Real.pi..Real.pi,
        sixVertexOffsetRapidityProfile lam alpha *
          sixVertexOffsetLogDerivativePartialSum lam N alpha)
      atTop (nhds (sixVertexAntiferroelectricGapRate lam)) := by
  apply (sixVertexOffsetFourierPartialSum_tendsto hlam).congr'
  filter_upwards [] with N
  exact (sixVertexOffsetLogBoundary_add_pairing_eq_fourierPartialSum hlam N).symm

end

end StatMech.FrontierD
