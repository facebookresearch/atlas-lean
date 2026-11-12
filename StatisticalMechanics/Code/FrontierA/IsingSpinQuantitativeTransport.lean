/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.IsingSpinMovingMesh

open Filter Topology

namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising




structure SpinConformalTransportEstimate
    {ι : Type*} [Fintype ι]
    (Φ : Complex → Complex) (a : ι → Complex)
    (source target : Nat → Real) where
  discreteDerivative : Nat → ι → Complex
  error : Nat → Real
  error_tendsto : Tendsto error atTop (nhds 0)
  derivative_error_le : ∀ n i,
    dist (discreteDerivative n i) (deriv Φ (a i)) ≤ error n
  correlation_error_le : ∀ n,
    |target n - spinDerivativeFactor (discreteDerivative n) * source n| ≤ error n

namespace SpinConformalTransportEstimate

variable {ι : Type*} [Fintype ι]
  {Φ : Complex → Complex} {a : ι → Complex}
  {source target : Nat → Real}



theorem tendsto_discreteDerivative
    (transport : SpinConformalTransportEstimate Φ a source target) (i : ι) :
    Tendsto (fun n ↦ transport.discreteDerivative n i) atTop
      (nhds (deriv Φ (a i))) := by
  apply (tendsto_iff_dist_tendsto_zero).2
  apply squeeze_zero (g := transport.error)
  · exact fun n ↦ dist_nonneg
  · exact fun n ↦ transport.derivative_error_le n i
  · exact transport.error_tendsto



theorem tendsto_spinDerivativeFactor
    (transport : SpinConformalTransportEstimate Φ a source target) :
    Tendsto (fun n ↦ spinDerivativeFactor (transport.discreteDerivative n))
      atTop (nhds (spinConformalFactor Φ a)) := by
  classical
  unfold spinDerivativeFactor spinConformalFactor
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (transport.tendsto_discreteDerivative i).norm.rpow_const
    (Or.inr (by norm_num [isingSpinScalingDimension]))


theorem correlation_residual_tendsto
    (transport : SpinConformalTransportEstimate Φ a source target) :
    Tendsto (fun n ↦
      target n - spinDerivativeFactor (transport.discreteDerivative n) * source n)
      atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero (fun n ↦
    target n - spinDerivativeFactor (transport.discreteDerivative n) * source n)).2
  apply squeeze_zero (g := transport.error)
  · exact fun n ↦ abs_nonneg _
  · exact transport.correlation_error_le
  · exact transport.error_tendsto




theorem target_tendsto
    (transport : SpinConformalTransportEstimate Φ a source target)
    {limit : Real} (hsource : Tendsto source atTop (nhds limit)) :
    Tendsto target atTop (nhds (spinConformalFactor Φ a * limit)) := by
  have hmain : Tendsto (fun n ↦
      spinDerivativeFactor (transport.discreteDerivative n) * source n)
      atTop (nhds (spinConformalFactor Φ a * limit)) :=
    transport.tendsto_spinDerivativeFactor.mul hsource
  have hsum := transport.correlation_residual_tendsto.add hmain
  simpa only [sub_add_cancel, zero_add] using hsum




theorem target_tendsto_comp
    {Ψ : Complex → Complex} {middle final : Nat → Real}
    (first : SpinConformalTransportEstimate Φ a source middle)
    (second : SpinConformalTransportEstimate Ψ (Φ ∘ a) middle final)
    {limit : Real} (hsource : Tendsto source atTop (nhds limit))
    (hΦ : ∀ i, DifferentiableAt Complex Φ (a i))
    (hΨ : ∀ i, DifferentiableAt Complex Ψ (Φ (a i))) :
    Tendsto final atTop
      (nhds (spinConformalFactor (Ψ ∘ Φ) a * limit)) := by
  have hmiddle := first.target_tendsto hsource
  have hfinal := second.target_tendsto hmiddle
  rw [spinConformalFactor_comp Ψ Φ a hΦ hΨ]
  simpa only [mul_assoc] using hfinal

end SpinConformalTransportEstimate




theorem tendsto_squareBoxRenormalizedSpinCorrelation_of_quantitative_transport
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real)
    (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (Φ : Complex → Complex) (a : ι → Complex) (limit : Real)
    (transport : SpinConformalTransportEstimate Φ a
      (squareBoxRenormalizedSpinCorrelation
        ι δ β h sourceRadius sourceMarked)
      (squareBoxRenormalizedSpinCorrelation
        ι δ β h targetRadius targetMarked))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι δ β h sourceRadius sourceMarked)
      atTop (nhds limit)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι δ β h targetRadius targetMarked)
      atTop (nhds (spinConformalFactor Φ a * limit)) :=
  transport.target_tendsto hsource

end StatMech.FrontierA
