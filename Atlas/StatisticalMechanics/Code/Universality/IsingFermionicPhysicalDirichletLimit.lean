/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareDirichletConvergence
import Code.Universality.IsingFermionicPhysicalEnergy










open Filter Set Topology

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquareSampledImaginaryPart
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex) :
    ∀ n, (fkSquareBoxPlanar n).V → Real :=
  fun n x ↦ (Phi (embedding n x)).im





theorem fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_barrier
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (harmonic barrier : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (boundaryError residual barrierBound : Nat → Real)
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |harmonic n x - fkIsingSquareSampledImaginaryPart
        embedding Phi n x| ≤ boundaryError n)
    (hresidual_nonneg : ∀ n, 0 ≤ residual n)
    (hbarrier_nonneg : ∀ n x, 0 ≤ barrier n x)
    (hbarrier_bound : ∀ n x, barrier n x ≤ barrierBound n)
    (hbarrier_laplacian : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (barrier n) x ≤ -1)
    (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
    (herror : Tendsto
      (fun n ↦ boundaryError n + residual n * barrierBound n)
      atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop,
      boundaryError n + residual n * barrierBound n < eta :=
    herror (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact lt_of_le_of_lt
    (isingFiniteGraph_harmonic_approximation_of_barrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (harmonic n) (fkIsingSquareSampledImaginaryPart embedding Phi n)
      (barrier n) (boundaryError n) (residual n) (barrierBound n)
      (fkIsingSquareBox_reachable_boundary n) (hharmonic n)
      (hboundary n) (hresidual_nonneg n) (hbarrier_nonneg n)
      (hbarrier_bound n) (hbarrier_laplacian n) (htarget_residual n) x)
    hn


noncomputable def fkIsingSquareBoxPoissonBarrierBound (n : Nat) : Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrierBound
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)




theorem fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_consistency
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (boundaryError residual : Nat → Real)
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |harmonic n x - fkIsingSquareSampledImaginaryPart
        embedding Phi n x| ≤ boundaryError n)
    (hresidual_nonneg : ∀ n, 0 ≤ residual n)
    (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
    (herror : Tendsto
      (fun n ↦ boundaryError n +
        residual n * fkIsingSquareBoxPoissonBarrierBound n)
      atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop,
      boundaryError n +
        residual n * fkIsingSquareBoxPoissonBarrierBound n < eta :=
    herror (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact lt_of_le_of_lt
    (isingFiniteGraph_harmonic_approximation_of_residual
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (harmonic n) (fkIsingSquareSampledImaginaryPart embedding Phi n)
      (boundaryError n) (residual n)
      (fkIsingSquareBox_reachable_boundary n) (hharmonic n)
      (hboundary n) (hresidual_nonneg n) (htarget_residual n) x)
    hn



theorem fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_quadratic_rate
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (boundaryError residual : Nat → Real)
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |harmonic n x - fkIsingSquareSampledImaginaryPart
        embedding Phi n x| ≤ boundaryError n)
    (hresidual_nonneg : ∀ n, 0 ≤ residual n)
    (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
    (herror : Tendsto
      (fun n ↦ boundaryError n + residual n * ((n : Real) ^ 2 / 2))
      atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop,
      boundaryError n + residual n * ((n : Real) ^ 2 / 2) < eta :=
    herror (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  have hbound := isingFiniteGraph_harmonic_approximation_of_barrier
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (harmonic n) (fkIsingSquareSampledImaginaryPart embedding Phi n)
    (fkIsingSquareBoxQuadraticBarrier n)
    (boundaryError n) (residual n) ((n : Real) ^ 2 / 2)
    (fkIsingSquareBox_reachable_boundary n) (hharmonic n)
    (hboundary n) (hresidual_nonneg n)
    (fkIsingSquareBoxQuadraticBarrier_nonneg n)
    (fkIsingSquareBoxQuadraticBarrier_le n)
    (fun y hy ↦ by
      rw [fkIsingSquareBoxQuadraticBarrier_laplacian n y hy])
    (htarget_residual n) x
  exact lt_of_le_of_lt hbound hn




theorem fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (upper lower harmonic physical :
      ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x,
      lower n x ≤ physical n x ∧ physical n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0))
    (hdirichlet : ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |physical n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta := by
  intro eta heta
  have hhalf : 0 < eta / 2 := half_pos heta
  have hphysical : ∀ᶠ n in atTop, ∀ x,
      |physical n x - harmonic n x| < eta / 2 :=
    fkIsingSquare_dirichlet_sandwich_uniform_convergence
      upper lower harmonic physical eps hupper hlower hharmonic
      hupperBoundary hlowerBoundary hsandwich heps (eta / 2) hhalf
  filter_upwards [hphysical, hdirichlet (eta / 2) hhalf] with n hph hdir
  intro x
  calc
    |physical n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| ≤
        |physical n x - harmonic n x| +
          |harmonic n x -
            fkIsingSquareSampledImaginaryPart embedding Phi n x| := by
      exact abs_sub_le _ _ _
    _ < eta := by linarith [hph x, hdir x]

end

end StatMech.Universality
