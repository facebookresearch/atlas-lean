/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy
import Code.FrontierA.IsingSurfaceTensionPrismGinibre
import Code.FrontierA.IsingSurfaceTensionBoundaryBridge
import Code.Ising.GinibreBoundaryDerivativeLower

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice

noncomputable section


theorem hasDerivAt_standardCubicInterfaceDensity (beta : Real) (n : Nat) :
    HasDerivAt (fun b => standardCubicInterfaceDensity b n)
      ((fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) /
        ((2 * n + 1 : Nat) : Real) ^ 2) beta := by
  unfold standardCubicInterfaceDensity
  exact (hasDerivAt_finiteInterfaceFreeEnergy
    (⟨2, by omega⟩ : Fin 3) n beta).div_const
      (((2 * n + 1 : Nat) : Real) ^ 2)



theorem standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit
    (M : Real -> Real) (beta : Real) (n : Nat)
    (henergy :
      2 * (M beta) ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <=
        fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) :
    2 * (M beta) ^ 2 <=
      deriv (fun b => standardCubicInterfaceDensity b n) beta := by
  rw [(hasDerivAt_standardCubicInterfaceDensity beta n).deriv]
  have harea : (0 : Real) < (((2 * n + 1 : Nat) : Real) ^ 2) := by
    positivity
  rw [le_div_iff₀ harea]
  simpa [mul_assoc] using henergy



theorem standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    2 * magnetization 3 beta ^ 2 <=
      deriv (fun b => standardCubicInterfaceDensity b n) beta := by
  exact standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit
    (magnetization 3) beta n
    (finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq beta hbeta n hn)



theorem standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit
    (M : Real -> Real)
    (hMnonneg : forall beta, 0 < beta -> 0 <= M beta)
    (hMmono : MonotoneOn M (Ioi 0))
    (n : Nat)
    (henergy : forall beta, 0 < beta ->
      2 * (M beta) ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <=
        fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) :
    HasWeakSurfaceTensionLowerBound 1 M
      (fun beta => standardCubicInterfaceDensity beta n) := by
  have hdiff : Differentiable Real
      (fun beta => standardCubicInterfaceDensity beta n) := by
    intro beta
    exact (hasDerivAt_standardCubicInterfaceDensity beta n).differentiableAt
  apply weakSurfaceTensionLowerBound_of_deriv 1 M
    (fun beta => standardCubicInterfaceDensity beta n)
    (by norm_num) hMnonneg hMmono hdiff.continuous.continuousOn
      hdiff.differentiableOn
  intro beta hbeta
  simpa using
    (standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit
      M beta n (henergy beta hbeta))




theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_finite_energy_deficit
    {betaC : Real}
    (hregime : HasOrderedMagnetizationRegime (magnetization 3) betaC)
    (hMnonneg : forall beta, 0 < beta -> 0 <= magnetization 3 beta)
    (hMmono : MonotoneOn (magnetization 3) (Ioi 0))
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta)
    (hupper : forall n beta, 0 < beta ->
      standardCubicInterfaceDensity beta n <=
        2 * beta * (magnetization 3 beta) ^ 2)
    (henergy : forall n beta, 0 < beta ->
      2 * (magnetization 3 beta) ^ 2 *
          (((2 * n + 1 : Nat) : Real) ^ 2) <=
        fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
          fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
            (bondFinsetTouch 3 n) beta 0) :
    forall beta, 0 < beta ->
      (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
  apply rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds
    hregime hprism (fun beta _ => hasStandardPrismSurfaceComparison beta)
    hupper
  intro n
  exact standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit
    (magnetization 3) hMnonneg hMmono n (henergy n)

end

end StatMech.FrontierA
