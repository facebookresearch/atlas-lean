/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.IsingSurfaceTensionLebowitzPfisterLower
import Code.IsingFK.HisingBoxClose
import Code.FK.ThetaZeroBelowPc

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.IsingFK StatMech.FK

noncomputable section


theorem pOfBeta_mono {a b : Real} (hab : a <= b) :
    pOfBeta a <= pOfBeta b := by
  unfold pOfBeta
  have hexp : Real.exp (-2 * b) <= Real.exp (-2 * a) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith




theorem magnetization_monotoneOn_Ioi (d : Nat) (hd : 1 <= d) :
    MonotoneOn (magnetization d) (Ioi 0) := by
  intro a ha b hb hab
  have hpa0 : 0 < pOfBeta a := pOfBeta_pos ha
  have hpa1 : pOfBeta a < 1 := pOfBeta_lt_one a
  have hpb0 : 0 < pOfBeta b := pOfBeta_pos hb
  have hpb1 : pOfBeta b < 1 := pOfBeta_lt_one b
  rw [(mfc_magPercoId d hd (hbx_hisingBox d)) a ha hpa0 hpa1,
    (mfc_magPercoId d hd (hbx_hisingBox d)) b hb hpb0 hpb1]
  exact tzp_fkTheta_monotone_in_p hpa0 hpa1 hpb0 hpb1
    (pOfBeta_mono hab)




theorem standardCubicInterfaceDensity_hasWeakLowerBound
    (n : Nat) (hn : 0 < n) :
    HasWeakSurfaceTensionLowerBound 1 (magnetization 3)
      (fun beta => standardCubicInterfaceDensity beta n) := by
  exact standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit
    (magnetization 3)
    (fun beta hbeta => IsingFK.magnetization_nonneg 3 hbeta.le)
    (magnetization_monotoneOn_Ioi 3 (by norm_num)) n
    (fun beta hbeta =>
      finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq
        beta hbeta.le n hn)






theorem rectangularIsingSurfaceTension_hasWeakLowerBound_of_prismComparison
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta) :
    HasWeakSurfaceTensionLowerBound 1 (magnetization 3)
      rectangularIsingSurfaceTension := by
  apply weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto
    1 (magnetization 3) rectangularIsingSurfaceTension
      (fun n beta => standardCubicInterfaceDensity beta (n + 1))
  · intro beta hbeta
    have hlim :=
      standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
        hbeta (hprism beta hbeta) (hasStandardPrismSurfaceComparison beta)
    exact hlim.comp (tendsto_add_atTop_nat 1)
  · intro n
    exact standardCubicInterfaceDensity_hasWeakLowerBound (n + 1) (by omega)

end

end StatMech.FrontierA
