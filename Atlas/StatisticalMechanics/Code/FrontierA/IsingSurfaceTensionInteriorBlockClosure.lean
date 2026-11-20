/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeInteriorBlockTiling
import Code.FrontierA.IsingSurfaceTensionFiniteInfiniteGap










open Filter Topology

namespace StatMech.FrontierA

noncomputable section



theorem rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity
    (K : Real) (hK : 0 < K) (n : Nat) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) <=
      cubicalInfiniteVolumeSquareWilsonDensity K n := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨p, hp, _, hclose⟩ :=
    exists_cubicalPaddedDisorderDensity_close_infiniteVolume hK n heps
  have htile := rectangularIsingSurfaceTension_le_paddedDisorderDensity
    hK (centralSquareSide n) p (by simp [centralSquareSide]) hp
  have htile' : rectangularIsingSurfaceTension (gaugeDualCoupling K) <=
      cubicalPaddedDisorderFreeEnergy K
          (centralSquareSide n) (centralSquareSide n) p p p p p p /
        ((centralSquareSide n : Nat) : Real) ^ 2 := by
    simpa using htile
  linarith



theorem rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) = 0 := by
  have hinfinite :=
    cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
      K hK hlt
  have hupper : rectangularIsingSurfaceTension (gaugeDualCoupling K) <= 0 :=
    ge_of_tendsto hinfinite (Eventually.of_forall fun n =>
      rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity
        K hK n)
  exact le_antisymm hupper
    (rectangularIsingSurfaceTension_nonneg (gaugeDualCoupling_pos hK))



theorem cubicalFiniteInfiniteSquareDensityGap_tendsto_zero_of_dual_lt_betaC
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds 0) := by
  rw [← rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC K hK hlt]
  exact cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt


theorem rectangularIsingSurfaceTension_eq_zero_of_lt_betaC
    (beta : Real) (hbeta : 0 < beta)
    (hlt : beta < StatMech.Ising.betaC 3) :
    rectangularIsingSurfaceTension beta = 0 := by
  let K := gaugeCriticalCoupling beta
  have hK : 0 < K := gaugeCriticalCoupling_pos hbeta
  have hzero := rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC
    K hK (by simpa [K, gaugeDualCoupling_gaugeCriticalCoupling hbeta] using hlt)
  simpa [K, gaugeDualCoupling_gaugeCriticalCoupling hbeta] using hzero



theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_ne_betaC
    (beta : Real) (hbeta : 0 < beta)
    (hne : beta ≠ StatMech.Ising.betaC 3) :
    0 < rectangularIsingSurfaceTension beta <->
      StatMech.Ising.betaC 3 < beta := by
  constructor
  · intro hpos
    by_contra hnot
    have hle : beta <= StatMech.Ising.betaC 3 := not_lt.mp hnot
    have hlt : beta < StatMech.Ising.betaC 3 := lt_of_le_of_ne hle hne
    rw [rectangularIsingSurfaceTension_eq_zero_of_lt_betaC beta hbeta hlt]
      at hpos
    exact (lt_irrefl 0) hpos
  · exact rectangularIsingSurfaceTension_pos




theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero
    (hcritical : rectangularIsingSurfaceTension
      (StatMech.Ising.betaC 3) = 0)
    (beta : Real) (hbeta : 0 < beta) :
    0 < rectangularIsingSurfaceTension beta <->
      StatMech.Ising.betaC 3 < beta := by
  constructor
  · intro hpos
    by_contra hnot
    have hle : beta <= StatMech.Ising.betaC 3 := not_lt.mp hnot
    rcases hle.lt_or_eq with hlt | rfl
    · rw [rectangularIsingSurfaceTension_eq_zero_of_lt_betaC beta hbeta hlt]
        at hpos
      exact (lt_irrefl 0) hpos
    · rw [hcritical] at hpos
      exact (lt_irrefl 0) hpos
  · exact rectangularIsingSurfaceTension_pos

end

end StatMech.FrontierA
