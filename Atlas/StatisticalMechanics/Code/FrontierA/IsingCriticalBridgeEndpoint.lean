/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalSurfaceBulk









open Filter Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice

noncomputable section



noncomputable def oddPrismCriticalLowerHalfBridgeMeanDensity
    (n : Nat) : Real := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  exact replicaBridgeMean (oddPrismLowerHalfGraph n)
      (fun _ => Ising.betaC 3)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
      (oddPrismLowerHalfBridgeSites n) 0 /
    (((2 * n + 1 : Nat) : Real) ^ 2)



theorem oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage
    (n : Nat) :
    oddPrismCriticalLowerHalfBridgeMeanDensity n =
      oddPrismCriticalLowerHalfSpinSquareAverage n := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  unfold oddPrismCriticalLowerHalfBridgeMeanDensity
    oddPrismCriticalLowerHalfSpinSquareAverage
  rw [replicaBridgeMean_zero]
  congr 1



theorem oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfBridgeMeanDensity atTop (nhds 0) := by
  apply oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero.congr'
  exact Filter.Eventually.of_forall fun n =>
    (oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage n).symm



noncomputable def oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity
    (n : Nat) : Real := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  exact deriv (replicaBridgeFreeEnergy (oddPrismLowerHalfGraph n)
      (fun _ => Ising.betaC 3)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
      (oddPrismLowerHalfBridgeSites n)) 0 /
    (((2 * n + 1 : Nat) : Real) ^ 2)


theorem oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_eq
    (n : Nat) :
    oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity n =
      2 * oddPrismCriticalLowerHalfBridgeMeanDensity n := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  unfold oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity
  rw [replicaBridgeFreeEnergy_deriv_zero
    (oddPrismLowerHalfGraph n)
    (fun _ => Ising.betaC 3)
    (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
    (oddPrismLowerHalfBridgeSites n)]
  unfold oddPrismCriticalLowerHalfBridgeMeanDensity
  rw [replicaBridgeMean_zero]
  ring



theorem
    oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity atTop
      (nhds 0) := by
  have htwo : Tendsto (fun _ : Nat => (2 : Real)) atTop (nhds 2) :=
    tendsto_const_nhds
  have h := htwo.mul
    oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero
  simpa only [mul_zero] using h.congr'
    (Filter.Eventually.of_forall fun n =>
      (oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_eq n).symm)




theorem oddPrismCriticalLowerHalfBridge_eventually_le_of_variance_order
    (hvar : forall n,
      letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
      forall t, 0 <= t ->
        replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => Ising.betaC 3)
            (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) t <=
          replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => Ising.betaC 3)
            (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) (-t))
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun n =>
      oddPrismLowerHalfBridgeFreeEnergy (Ising.betaC 3) n /
          (((2 * n + 1 : Nat) : Real) ^ 2) <= eps) atTop := by
  have hupper : forall n,
      oddPrismLowerHalfBridgeFreeEnergy (Ising.betaC 3) n /
          (((2 * n + 1 : Nat) : Real) ^ 2) <=
        2 * Ising.betaC 3 *
          oddPrismCriticalLowerHalfSpinSquareAverage n := by
    intro n
    have h := oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order
      (Ising.betaC 3) isingBetaC_three_pos.le n (hvar n)
    have hden : (0 : Real) < (((2 * n + 1 : Nat) : Real) ^ 2) := by
      positivity
    rw [div_le_iff₀ hden]
    unfold oddPrismCriticalLowerHalfSpinSquareAverage
    convert h using 1 <;> field_simp
  have hzero : Tendsto (fun n =>
      2 * Ising.betaC 3 * oddPrismCriticalLowerHalfSpinSquareAverage n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero
  have hevent : Filter.Eventually (fun n =>
      2 * Ising.betaC 3 * oddPrismCriticalLowerHalfSpinSquareAverage n < eps)
      atTop := hzero.eventually (Iio_mem_nhds heps)
  filter_upwards [hevent] with n hn
  exact (hupper n).trans hn.le

end

end StatMech.FrontierA
