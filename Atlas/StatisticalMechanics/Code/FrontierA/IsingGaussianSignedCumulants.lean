/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianPhysicalPolarization
import Code.FrontierA.IsingGaussianHadamardCumulants










open Filter Topology

namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

namespace PhysicalIsing




theorem criticalFiniteBoxWeightedSignedScaledCumulant_tendsto_zero
    (d order : Nat) (hd : 4 < d) (horder : Not (order = 2))
    (positive negative signed : (n : Nat) -> sctBox d n -> Real)
    (hsigned : forall n, signed n = positive n - negative n)
    (hnonneg : forall (i : Fin (order + 1)) n x,
      0 <= positive n x + ((i : Nat) : Real) * negative n x)
    (hbounded : forall (i : Fin (order + 1)) n x,
      positive n x + ((i : Nat) : Real) * negative n x <= 1)
    (hF : forall (i : Fin (order + 1)) n,
      FiniteIsingWeightedHadamardFactorization
        (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d))
          (positive n + (((i : Nat) : Real) • negative n)))
    (variance : Fin (order + 1) -> Real)
    (hvariance : forall i : Fin (order + 1),
      Tendsto
        (fun n => criticalFiniteBoxWeightedScaledCumulant d n (by omega)
          (positive n + (((i : Nat) : Real) • negative n)) 2)
        atTop (nhds (variance i))) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedScaledCumulant d n (by omega)
        (signed n) order) atTop (nhds 0) := by
  apply criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line
    d order (by omega) positive negative signed hsigned
  intro i
  have hlimits := criticalFiniteBoxWeightedScaled_cumulantLimits d hd
    (fun n => positive n + (((i : Nat) : Real) • negative n))
    (fun n x => by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hnonneg i n x)
    (fun n x => by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hbounded i n x)
    (hF i) (variance i) (hvariance i) order
  simpa only [scalarGaussianCumulant, if_neg horder] using hlimits

end PhysicalIsing

end

end StatMech.FrontierA
