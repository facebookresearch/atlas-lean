/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.ConformalSpinFactor
import Code.Ising.MagNonneg
import Code.Ising.GKS

open BoundedContinuousFunction Filter MeasureTheory Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice



noncomputable def spinProdBCF {d : Nat} (A : Finset (Site d)) :
    ConfigSpace (Site d) →ᵇ Real :=
  ∏ x ∈ A, spinBCF x

@[simp] theorem spinProdBCF_apply {d : Nat} (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) :
    spinProdBCF A omega = spinProd A omega := by
  simp [spinProdBCF, spinProd]




theorem WeakConvergesTo.tendsto_integral_spinProd
    {d : Nat} {laws : Nat -> ProbabilityMeasure (ConfigSpace (Site d))}
    {limit : ProbabilityMeasure (ConfigSpace (Site d))}
    (h : WeakConvergesTo laws limit) (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(laws n : Measure (ConfigSpace (Site d)))) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(limit : Measure (ConfigSpace (Site d))))) := by
  simpa only [spinProdBCF_apply] using h.tendsto_integral (spinProdBCF A)




theorem tendsto_prod_localSpinFactors
    {iota : Type*} [Fintype iota]
    (localFactor : Nat -> iota -> Real) (Phi : Complex -> Complex)
    (a : iota -> Complex)
    (hlocal : forall i,
      Tendsto (fun n => localFactor n i) atTop
        (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension))) :
    Tendsto (fun n => ∏ i, localFactor n i) atTop
      (nhds (spinConformalFactor Phi a)) := by
  classical
  unfold spinConformalFactor spinDerivativeFactor
  exact tendsto_finsetProd Finset.univ (fun i _ => hlocal i)



theorem tendsto_spinCorrelation_mul_localFactors
    {iota : Type*} [Fintype iota]
    (localFactor : Nat -> iota -> Real) (Phi : Complex -> Complex)
    (a : iota -> Complex) (correlation : Nat -> Real) (limit : Real)
    (hlocal : forall i,
      Tendsto (fun n => localFactor n i) atTop
        (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
    (hcorrelation : Tendsto correlation atTop (nhds limit)) :
    Tendsto (fun n => (∏ i, localFactor n i) * correlation n) atTop
      (nhds (spinConformalFactor Phi a * limit)) :=
  (tendsto_prod_localSpinFactors localFactor Phi a hlocal).mul hcorrelation






theorem tendsto_spinCorrelation_of_asymptotic_conformal_transport
    {iota : Type*} [Fintype iota]
    (localFactor : Nat -> iota -> Real) (Phi : Complex -> Complex)
    (a : iota -> Complex) (source target : Nat -> Real) (limit : Real)
    (hlocal : forall i,
      Tendsto (fun n => localFactor n i) atTop
        (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
    (hsource : Tendsto source atTop (nhds limit))
    (htransport : Tendsto
      (fun n => target n - (∏ i, localFactor n i) * source n)
      atTop (nhds 0)) :
    Tendsto target atTop (nhds (spinConformalFactor Phi a * limit)) := by
  have hmain := tendsto_spinCorrelation_mul_localFactors
    localFactor Phi a source limit hlocal hsource
  have hsum := htransport.add hmain
  simpa only [sub_add_cancel, zero_add] using hsum

end StatMech.FrontierA
