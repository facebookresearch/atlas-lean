/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSpinConformalReduction










open Filter Topology
open scoped BigOperators

namespace StatMech.FrontierA


noncomputable def spinMeshRenormalization
    (iota : Type*) [Fintype iota] (delta : Real) : Real :=
  delta ^ (-(Fintype.card iota : Real) * isingSpinScalingDimension)

theorem spinMeshRenormalization_eq_card_div_eight
    (iota : Type*) [Fintype iota] (delta : Real) :
    spinMeshRenormalization iota delta =
      delta ^ (-(Fintype.card iota : Real) / 8) := by
  unfold spinMeshRenormalization isingSpinScalingDimension
  congr 1
  ring


noncomputable def spinRenormalizedCorrelation
    (iota : Type*) [Fintype iota]
    (delta correlation : Nat → Real) (n : Nat) : Real :=
  spinMeshRenormalization iota (delta n) * correlation n

theorem spinRenormalizedCorrelation_eq_delta_pow
    (iota : Type*) [Fintype iota]
    (delta correlation : Nat → Real) (n : Nat) :
    spinRenormalizedCorrelation iota delta correlation n =
      delta n ^ (-(Fintype.card iota : Real) / 8) * correlation n := by
  rw [spinRenormalizedCorrelation, spinMeshRenormalization_eq_card_div_eight]





theorem tendsto_spinRenormalizedCorrelation_of_asymptotic_conformal_transport
    {iota : Type*} [Fintype iota]
    (delta : Nat → Real) (localFactor : Nat → iota → Real)
    (Phi : Complex → Complex) (a : iota → Complex)
    (sourceRaw targetRaw : Nat → Real) (limit : Real)
    (hlocal : ∀ i,
      Tendsto (fun n ↦ localFactor n i) atTop
        (nhds (norm (deriv Phi (a i)) ^ isingSpinScalingDimension)))
    (hsource : Tendsto
      (spinRenormalizedCorrelation iota delta sourceRaw)
      atTop (nhds limit))
    (htransport : Tendsto (fun n ↦
      spinRenormalizedCorrelation iota delta targetRaw n -
        (∏ i, localFactor n i) *
          spinRenormalizedCorrelation iota delta sourceRaw n)
      atTop (nhds 0)) :
    Tendsto (spinRenormalizedCorrelation iota delta targetRaw) atTop
      (nhds (spinConformalFactor Phi a * limit)) := by
  exact tendsto_spinCorrelation_of_asymptotic_conformal_transport
    localFactor Phi a
    (spinRenormalizedCorrelation iota delta sourceRaw)
    (spinRenormalizedCorrelation iota delta targetRaw)
    limit hlocal hsource htransport

end StatMech.FrontierA
