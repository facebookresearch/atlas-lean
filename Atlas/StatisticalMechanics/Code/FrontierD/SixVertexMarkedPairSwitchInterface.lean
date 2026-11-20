/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedTorusBridge











open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropPairSwitch (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev SixVertexMarkedSectorConfiguration
    (T : EvenTorus) (n : Fin (T.width + 1)) :=
  {omega : SixVertexArrows T //
    omega.IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val}


noncomputable def sixVertexMarkedSectorConfigurationPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) : Real[X] :=
  ∑ omega : SixVertexMarkedSectorConfiguration T n,
    sixVertexTorusMarkedWeight omega.1

theorem sixVertexMarkedSectorConfigurationPolynomial_eq_trace
    (T : EvenTorus) (n : Fin (T.width + 1)) :
    sixVertexMarkedSectorConfigurationPolynomial T n =
      sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
  rw [← sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace T n]
  unfold sixVertexMarkedSectorConfigurationPolynomial
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun omega : SixVertexArrows T =>
      omega.IceRule /\
        sixVertexUpCount
          (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val)
    (by simp) (fun omega => sixVertexTorusMarkedWeight omega)]
  rw [Finset.sum_filter]
  unfold sixVertexTorusMarkedSectorPartitionPolynomial
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hice : omega.IceRule
  · by_cases hsector : sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val <;>
      simp [hice, hsector]
  · rw [sixVertexTorusMarkedWeight_eq_zero_of_not_ice omega hice]
    simp [hice]



noncomputable def sixVertexMarkedPairMultiplicity
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) : Real :=
  (sixVertexTorusMarkedWeight omega *
    sixVertexTorusMarkedWeight eta).coeff k


noncomputable def sixVertexMarkedSectorPairMass
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) : Real :=
  ∑ pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right,
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k

theorem sixVertexMarkedSectorPairMass_eq_coeff
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorPairMass T left right k =
      (sixVertexShiftedSectorTracePolynomial T.width T.height left.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height right.val).coeff k := by
  rw [← sixVertexMarkedSectorConfigurationPolynomial_eq_trace T left,
    ← sixVertexMarkedSectorConfigurationPolynomial_eq_trace T right]
  unfold sixVertexMarkedSectorPairMass sixVertexMarkedPairMultiplicity
  unfold sixVertexMarkedSectorConfigurationPolynomial
  have hpoly :
      (∑ omega : SixVertexMarkedSectorConfiguration T left,
          sixVertexTorusMarkedWeight omega.1) *
        (∑ eta : SixVertexMarkedSectorConfiguration T right,
          sixVertexTorusMarkedWeight eta.1) =
      ∑ pair : SixVertexMarkedSectorConfiguration T left ×
          SixVertexMarkedSectorConfiguration T right,
        sixVertexTorusMarkedWeight pair.1.1 *
          sixVertexTorusMarkedWeight pair.2.1 := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
  rw [hpoly]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]

theorem sixVertexMarkedPairMultiplicity_nonneg
    {T : EvenTorus}
    (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule) (k : Nat) :
    0 <= sixVertexMarkedPairMultiplicity omega eta k := by
  unfold sixVertexMarkedPairMultiplicity
  apply Polynomial.coeffNonnegative_mul
  · rw [sixVertexTorusMarkedWeight_eq_pow omega homega]
    exact Polynomial.coeffNonnegative_pow
      Polynomial.coeffNonnegative_two_add_X _
  · rw [sixVertexTorusMarkedWeight_eq_pow eta heta]
    exact Polynomial.coeffNonnegative_pow
      Polynomial.coeffNonnegative_two_add_X _



structure SixVertexGlobalMarkedPairSwitch
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat) where
  toPair :
    SixVertexMarkedSectorConfiguration T lower ×
        SixVertexMarkedSectorConfiguration T upper ->
      SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle
  injective : Function.Injective toPair
  mask :
    SixVertexMarkedSectorConfiguration T lower ×
        SixVertexMarkedSectorConfiguration T upper -> SixVertexArrows T
  first_eq : forall pair,
    (toPair pair).1.1 =
      sixVertexTorusSwitchFirst (mask pair) pair.1.1 pair.2.1
  second_eq : forall pair,
    (toPair pair).2.1 =
      sixVertexTorusSwitchSecond (mask pair) pair.1.1 pair.2.1
  local_route_size : forall pair v,
    sixVertexLocalSwitchMaskCount
        (sixVertexTorusLocalSwitchMask (mask pair) v) = 0 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask (mask pair) v) = 2 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask (mask pair) v) = 4
  multiplicity_le : forall pair,
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k <=
      sixVertexMarkedPairMultiplicity
        (toPair pair).1.1 (toPair pair).2.1 k

theorem sixVertexMarkedSectorPairMass_le_of_switch
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (S : SixVertexGlobalMarkedPairSwitch T lower middle upper k) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  let domain := SixVertexMarkedSectorConfiguration T lower ×
    SixVertexMarkedSectorConfiguration T upper
  let codomain := SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle
  let w : domain -> Real := fun pair =>
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  let v : codomain -> Real := fun pair =>
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  change (∑ pair : domain, w pair) <= ∑ pair : codomain, v pair
  calc
    (∑ pair : domain, w pair) <= ∑ pair : domain, v (S.toPair pair) :=
      Finset.sum_le_sum fun pair hpair => S.multiplicity_le pair
    _ = ∑ pair ∈ Finset.univ.image S.toPair, v pair := by
      rw [Finset.sum_image]
      exact S.injective.injOn
    _ <= ∑ pair ∈ (Finset.univ : Finset codomain), v pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun pair hpair => Finset.mem_univ _
      · intro pair hpair hall
        exact sixVertexMarkedPairMultiplicity_nonneg
          pair.1.1 pair.2.1 pair.1.2.1 pair.2.2.1 k
    _ = ∑ pair : codomain, v pair := by simp



theorem coeff_shiftedSectorTrace_mul_le_sq_of_globalMarkedPairSwitch
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (S : SixVertexGlobalMarkedPairSwitch T lower middle upper k) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
  rw [pow_two]
  rw [← sixVertexMarkedSectorPairMass_eq_coeff,
    ← sixVertexMarkedSectorPairMass_eq_coeff]
  exact sixVertexMarkedSectorPairMass_le_of_switch S

end

end StatMech.FrontierD
