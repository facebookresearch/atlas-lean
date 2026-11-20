/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialKacWardLaplacian









namespace StatMech.FrontierA

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def finiteCRSFFixedPointEquivComplement {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    laplacianPermutationFixedPoint S.ambientPerm ≃
      {v : V // v ∉ S.carrier} where
  toFun v := ⟨v, by
    intro hv
    exact S.ambientPerm_ne_of_mem hv v.property⟩
  invFun v := ⟨v, S.ambientPerm_apply_of_not_mem v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


noncomputable def finiteCRSFOutgoingConductance
    (conductance : V -> V -> Complex) (next : V -> V) : Complex :=
  ∏ v : V, conductance v (next v)


noncomputable def finiteCRSFSupportTransport
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Complex :=
  Equiv.Perm.sign S.ambientPerm •
    ∏ v ∈ S.carrier, -transport v (next v)


noncomputable def finiteCRSFAtomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  ∏ v ∈ cycle.support, transport v (next v)


theorem finiteCRSF_atomicCycleSupports_biUnion {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.atomicCycles.biUnion (fun cycle => cycle.support) = Finset.univ := by
  rw [← S.restrictedPerm_support]
  ext v
  simp only [Finset.mem_biUnion, finiteCRSFCycleSupport.atomicCycles]
  exact (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).symm



theorem finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ S.carrier, transport v (next v)) =
      ∏ cycle ∈ S.atomicCycles,
        finiteCRSFAtomicCycleHolonomy transport S cycle := by
  rw [← Finset.prod_coe_sort S.carrier
    (fun v => transport v (next v))]
  change (∏ v ∈ (Finset.univ : Finset (↑S.carrier)),
      transport v (next v)) = _
  rw [← finiteCRSF_atomicCycleSupports_biUnion S]
  rw [Finset.prod_biUnion]
  · rfl
  · intro cycle hcycle cycle' hcycle' hne
    exact Equiv.Perm.disjoint_iff_disjoint_support.mp
      (S.restrictedPerm.cycleFactorsFinset_pairwise_disjoint
        hcycle hcycle' hne)


noncomputable def finiteCRSFAtomicCycleCoefficient
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  -finiteCRSFAtomicCycleHolonomy transport S cycle



theorem finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFSupportTransport transport S =
      ∏ cycle ∈ S.atomicCycles,
        finiteCRSFAtomicCycleCoefficient transport S cycle := by
  unfold finiteCRSFSupportTransport finiteCRSFAtomicCycleCoefficient
  rw [S.sign_ambientPerm_eq_atomicCycles]
  rw [Finset.prod_neg]
  rw [finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy]
  rw [Finset.prod_neg]
  simp only [Units.smul_def, zsmul_eq_mul]
  have hsignCast (n : Nat) :
      (((↑((-1 : ℤˣ) ^ n) : ℤ) : Complex)) = (-1 : Complex) ^ n := by
    change ((((-1 : ℤ) ^ n : ℤ) : Complex)) = (-1 : Complex) ^ n
    push_cast
    rfl
  rw [hsignCast]
  rw [pow_add]
  have hcancel :
      (-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.atomicCycles.card) *
        ((-1 : Complex) ^ S.carrier.card *
          ∏ cycle ∈ S.atomicCycles,
            finiteCRSFAtomicCycleHolonomy transport S cycle) =
      ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card) *
        ((-1 : Complex) ^ S.atomicCycles.card *
          ∏ cycle ∈ S.atomicCycles,
            finiteCRSFAtomicCycleHolonomy transport S cycle) := by ring
    _ = _ := by rw [hcancel, one_mul]



theorem finiteCRSF_nonfixed_product_reindex
    (conductance transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
        -conductance (S.ambientPerm v) v *
          transport (S.ambientPerm v) v) =
      ∏ v ∈ S.carrier,
        -conductance v (next v) * transport v (next v) := by
  rw [show (Finset.univ.filter fun v => S.ambientPerm v ≠ v) =
      S.carrier by
    simpa [Equiv.Perm.mem_support] using S.ambientPerm_support]
  rw [S.ambientPerm.prod_comp' S.carrier
    (fun v w => -conductance v w * transport v w)]
  · apply Finset.prod_congr rfl
    intro v hv
    rw [S.ambientPerm_symm_apply_of_mem hv]
  · intro v hv
    rw [← S.ambientPerm_support]
    exact Equiv.Perm.mem_support.mpr hv



theorem finiteCRSF_fixed_product_eq_complement
    (conductance : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v : laplacianPermutationFixedPoint S.ambientPerm,
        conductance v (next v)) =
      ∏ v : {v : V // v ∉ S.carrier}, conductance v (next v) := by
  exact Fintype.prod_equiv (finiteCRSFFixedPointEquivComplement S)
    (fun v : laplacianPermutationFixedPoint S.ambientPerm =>
      conductance v (next v))
    (fun v : {v : V // v ∉ S.carrier} => conductance v (next v))
    (fun _ => rfl)




theorem finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport
    (conductance transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessTerm conductance transport S.toFiber =
      finiteCRSFOutgoingConductance conductance next *
        finiteCRSFSupportTransport transport S := by
  unfold finiteCRSFWitnessTerm finiteCRSFOutgoingConductance
    finiteCRSFSupportTransport
  change Equiv.Perm.sign S.ambientPerm •
      ((∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) *
        ∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) = _
  rw [finiteCRSF_fixed_product_eq_complement conductance S]
  rw [finiteCRSF_nonfixed_product_reindex conductance transport S]
  rw [show (∏ v ∈ S.carrier,
      -conductance v (next v) * transport v (next v)) =
        ∏ v ∈ S.carrier,
          conductance v (next v) * (-transport v (next v)) by
    apply Finset.prod_congr rfl
    intro v _
    ring]
  rw [Finset.prod_mul_distrib]
  rw [← mul_assoc]
  rw [← Finset.prod_subtype S.carrierᶜ (by simp)
    (fun v => conductance v (next v))]
  rw [Finset.prod_compl_mul_prod]
  exact (mul_smul_comm (Equiv.Perm.sign S.ambientPerm)
    (∏ v : V, conductance v (next v))
    (∏ v ∈ S.carrier, -transport v (next v))).symm




theorem det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∑ S : finiteCRSFCycleSupport next,
            finiteCRSFSupportTransport transport S := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport]
  apply Finset.sum_congr rfl
  intro next _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFWitnessTerm_toFiber_eq_outgoing_mul_transport
    conductance transport S




theorem det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∑ S : finiteCRSFCycleSupport next,
            ∏ cycle ∈ S.atomicCycles,
              finiteCRSFAtomicCycleCoefficient transport S cycle := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_cycleTransport]
  apply Finset.sum_congr rfl
  intro next _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFSupportTransport_eq_prod_atomicCycleCoefficient transport S

end StatMech.FrontierA
