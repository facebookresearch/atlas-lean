/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialKacWardFormanTerm









namespace StatMech.FrontierA

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCRSFAmbientAtomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (cycle : finiteCRSFAtomicCycle next) : Complex :=
  ∏ v ∈ cycle.1.support, transport v (next v)



theorem finiteCRSFAmbientAtomicCycleHolonomy_toAtomicCycle
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    finiteCRSFAmbientAtomicCycleHolonomy transport (S.toAtomicCycle cycle) =
      S.atomicCycleHolonomy transport cycle := by
  change (S.toAtomicCycle cycle).holonomy transport =
    S.atomicCycleHolonomy transport cycle
  exact S.holonomy_toAtomicCycle transport cycle



theorem finiteCRSF_prod_localAtomic_eq_prod_ambientAtomic
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ cycle ∈ S.atomicCycles,
        -S.atomicCycleHolonomy transport cycle) =
      ∏ cycle ∈ S.toAtomicCycles,
        -finiteCRSFAmbientAtomicCycleHolonomy transport cycle := by
  rw [Finset.prod_neg, Finset.prod_neg, S.card_toAtomicCycles]
  congr 1
  change (∏ cycle ∈ S.atomicCycles,
      S.atomicCycleHolonomy transport cycle) =
    ∏ cycle ∈ S.toAtomicCycles, cycle.holonomy transport
  exact (S.prod_holonomy_toAtomicCycles transport).symm



theorem sum_finiteCRSFCycleSupport_eq_prod_one_sub_holonomy
    (transport : V -> V -> Complex) (next : V -> V) :
    (∑ S : finiteCRSFCycleSupport next,
        ∏ cycle ∈ S.atomicCycles,
          -S.atomicCycleHolonomy transport cycle) =
      ∏ cycle : finiteCRSFAtomicCycle next,
        (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
  calc
    (∑ S : finiteCRSFCycleSupport next,
        ∏ cycle ∈ S.atomicCycles,
          -S.atomicCycleHolonomy transport cycle) =
      ∑ selected : Finset (finiteCRSFAtomicCycle next),
        ∏ cycle ∈ selected,
          -finiteCRSFAmbientAtomicCycleHolonomy transport cycle := by
        exact Fintype.sum_equiv
          (finiteCRSFCycleSupport.equivAtomicCycles next)
          (fun S : finiteCRSFCycleSupport next =>
            ∏ cycle ∈ S.atomicCycles,
              -S.atomicCycleHolonomy transport cycle)
          (fun selected : Finset (finiteCRSFAtomicCycle next) =>
            ∏ cycle ∈ selected,
              -finiteCRSFAmbientAtomicCycleHolonomy transport cycle)
          (fun S => finiteCRSF_prod_localAtomic_eq_prod_ambientAtomic
            transport S)
    _ = ∑ selected : Finset (finiteCRSFAtomicCycle next),
        (-1 : Complex) ^ selected.card *
          ∏ cycle ∈ selected,
            finiteCRSFAmbientAtomicCycleHolonomy transport cycle := by
      apply Finset.sum_congr rfl
      intro selected _
      exact Finset.prod_neg _
    _ = _ := sum_cycleSelections_eq_prod_one_sub
      (finiteCRSFAmbientAtomicCycleHolonomy transport)



theorem det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∏ cycle : finiteCRSFAtomicCycle next,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
  rw [det_finiteTwistedLaplacian_eq_sum_atomicCycleCoefficients]
  apply Finset.sum_congr rfl
  intro next _
  congr 1
  rw [show (∑ S : finiteCRSFCycleSupport next,
      ∏ cycle ∈ S.atomicCycles,
        finiteCRSFAtomicCycleCoefficient transport S cycle) =
      ∑ S : finiteCRSFCycleSupport next,
        ∏ cycle ∈ S.atomicCycles,
          -S.atomicCycleHolonomy transport cycle by
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.prod_congr rfl
    intro cycle hcycle
    unfold finiteCRSFAtomicCycleCoefficient finiteCRSFAtomicCycleHolonomy
    rfl]
  exact sum_finiteCRSFCycleSupport_eq_prod_one_sub_holonomy transport next

end StatMech.FrontierA
