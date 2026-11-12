/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeTransform

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

section Elitzur

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

omit [DecidableEq P] in

theorem gaugePartition_pos (incidence : P -> Finset E) (K : P -> ℝ) :
    0 < gaugePartition incidence K := by
  unfold gaugePartition gaugeWeight
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


noncomputable def gaugeWilsonExpectation (incidence : P -> Finset E)
    (K : P -> ℝ) (L : Finset E) : ℝ :=
  gaugeWilsonNumerator incidence K L / gaugePartition incidence K



def IsLocallyGaugeCharged (star : Q -> Finset E) (L : Finset E) : Prop :=
  ∃ v, Odd (L ∩ star v).card

omit [DecidableEq P] in



theorem gaugeWilsonNumerator_eq_zero_of_locallyCharged
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (L : Finset E) (hcharged : IsLocallyGaugeCharged star L) :
    gaugeWilsonNumerator incidence K L = 0 := by
  obtain ⟨v, hv⟩ := hcharged
  let f : GaugeConfig E -> ℝ := fun omega =>
    wilsonSpin L omega * gaugeWeight incidence K omega
  have hreindex :
      (∑ omega : GaugeConfig E, f omega) =
        ∑ omega : GaugeConfig E, f (localGaugeEquiv star v omega) := by
    exact (Equiv.sum_comp (localGaugeEquiv star v) f).symm
  have hneg : ∀ omega : GaugeConfig E,
      f (localGaugeEquiv star v omega) = -f omega := by
    intro omega
    change wilsonSpin L (localGaugeTransform star v omega) *
        gaugeWeight incidence K (localGaugeTransform star v omega) =
      -(wilsonSpin L omega * gaugeWeight incidence K omega)
    rw [wilsonSpin_localGaugeTransform,
      gaugeWeight_localGaugeTransform_eq incidence star hcomplex]
    rw [hv.neg_one_pow]
    ring
  unfold gaugeWilsonNumerator
  change (∑ omega : GaugeConfig E, f omega) = 0
  have hself : (∑ omega : GaugeConfig E, f omega) =
      -(∑ omega : GaugeConfig E, f omega) := by
    calc
      (∑ omega : GaugeConfig E, f omega) =
          ∑ omega : GaugeConfig E, f (localGaugeEquiv star v omega) := hreindex
      _ = ∑ omega : GaugeConfig E, -f omega := by
        apply Finset.sum_congr rfl
        intro omega _
        exact hneg omega
      _ = -(∑ omega : GaugeConfig E, f omega) := by
        rw [Finset.sum_neg_distrib]
  linarith

omit [DecidableEq P] in


theorem gaugeWilsonExpectation_eq_zero_of_locallyCharged
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (L : Finset E) (hcharged : IsLocallyGaugeCharged star L) :
    gaugeWilsonExpectation incidence K L = 0 := by
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_eq_zero_of_locallyCharged
    incidence star hcomplex K L hcharged]
  simp

end Elitzur

end StatMech.FrontierA
