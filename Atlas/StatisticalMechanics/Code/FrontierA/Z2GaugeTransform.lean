/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeHighTemp

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


def localGaugeTransform (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) : GaugeConfig E :=
  fun e => if e ∈ star v then !(omega e) else omega e

omit [Fintype E] [Fintype P] [DecidableEq P] in
@[simp] theorem localGaugeTransform_apply (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) (e : E) :
    localGaugeTransform star v omega e =
      if e ∈ star v then !(omega e) else omega e := rfl

omit [Fintype E] [Fintype P] [DecidableEq P] in

@[simp] theorem localGaugeTransform_involutive (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) :
    localGaugeTransform star v (localGaugeTransform star v omega) = omega := by
  funext e
  by_cases he : e ∈ star v <;> simp [localGaugeTransform, he]

omit [Fintype E] [Fintype P] [DecidableEq P] in

def localGaugeEquiv (star : Q -> Finset E) (v : Q) :
    GaugeConfig E ≃ GaugeConfig E where
  toFun := localGaugeTransform star v
  invFun := localGaugeTransform star v
  left_inv := localGaugeTransform_involutive star v
  right_inv := localGaugeTransform_involutive star v

omit [Fintype E] [Fintype P] [DecidableEq P] in

theorem gaugeEdgeSpin_localGaugeTransform (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) (e : E) :
    gaugeEdgeSpin (localGaugeTransform star v omega) e =
      (if e ∈ star v then (-1 : ℝ) else 1) * gaugeEdgeSpin omega e := by
  by_cases he : e ∈ star v <;>
    cases hspin : omega e <;>
      simp [localGaugeTransform, gaugeEdgeSpin, he, hspin]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem prod_star_sign (star : Q -> Finset E) (v : Q) (A : Finset E) :
    (∏ e ∈ A, if e ∈ star v then (-1 : ℝ) else 1) =
      (-1 : ℝ) ^ (A ∩ star v).card := by
  calc
    (∏ e ∈ A, if e ∈ star v then (-1 : ℝ) else 1) =
        ∏ e ∈ A.filter (fun e => e ∈ star v), (-1 : ℝ) := by
      rw [Finset.prod_filter]
    _ = (-1 : ℝ) ^ (A.filter fun e => e ∈ star v).card := by
      rw [Finset.prod_const]
    _ = (-1 : ℝ) ^ (A ∩ star v).card := by
      rw [Finset.filter_mem_eq_inter]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem plaquetteSpin_localGaugeTransform (incidence : P -> Finset E)
    (star : Q -> Finset E) (v : Q) (omega : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (localGaugeTransform star v omega) p =
      (-1 : ℝ) ^ (incidence p ∩ star v).card *
        plaquetteSpin incidence omega p := by
  unfold plaquetteSpin
  simp_rw [gaugeEdgeSpin_localGaugeTransform star v omega]
  rw [Finset.prod_mul_distrib, prod_star_sign]



def HasEvenPlaquetteStarIncidence (incidence : P -> Finset E)
    (star : Q -> Finset E) : Prop :=
  ∀ v p, Even (incidence p ∩ star v).card

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem plaquetteSpin_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (v : Q) (omega : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (localGaugeTransform star v omega) p =
      plaquetteSpin incidence omega p := by
  rw [plaquetteSpin_localGaugeTransform]
  rw [(hcomplex v p).neg_one_pow]
  simp

omit [Fintype E] [DecidableEq P] in

theorem gaugeAction_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (v : Q) (omega : GaugeConfig E) :
    gaugeAction incidence K (localGaugeTransform star v omega) =
      gaugeAction incidence K omega := by
  unfold gaugeAction
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquetteSpin_localGaugeTransform_eq incidence star hcomplex]

omit [Fintype E] [DecidableEq P] in

theorem gaugeWeight_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (v : Q) (omega : GaugeConfig E) :
    gaugeWeight incidence K (localGaugeTransform star v omega) =
      gaugeWeight incidence K omega := by
  unfold gaugeWeight
  rw [gaugeAction_localGaugeTransform_eq incidence star hcomplex]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem wilsonSpin_localGaugeTransform (star : Q -> Finset E) (v : Q)
    (L : Finset E) (omega : GaugeConfig E) :
    wilsonSpin L (localGaugeTransform star v omega) =
      (-1 : ℝ) ^ (L ∩ star v).card * wilsonSpin L omega := by
  unfold wilsonSpin
  simp_rw [gaugeEdgeSpin_localGaugeTransform star v omega]
  rw [Finset.prod_mul_distrib, prod_star_sign]



def IsGaugeClosed (star : Q -> Finset E) (L : Finset E) : Prop :=
  ∀ v, Even (L ∩ star v).card

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem wilsonSpin_localGaugeTransform_eq (star : Q -> Finset E)
    (L : Finset E) (hclosed : IsGaugeClosed star L)
    (v : Q) (omega : GaugeConfig E) :
    wilsonSpin L (localGaugeTransform star v omega) = wilsonSpin L omega := by
  rw [wilsonSpin_localGaugeTransform]
  rw [(hclosed v).neg_one_pow]
  simp

end LocalGauge

end StatMech.FrontierA
