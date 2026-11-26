/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance

/-!
# Free random-cluster measures on nested graphs: decreasing events

The free random-cluster measure on a larger graph gives a decreasing event of an embedded smaller
graph at most the probability the free measure on the smaller graph gives it.

## i. Overview

For `q ≥ 1` the free random-cluster measure is stochastically increasing in the volume: if `Gin`
embeds into `Gout` with matching adjacency, then the outer measure, restricted to the inner edges,
dominates the inner measure on increasing events. Applying this to the complement of a decreasing
event `A` and using that both measures have total mass one gives the reverse inequality for `A`.
The headline `fkProb_free_nested_decreasing_le` is proved unconditionally (it takes only
injectivity of the embedding, adjacency matching, and `0 < p < 1`, `1 ≤ q`).

## ii. Key results

- `fkProb_free_nested_decreasing_le` : for a decreasing event `A` of the inner graph,
  `φ^free_Gout(ω|_Gin ∈ A) ≤ φ^free_Gin(A)`.

## iii. Table of contents

- A. Domination of decreasing events

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech.FK

noncomputable section

variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]
variable [DecidableEq Vin] [DecidableEq Vout]
variable {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]
variable {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
variable {iota : Vin → Vout}

/-! ## A. Domination of decreasing events -/

/-- For `q ≥ 1`, the free random-cluster measure on an outer graph gives the pull-back of a
decreasing event of an embedded inner graph at most the inner free measure of that event. -/
theorem fkProb_free_nested_decreasing_le
    (hiota : Function.Injective iota)
    (hadjm : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsDecreasing A) :
    (∑ rho,
        (ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho * fkProb Gout p q rho) ≤
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        fkProb Gin p q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcomp := bdp_free_inner_dominated_fkProb
    hiota hadjm hp hp1 hq hA.compl
  have hinSplit :
      (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
          fkProb Gin p q omega) +
        (∑ omega, Aᶜ.indicator (fun _ => (1 : Real)) omega *
          fkProb Gin p q omega) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ omega, (A.indicator (fun _ => (1 : Real)) omega *
              fkProb Gin p q omega +
            Aᶜ.indicator (fun _ => (1 : Real)) omega *
              fkProb Gin p q omega)) =
          ∑ omega, fkProb Gin p q omega := by
        apply Finset.sum_congr rfl
        intro omega _
        by_cases hmem : omega ∈ A <;> simp [hmem]
      _ = 1 := fkProb_sum_eq_one Gin hp hp1 hq0
  have houtSplit :
      (∑ rho,
          (ocd_innerRestrict iota ⁻¹' A).indicator
              (fun _ => (1 : Real)) rho * fkProb Gout p q rho) +
        (∑ rho,
          (ocd_innerRestrict iota ⁻¹' Aᶜ).indicator
              (fun _ => (1 : Real)) rho * fkProb Gout p q rho) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ rho, ((ocd_innerRestrict iota ⁻¹' A).indicator
                (fun _ => (1 : Real)) rho * fkProb Gout p q rho +
            (ocd_innerRestrict iota ⁻¹' Aᶜ).indicator
                (fun _ => (1 : Real)) rho * fkProb Gout p q rho)) =
          ∑ rho, fkProb Gout p q rho := by
        apply Finset.sum_congr rfl
        intro rho _
        by_cases hmem : ocd_innerRestrict iota rho ∈ A <;>
          simp [hmem]
      _ = 1 := fkProb_sum_eq_one Gout hp hp1 hq0
  linarith

end

end StatMech.FK
