/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.BulkDeviationProof





open Finset Set SimpleGraph

namespace StatMech.FK

noncomputable section

variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]
variable [DecidableEq Vin] [DecidableEq Vout]
variable {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]
variable {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
variable {iota : Vin → Vout}



theorem bdp_free_outer_dominated_inner_decreasing
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
