/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.OffCentreDomination
import Code.FK.FKDisjointBoxDomainMarkov



open SimpleGraph

namespace StatMech.FK

variable {Vin Vout : Type*}
  [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]




theorem ocd_freeMass_mul_outsideMass_le_inter
    (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (bdryOut : Vout → Prop) [DecidablePred bdryOut]
    (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 Vout))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
          fkProb Gin p q omega) *
        (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          bcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q rho) ≤
      ∑ rho,
        ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator
            (fun _ => (1 : Real)) rho *
          bcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q rho := by
  apply bcProb_disjoint_product_lower_of_conditional Gout
    (StatMech.Lattice.boundaryCliqueGraph bdryOut)
    hp hp1 (lt_of_lt_of_le zero_lt_one hq) hB
  intro psi hpsi
  exact ocd_free_le_condBcProb_innerRestrict
    (Gin := Gin) (Gout := Gout) (ιV := ιV) (bdryOut := bdryOut)
    hι hadjm hp hp1 hq psi hA


theorem ocd_freeMass_mul_freeOutsideMass_le_inter
    (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout)
    (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 Vout))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
          fkProb Gin p q omega) *
        (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          fkProb Gout p q rho) ≤
      ∑ rho,
        ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator
            (fun _ => (1 : Real)) rho *
          fkProb Gout p q rho := by
  have hbot : StatMech.Lattice.boundaryCliqueGraph
      (fun _ : Vout => False) = (⊥ : SimpleGraph Vout) := by
    ext x y
    rw [StatMech.Lattice.boundaryCliqueGraph_adj]
    simp
  simpa only [hbot, bcProb_bot_eq_fkProb] using
    ocd_freeMass_mul_outsideMass_le_inter Gin Gout ιV
      (fun _ : Vout => False) hι hadjm hp hp1 hq hA hB

end StatMech.FK
