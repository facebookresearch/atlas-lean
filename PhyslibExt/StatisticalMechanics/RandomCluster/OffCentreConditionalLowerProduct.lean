/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxDomainMarkov

/-!
# Lower product bound for an off-centre box and an outside event

The free random-cluster mass of an increasing event in an embedded box, times the mass of an event
that depends only on edges outside the box, is at most the mass of their intersection.

## i. Overview

Embed a box graph `Gin` into a larger graph `Gout` by an injective vertex map that matches
adjacency. For `q ≥ 1`, conditioning the boundary-clique measure on `Gout` on the edges outside the
image of `Gin` gives, on the inner edges, a measure that dominates the free measure on `Gin`.
Summing this domination against an outside event yields a lower product bound. Both results are
proved unconditionally, under `0 < p < 1`, `1 ≤ q`, injectivity and adjacency matching of the
embedding.

## ii. Key results

- `ocd_freeMass_mul_outsideMass_le_inter` : free inner mass times boundary-clique outside mass
  is at most the boundary-clique mass of the intersection.
- `ocd_freeMass_mul_freeOutsideMass_le_inter` : the same bound with the free measure on `Gout`.

## iii. Table of contents

- A. Lower product bounds

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 4.2.
-/

@[expose] public section

open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

variable {Vin Vout : Type*}
  [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]

/-! ## A. Lower product bounds -/

/-- For `q ≥ 1`, the free mass of an increasing inner event times the boundary-clique mass of an
event depending only on outside edges is at most the boundary-clique mass of their intersection. -/
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

/-- For `q ≥ 1`, the free mass of an increasing inner event times the free mass on the larger
graph of an event depending only on outside edges is at most the free mass of their intersection. -/
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
