/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination

/-!
# Free domination of an embedded box by the free measure on a larger graph

For `q ≥ 1`, the free random-cluster probability of an increasing event in a box is at most the free
probability, on a larger graph containing the box, of the pulled-back event.

## i. Overview

Embed a box graph `Gin` into `Gout` by an injective, adjacency-matching vertex map. Conditioning the
free measure on `Gout` on the outside edges gives, on the inner edges, a random-cluster measure with
boundary condition at least free, which dominates the free measure on `Gin` for increasing events.
Averaging over the outside configuration gives the comparison of free measures. The result is
proved unconditionally, under `0 < p < 1`, `1 ≤ q`, injectivity and adjacency matching.

## ii. Key results

- `ocd_condFreeProb_innerRestrict_ge` : conditionally on any outside configuration, the free mass of
  an increasing inner event is at most that of its pull-back on the larger graph.

The unconditional comparison is `bdp_free_inner_dominated_fkProb` (`FreeTranslationInvariance`).

## iii. Table of contents

- A. The empty boundary condition
- B. Domination of the free measure

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Lemma 4.14.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

noncomputable section

/-! ## A. The empty boundary condition -/

lemma bcProb_congr_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (h : C = D) (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p q omega = bcProb G D p q omega := by
  subst D
  congr 1

variable {Vin Vout : Type*}
variable [Fintype Vin] [DecidableEq Vin]
variable [Fintype Vout] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (iota : Vin -> Vout)

/-- The empty boundary predicate: no vertex is a boundary vertex. See also `bdp_noBdry`
(FreeTranslationInvariance), the same definition, kept separate to avoid importing the free-energy
modules here. -/
def falseBoundary (_ : Vout) : Prop := False

/-- The empty boundary predicate is decidable. -/
instance : DecidablePred (falseBoundary : Vout -> Prop) :=
  fun _ => isFalse id

/-! ## B. Domination of the free measure -/

/-- For `q ≥ 1` and any outside configuration `ψ`, the free measure on the larger graph conditioned
on `ψ` gives an increasing inner event at least its free probability on the box. See also
`bdp_condBcProb_innerRestrict_ge` (FreeTranslationInvariance), the boundary-condition form. -/
theorem ocd_condFreeProb_innerRestrict_ge
    (hiota : Function.Injective iota)
    (hadj : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (psi : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
          condBcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph
              (falseBoundary : Vout -> Prop))
            p q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) >=
      ∑ omega,
        A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox
    (bdryOut := (falseBoundary : Vout -> Prop))
    hiota hadj hp hp1 hq0 psi (ocd_innerRestrict iota ⁻¹' A)]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  have hmono := bcProb_free_le Gin
    (ocd_inducedWiring Gout iota
      (falseBoundary : Vout -> Prop) psi)
    hp hp1 hq hA
  simpa only [bcProb_bot_eq_fkProb] using hmono

end

end StatMech.FK
