/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination

/-!
# The law of inner events under the conditioned off-centre measure

If the conditioned boundary-clique measure on a larger graph agrees pointwise on the embedded box
with a function `μ`, then every inner event has conditioned probability equal to its `μ`-mass.

## i. Overview

For a box graph embedded in a larger graph by an injective, adjacency-matching vertex map, the
measure obtained by conditioning on the outside edges is carried by the extensions of the outside
configuration. Pulling back inner events along the restriction map turns the conditioned
probability of an inner event into a sum over inner configurations. The result is proved
unconditionally, under `0 < p < 1`, `0 < q`, and the pointwise identification `hmu` it is about.

## ii. Key results

- `ocd_condBcProb_innerEvent_eq_of_pointwise` : the conditioned probability of an inner event equals
  its `μ`-mass when the conditioned measure agrees pointwise with `μ`.

## iii. Table of contents

- A. Inner events under the conditioned measure

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 4.2.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

noncomputable section

/-! ## A. Inner events under the conditioned measure -/

/-- If the conditioned boundary-clique measure, read on extensions of the outside configuration,
equals `μ` pointwise, then every inner event has conditioned probability equal to its `μ`-mass. -/
theorem ocd_condBcProb_innerEvent_eq_of_pointwise
    {Vin Vout : Type*}
    [Fintype Vin] [DecidableEq Vin]
    [Fintype Vout] [DecidableEq Vout]
    {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {iota : Vin -> Vout} {bdryOut : Vout -> Prop}
    [DecidablePred bdryOut]
    (hiota : Function.Injective iota)
    (hadj : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout))
    (mu : ConfigSpace (Sym2 Vin) -> Real)
    (hmu : ∀ omega,
      condBcProb Gout
          (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset iota) psi (ocd_psiExt iota psi omega) =
        mu omega)
    (A : Set (ConfigSpace (Sym2 Vin))) :
    (∑ rho : ConfigSpace (Sym2 Vout),
        (ocd_innerRestrict iota ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          condBcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
            (ocd_innerEdgeFinset iota) psi rho) =
      ∑ omega : ConfigSpace (Sym2 Vin),
        A.indicator (fun _ => (1 : Real)) omega * mu omega := by
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox
    hiota hadj hp hp1 hq psi (ocd_innerRestrict iota ⁻¹' A)]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  have hdm := ocd_condBcProb_psiExt_eq_bcProb
    (Gin := Gin) (Gout := Gout) (ιV := iota) (bdryOut := bdryOut)
    hiota hadj hp hp1 hq psi omega
  exact hdm.symm.trans (hmu omega)

end

end StatMech.FK
