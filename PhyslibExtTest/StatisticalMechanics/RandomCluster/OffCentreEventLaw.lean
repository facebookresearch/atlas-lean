/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreEventLaw

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreEventLaw`

* `ocd_condBcProb_innerEvent_eq_of_pointwise` for the identity embedding of the one-edge graph
  `⊤` on `Fin 2` into itself, boundary `{1}`, `p = 1/2`, `q = 2`, with `μ` the conditioned measure
  read through `ocd_psiExt` (so the pointwise hypothesis holds by `rfl`), for the event "the edge
  `s(0, 1)` is open" and the all-closed outside configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.OffCentreEventLaw

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The conditioned measure read on the inner configurations. -/
noncomputable def μ (ω : ConfigSpace (Sym2 (Fin 2))) : ℝ :=
  condBcProb G2 (Lattice.boundaryCliqueGraph (· = (1 : Fin 2))) (1 / 2) 2
    (ocd_innerEdgeFinset (Vin := Fin 2) id) (fun _ => false) (ocd_psiExt id (fun _ => false) ω)

-- Inner events have conditioned probability equal to their `μ`-mass.
example := ocd_condBcProb_innerEvent_eq_of_pointwise (Gin := G2) (Gout := G2)
  (bdryOut := (· = (1 : Fin 2))) Function.injective_id (fun _ _ => Iff.rfl) (p := 1 / 2)
  (q := 2) (by norm_num) (by norm_num) two_pos (fun _ => false) μ (fun _ => rfl)
  {ω | ω s(0, 1) = true}

-- The same for the sure event.
example := ocd_condBcProb_innerEvent_eq_of_pointwise (Gin := G2) (Gout := G2)
  (bdryOut := (· = (1 : Fin 2))) Function.injective_id (fun _ _ => Iff.rfl) (p := 1 / 2)
  (q := 2) (by norm_num) (by norm_num) two_pos (fun _ => false) μ (fun _ => rfl) Set.univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.OffCentreEventLaw
