/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreFreeDomination

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreFreeDomination`

For the identity embedding of the one-edge graph `⊤` on `Fin 2` into itself, `p = 1/2`, `q = 2`:
* `bcProb_congr_boundary` for equal wirings;
* `ocd_condFreeProb_innerRestrict_ge` for the increasing events `univ` and "the edge `s(0, 1)` is
  open", conditionally on the all-closed outside configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.OffCentreFreeDomination

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- Equal wirings give equal measures.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    bcProb G2 (⊥ ⊔ ⊥) (1 / 2) 2 ω = bcProb G2 ⊥ (1 / 2) 2 ω :=
  bcProb_congr_boundary G2 _ _ (sup_idem _) _ _ ω

/-- "The edge `s(0, 1)` is open" is increasing. -/
theorem edgeOpen_isIncreasing :
    IsIncreasing {ω : ConfigSpace (Sym2 (Fin 2)) | ω s(0, 1) = true} := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- Conditional free domination for the sure event.
example := ocd_condFreeProb_innerRestrict_ge G2 G2 id Function.injective_id (fun _ _ => Iff.rfl)
  (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two (fun _ => false) isUpperSet_univ

-- Conditional free domination for a single open edge.
example := ocd_condFreeProb_innerRestrict_ge G2 G2 id Function.injective_id (fun _ _ => Iff.rfl)
  (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two (fun _ => false)
  edgeOpen_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.OffCentreFreeDomination
