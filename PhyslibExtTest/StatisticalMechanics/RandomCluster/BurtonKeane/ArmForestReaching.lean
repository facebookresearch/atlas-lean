/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching`

* `sfa_walk_avoid_connected` with the empty arm graph and the trivial walk at a site `a ≠ x`;
* `sfa_spanForestArms_of_armForestReaching` and `sfa_Tcount_le_boundary_of_armForestReaching`
  in conditional form;
* `sfa_armForestReaching_of_boundary_edge` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- A site different from `x` stays connected to itself after removing `x` (trivial walk).
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) (h : x ≠ a) :
    Connected d (removeSite x ω) a a :=
  sfa_walk_avoid_connected ω ⊥ (fun _ _ h => h.elim) .nil (by simpa using h)

-- Arm forest reaching gives the span forest arms.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : sfa_ArmForestReaching ω n) :
    spc_SpanForestArms ω n :=
  sfa_spanForestArms_of_armForestReaching ω n h

-- Arm forest reaching gives the count bound.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : sfa_ArmForestReaching ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n h

-- An open boundary edge and no trifurcation give arm forest reaching.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {b₁ b₂ : Site d}
    (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n) (hbne : b₁ ≠ b₂)
    (hopen : (openSubgraph d ω).Adj b₁ b₂) (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    sfa_ArmForestReaching ω n :=
  sfa_armForestReaching_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching
