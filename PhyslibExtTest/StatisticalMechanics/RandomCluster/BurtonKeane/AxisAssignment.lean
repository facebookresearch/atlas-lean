/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment`

* `caa_hall_of_injective_singletons` for the identity axis choice on `Fin 3`;
* `caa_hall_of_full` with full candidate sets in `d = 3`;
* `caa_axisAssignment` and `caa_disjointRouting` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Hall's condition for injective singleton candidates (explicit instance).
example : ∀ s : Finset (Fin 3),
    s.card ≤ (s.biUnion (fun i => ({id i} : Finset (Fin 3)))).card :=
  caa_hall_of_injective_singletons id Function.injective_id

-- Hall's condition for full candidate sets.
example : ∀ s : Finset (Fin 3),
    s.card ≤ (s.biUnion (fun _ => (Finset.univ : Finset (Fin 3)))).card :=
  caa_hall_of_full le_rfl _ fun _ => rfl

-- Candidates give an injective axis assignment.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Fin 3 → Site d)
    (S : Fin 3 → Finset (Fin d)) (h : caa_RunsAlongCandidates ω x S) :
    ∃ f : Fin 3 → Fin d, Function.Injective f ∧
      ∀ i : Fin 3, crr_ClusterRunsAlongAxis ω (x i) (f i) :=
  caa_axisAssignment ω x S h

-- The box candidates give disjoint routing.
example {d n : ℕ} (h : caa_BoxRunsAlongCandidates d n) : hrHD_DisjointRouting d n :=
  caa_disjointRouting h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AxisAssignment
