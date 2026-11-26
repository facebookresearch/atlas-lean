/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldTargetReassembly

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldTargetReassembly`

* `mtrPhi` vanishes when no edge is counted (`D = ∅`), so the hypothesis of
  `mtr_meanfield_reassembly` holds with `m = 0` on the two-vertex complete graph;
* `mtr_meanfield_reassembly` on that instance;
* `mtr_crossing_compl_eq_sum_surfaces` on the same graph with all edges closed.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.MeanfieldTargetReassembly

open _root_.StatMech _root_.StatMech.Sharpness

/-- With no counted edges, the restricted `φ(S)` is zero. -/
theorem mtrPhi_empty (S : Finset (Fin 2)) :
    mtrPhi (⊤ : SimpleGraph (Fin 2)) (fun _ => 0) ∅ 0 S = 0 := by
  simp [mtrPhi]

-- The reassembled inequality with `D = ∅` and `m = 0`.
example : (0 : ℝ) * (1 - probV (fun _ => 0) (mpiCrossingEvent (⊤ : SimpleGraph (Fin 2)) 0 {1})) ≤
    1 * ∑ e ∈ (∅ : Finset (Sym2 (Fin 2))),
      (fun _ => (0 : ℝ)) e * probV (fun _ => 0)
        (abgiClosedPivotal e (mpiCrossingEvent (⊤ : SimpleGraph (Fin 2)) 0 {1})) :=
  mtr_meanfield_reassembly ⊤ (fun _ => 0) (fun _ => 0) (fun _ => ⟨le_rfl, zero_le_one⟩) ∅ 1 0
    zero_le_one (by simp) (by simp) 0 {1} (fun S _ _ => (mtrPhi_empty S).ge)

-- The complement of the crossing event is partitioned by surfaces.
example : 1 - probV (fun _ => 0) (mpiCrossingEvent (⊤ : SimpleGraph (Fin 2)) 0 {1}) =
    ∑ S with 0 ∈ S, probV (fun _ => 0) (mpiSurfaceEvent (⊤ : SimpleGraph (Fin 2)) {1} S) :=
  mtr_crossing_compl_eq_sum_surfaces ⊤ _ 0 {1}

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.MeanfieldTargetReassembly
