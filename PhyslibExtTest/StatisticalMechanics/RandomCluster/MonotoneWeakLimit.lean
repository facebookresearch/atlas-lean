/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit`

The wired FK–Ising limit (`q = 2`) on `ℤ²` at `p = 1/2`, for the increasing cylinder event
"the box edge `e` of `Λ_1` is open":
* the cylinder event is clopen and measurable (`isClopen_boxRestrict_preimage`,
  `measurableSet_boxRestrict_preimage`);
* `fk_wired_infinite_measure`: the wired box measures of the event converge, along the whole
  sequence, to its probability under `wiredInfiniteVolume`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.MonotoneWeakLimit

open MeasureTheory Filter Topology _root_.StatMech _root_.StatMech.FK

/-- The event "the coordinate `e` is open". -/
def edgeOpen {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

/-- "The coordinate `e` is open" is an increasing event. -/
theorem isIncreasing_edgeOpen {E : Type*} (e : E) : IsIncreasing (edgeOpen e) := by
  intro x y hxy hx
  have h := hxy e
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- The cylinder event of a box edge is clopen.
example (e : Sym2 (boxVerts 2 1)) : IsClopen (boxRestrict 2 1 ⁻¹' edgeOpen e) :=
  isClopen_boxRestrict_preimage 1 _

-- The cylinder event of a box edge is measurable.
example (e : Sym2 (boxVerts 2 1)) : MeasurableSet (boxRestrict 2 1 ⁻¹' edgeOpen e) :=
  measurableSet_boxRestrict_preimage 1 _

-- Full-sequence convergence of the wired box measures on an increasing cylinder event.
example (e : Sym2 (boxVerts 2 1)) :
    Tendsto (fun m => (wiredFiniteMeasure 2 m (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
        (by norm_num) : Measure (ConfigSpace (Sym2 (Lattice.Site 2)))).real
          (boxRestrict 2 1 ⁻¹' edgeOpen e)) atTop
      (𝓝 ((wiredInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
        (by norm_num) : Measure (ConfigSpace (Sym2 (Lattice.Site 2)))).real
          (boxRestrict 2 1 ⁻¹' edgeOpen e))) :=
  fk_wired_infinite_measure 1 (by norm_num) (by norm_num) (isIncreasing_edgeOpen e)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.MonotoneWeakLimit
