/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.DlrInfiniteSandwich

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.DlrInfiniteSandwich`

* `dlr_infinite_sandwich` in conditional form for an FK-DLR measure on `ℤ²` at `p = 1/2`,
  `q = 1`, applied to the increasing box events `univ` and "the edge `e` is open";
* `dlr_box_mixture_sandwich` in the same setting for the sure event.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.DlrInfiniteSandwich

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

-- The infinite sandwich for the sure box event.
example (φ : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))))
    (hφ : IsFKDLR 2 (1 / 2) 1 φ) :
    (freeInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) zero_lt_one :
          Measure _).real (boxRestrict 2 3 ⁻¹' Set.univ) ≤
        (φ : Measure _).real (boxRestrict 2 3 ⁻¹' Set.univ) ∧
      (φ : Measure _).real (boxRestrict 2 3 ⁻¹' Set.univ) ≤
        (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) zero_lt_one :
          Measure _).real (boxRestrict 2 3 ⁻¹' Set.univ) :=
  dlr_infinite_sandwich (by norm_num) (by norm_num) le_rfl hφ isUpperSet_univ

/-- "The box edge `e` is open" is an increasing box event. -/
theorem edgeOpen_isIncreasing {n : ℕ} (e : Sym2 (boxVerts 2 n)) :
    IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts 2 n)) | ω e = true} := by
  intro x y hxy hx
  have h := hxy e
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- The infinite sandwich for a single-edge event.
example (φ : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))))
    (hφ : IsFKDLR 2 (1 / 2) 1 φ) (e : Sym2 (boxVerts 2 3)) :=
  dlr_infinite_sandwich (p := 1 / 2) (by norm_num) (by norm_num) le_rfl hφ
    (edgeOpen_isIncreasing e)

-- The finite-volume mixture sandwich for the sure event.
example (φ : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))))
    (hφ : IsFKDLR 2 (1 / 2) 1 φ) :=
  dlr_box_mixture_sandwich (n := 2) (p := 1 / 2) (by norm_num) (by norm_num) le_rfl hφ
    isUpperSet_univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.DlrInfiniteSandwich
