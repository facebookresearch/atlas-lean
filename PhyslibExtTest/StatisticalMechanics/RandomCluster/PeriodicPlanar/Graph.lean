/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Graph

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Graph`

* `triangularGraph` joins the origin to `(-1, 1)` (third step `(-1, 1)`);
* `hexagonalGraph` joins `(0, false)` to `((1, 1), true)` and not `(0, false)` to `(0, true)`;
* the origin lies in the orbit box of radius `0` of the square lattice;
* `wiredInfiniteVolume_isLimit` on the triangular lattice at `p = 1 / 2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Graph

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

-- The origin and `(-1, 1)` are triangular neighbors.
example : triangularGraph.Adj 0 ![-1, 1] :=
  ⟨2, Or.inl (by ext i; fin_cases i <;> rfl)⟩

-- `(0, false)` and `((1, 1), true)` are hexagonal neighbors.
example : hexagonalGraph.Adj (0, false) (![1, 1], true) :=
  Or.inl ⟨rfl, rfl, 2, by ext i; fin_cases i <;> rfl⟩

-- Two vertices over the same site are not hexagonal neighbors.
example : ¬ hexagonalGraph.Adj ((0 : Site 2), false) (0, true) := by
  rintro (⟨-, -, i, hi⟩ | ⟨h, -, -⟩)
  · have h0 := congrFun hi 0
    have h1 := congrFun hi 1
    fin_cases i <;> simp [hexagonalStep] at h0 h1
  · exact Bool.noConfusion h

-- The origin is in the radius-`0` orbit box of the square lattice.
example : (0 : Site 2) ∈ square.orbitBox 0 :=
  (square.mem_orbitBox_iff 0 0).2
    ⟨0, fun i => by simp, 0, Finset.mem_singleton_self _, by ext i; simp [square]⟩

-- The wired infinite-volume limit statement at `p = 1 / 2`, `q = 2` on the triangular lattice.
example : ∃ phi : ℕ → ℕ, StrictMono phi ∧
    WeakConvergesTo
      (fun n => triangular.wiredFiniteMeasure (phi n) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num) (by norm_num : (0 : ℝ) < 2))
      (triangular.wiredInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num) (by norm_num : (0 : ℝ) < 2)) :=
  triangular.wiredInfiniteVolume_isLimit _ _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Graph
