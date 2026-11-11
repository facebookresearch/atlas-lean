/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsInfinite

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsInfinite`

* `fvMagnetization` is the plus-boundary integral of the origin spin (unfolding);
* `magnetization_eq_limit` at `d = 2`, `β = 1`: a subsequence of finite-volume magnetizations
  converges to `m*(1)`, and the limit lies in `[-1, 1]`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.EsInfinite

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.IsingFK _root_.StatMech.Lattice
  _root_.StatMech.Percolation Filter Topology

-- `fvMagnetization` unfolds to the plus-boundary expectation of the origin spin.
example (n : ℕ) : fvMagnetization 2 1 n =
    ∫ ω, spin ω (origin 2)
      ∂(plusMeasure 2 n 1 0 : MeasureTheory.Measure (ConfigSpace (Site 2))) := rfl

-- A subsequence of the box magnetizations converges to `m*(1)`, which lies in `[-1, 1]`.
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => fvMagnetization 2 1 (φ n)) atTop (𝓝 (magnetization 2 1)) ∧
      magnetization 2 1 ∈ Set.Icc (-1) 1 := by
  obtain ⟨φ, hφ, hlim⟩ := magnetization_eq_limit 2 1
  exact ⟨φ, hφ, hlim, abs_le.mp (abs_magnetization_le_one 2 1)⟩

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.EsInfinite
