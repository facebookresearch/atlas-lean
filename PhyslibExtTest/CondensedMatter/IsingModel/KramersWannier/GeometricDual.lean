/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.GeometricDual

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.GeometricDual`

* `kwg_isingZ_high_temp` on the one-edge multigraph `Fin 2` with a single edge `s(0, 1)`, and on
  a single loop at one vertex;
* `kwg_geometricCutCycleDuality`, `kwg_geometricCutEvenMatching` and `kwg_unique_outerFace` for an
  arbitrary planar subgraph;
* `kwg_isingZ_duality` applied under its `tanh β* = e^{-2β}` hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.GeometricDual

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

-- High-temperature expansion for one edge between two vertices.
example (β : ℝ) : kwg_isingZ (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2))) β =
    2 ^ 2 * Real.cosh β ^ 1 * ∑ F : Finset (Fin 1),
      if kwg_IsEven (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2))) F then Real.tanh β ^ F.card
      else 0 := by
  simpa using kwg_isingZ_high_temp (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2))) β

-- High-temperature expansion for a single loop (a multigraph edge `s(0, 0)`).
example (β : ℝ) : kwg_isingZ (fun _ : Fin 1 => (s(0, 0) : Sym2 (Fin 1))) β =
    2 ^ 1 * Real.cosh β ^ 1 * ∑ F : Finset (Fin 1),
      if kwg_IsEven (fun _ : Fin 1 => (s(0, 0) : Sym2 (Fin 1))) F then Real.tanh β ^ F.card
      else 0 := by
  simpa using kwg_isingZ_high_temp (fun _ : Fin 1 => (s(0, 0) : Sym2 (Fin 1))) β

-- Cut–cycle duality and cut/even matching.
example (P : PlanarZ2Subgraph) :
    kwg_GeometricCutCycleDuality P ∧
      kwg_GeometricCutEvenMatching P (1 / 2) (2 ^ Nat.card P.G.ConnectedComponent) :=
  ⟨kwg_geometricCutCycleDuality P, kwg_geometricCutEvenMatching P _⟩

-- Every planar subgraph has a unique outer (infinite) face.
example (P : PlanarZ2Subgraph) := kwg_unique_outerFace P

-- Kramers–Wannier duality.
example (P : PlanarZ2Subgraph) (β βs : ℝ) (h : Real.tanh βs = Real.exp (-2 * β)) :
    kwg_isingZ (kwg_dualEnds P) βs =
      2 ^ Nat.card (kwg_Face P) * Real.cosh βs ^ Nat.card (kwg_Edge P) /
          (Real.exp (β * P.G.edgeSet.ncard) * 2 ^ Nat.card P.G.ConnectedComponent) *
        isingZ P.G β 0 :=
  kwg_isingZ_duality P β βs h

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.GeometricDual
