/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proper 3-coloring for homothets of a planar convex set
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Geometry.ConvexHomothetThreeColoringWanted

/-- Points of the real Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A homothet of `D` with displacement `a` and ratio `r`: the image of `D`
under `x ↦ a + r • x`. Rotations are not allowed. -/
def homothet (D : Set Point) (a : Point) (r : ℝ) : Set Point :=
  (fun x ↦ a + r • x) '' D

/-- Keszegh–Pálvölgyi conjecture for homothets of an arbitrary planar convex
set: for every convex set `D` in the plane — with no boundedness, compactness,
openness, nonempty-interior, or general-position hypotheses — there is a
threshold `m`, depending only on `D`,
such that every finite point set admits a (not necessarily surjective)
3-coloring with no monochromatic homothet copy of `D` containing at least `m`
of its points. The intersection is finite as a subset of `S`, so `ncard`
counts its points. The source proves the polygon case and leaves the arbitrary-convex-set case,
including disks, open; see the entry metadata for its later resolution. -/
def conjecture : Prop :=
  ∀ D : Set Point, Convex ℝ D →
    ∃ m : ℕ, 0 < m ∧
      ∀ S : Finset Point, ∃ color : S → Fin 3, ∀ a r, 0 < r →
        m ≤ ((S : Set Point) ∩ homothet D a r).ncard →
          ∃ x : S, ∃ y : S,
            (x : Point) ∈ homothet D a r ∧ (y : Point) ∈ homothet D a r ∧
              color x ≠ color y

/--
Resolved false: Damasdi and Palvolgyi (Combinatorica 42 (2022), arXiv:2011.12187) proved that
for every m there is a finite planar point set such that every 3-coloring leaves a disk
containing exactly m points, all of one color; taking D a disk refutes the statement. The
polygon case (Keszegh-Palvolgyi) remains true. Source: G. Damasdi, D. Palvolgyi, Realizing an
m-uniform four-chromatic hypergraph with disks, Combinatorica 42 (2022) 1027-1048,
arXiv:2011.12187, https://arxiv.org/abs/2011.12187. Moved from
`OpenConjectures/Geometry/ConvexHomothetThreeColoring`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Geometry.ConvexHomothetThreeColoringWanted
