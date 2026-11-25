/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd distance graph has infinite chromatic number
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted

/-! Source record `OPG-616`. Validated from hill-photon submission. -/

namespace ODGIC

/-!
# Clause inventory for [OPG-616]

- Object: `O`, graph on `ℝ²` (as `EuclideanSpace ℝ (Fin 2)`).
- Hypothesis: adjacency iff distance is an odd integer (odd `ℕ`
  suffices since distances are nonnegative).
- Question: `χ(O) = ∞` as `chromaticNumber = ⊤`.
-/

/-- **Odd distance graph.** The odd distance graph is the simple graph on the Euclidean plane
$\mathbb{R}^2$ in which two points $x$ and $y$ are adjacent when their Euclidean distance is an
odd integer. -/
noncomputable def OddDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := ∃ k : ℕ, Odd k ∧ dist x y = (k : ℝ)
  symm := ⟨by
    intro x y h
    obtain ⟨k, hk, hkk⟩ := h
    exact ⟨k, hk, by rw [dist_comm]; exact hkk⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨k, hk, hkk⟩ := h
    rw [dist_self] at hkk
    have hk0 : k = 0 := by exact_mod_cast hkk.symm
    rw [hk0] at hk
    exact Nat.not_odd_zero hk⟩

/-- **Infinite chromatic number of the odd distance graph.** The proposition that the odd distance
graph on $\mathbb{R}^2$ has infinite chromatic number, that is, has no proper colouring with
finitely many colours. -/
def OddDistanceChromaticInfinite : Prop := OddDistanceGraph.chromaticNumber = ⊤

end ODGIC

/--
**Davies' odd distance theorem.** The odd distance graph on the Euclidean plane $\mathbb{R}^2$,
in which two points are adjacent when their distance is an odd integer, has infinite chromatic
number: it has no proper colouring with finitely many colours.

Davies proves (Theorem 1) that every finite colouring of the plane has a monochromatic pair of
points at odd integer distance.

Source: James Davies, Odd distances in colourings of
the plane, Geometric and Functional Analysis 34 (2024) 19-31, arXiv:2209.15598,
https://arxiv.org/abs/2209.15598. Moved from
`OpenConjectures/GraphTheory/OddDistanceGraphInfiniteChromatic`.
-/
public theorem_wanted OddDistanceChromaticInfinite_holds : ODGIC.OddDistanceChromaticInfinite

end MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted
