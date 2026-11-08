/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.SmallInductiveDimension

@[expose] public section

namespace MathlibExt.Topology.ScottishBook187bWanted

/-- Covering dimension `≤ n`: every finite open cover has a finite
open refinement in which any `n + 2` distinct members have empty
intersection (order `≤ n + 1`). -/
def CoverLE (n : ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (m : ℕ) (U : Fin m → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ∃ (k : ℕ) (V : Fin k → Set X),
      (∀ j, IsOpen (V j)) ∧ (⋃ j, V j) = Set.univ ∧
      (∀ j, ∃ i, V j ⊆ U i) ∧
      ∀ s : Finset (Fin k), s.card = n + 2 →
        (⋂ j ∈ s, V j) = ∅

/--
Scottish Book Problem 187, part (2), is false as stated: the inductive
and covering definitions of dimension are not equivalent for all compact
Hausdorff spaces. Small inductive dimension is Mathlib's
`HasSmallInductiveDimensionLE`; the typescript does not say small vs large
inductive dimension. Status: solved-negative for part (2) (whole Problem 187 is
partially_solved, part (1) remaining separate). Citation: the Lunts–Lokutsievskii example is a Hausdorff compactum (bicompactum) with dim X ≠ ind X; see Encyclopedia of Mathematics, 'Dimension theory' ('There are, however, Hausdorff compacta X for which dim X ≠ ind X (the Lunts–Lokutsievskii example)'), and R. Engelking, Dimension Theory, North-Holland, 1978. Hence for some n the inductive and covering ≤ n predicates differ, which is what the negation above asserts. (In Soviet terminology a 'bicompactum' is a compact Hausdorff space.) Dimension theory gives `dim X ≤ ind X ≤ Ind X` for compact Hausdorff `X` with either inequality possibly strict; strictness of `dim < ind` is Lunts–Lokutsievskii; strictness of `ind < Ind` is Filippov's example (same EoM article).
Source: P. Alexandroff, Problem 187 part (2) of the Scottish Book,
typescript pp. 82–83.
-/
theorem_wanted scottishBook187b_refuted :
    ¬ ∀ (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X],
      ∀ n : ℕ, HasSmallInductiveDimensionLE X n ↔ CoverLE n X

end MathlibExt.Topology.ScottishBook187bWanted
