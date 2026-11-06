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

/-- **Covering dimension at most n.** A topological space $X$ has covering dimension at most
$n \in \mathbb{N}$ if every finite open cover $U_1, \dots, U_m$ of $X$ has a finite open
refinement $V_1, \dots, V_k$ (open sets covering $X$, each contained in some $U_i$) in which any
$n + 2$ members with distinct indices have empty intersection, that is, the refinement has order
at most $n + 1$. -/
def CoverLE (n : ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (m : ℕ) (U : Fin m → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ∃ (k : ℕ) (V : Fin k → Set X),
      (∀ j, IsOpen (V j)) ∧ (⋃ j, V j) = Set.univ ∧
      (∀ j, ∃ i, V j ⊆ U i) ∧
      ∀ s : Finset (Fin k), s.card = n + 2 →
        (⋂ j ∈ s, V j) = ∅

/--
**Small inductive and covering dimension can differ for compact Hausdorff spaces.** Scottish
Book Problem 187, part (2), has a negative answer: it is not the case that for every compact
Hausdorff space $X$ and every $n \in \mathbb{N}$, $X$ has small inductive dimension at most $n$
if and only if $X$ has covering dimension at most $n$.

The small inductive dimension is used here; Alexandroff's typescript does not say whether small or
large inductive dimension is meant. The Lunts–Lokutsievskii example is a compact Hausdorff space
$X$ whose covering dimension $\dim X$ differs from its small inductive dimension
$\operatorname{ind} X$ (Encyclopedia of Mathematics, "Dimension theory"; R. Engelking, Dimension
Theory, North-Holland, 1978).

Source: P. Alexandroff, Problem 187 part (2) of the Scottish Book,
typescript pp. 82–83.
-/
theorem_wanted scottishBook187b_refuted :
    ¬ ∀ (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X],
      ∀ n : ℕ, HasSmallInductiveDimensionLE X n ↔ CoverLE n X

end MathlibExt.Topology.ScottishBook187bWanted
