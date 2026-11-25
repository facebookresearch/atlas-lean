/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.ScottishBook46Wanted

/--
**Unit spheres of infinite-dimensional Banach spaces are unicoherent.** Let $E$ be a real
Banach space that is not finite-dimensional, and let $S = \{x \in E : \|x\| = 1\}$ be its unit
sphere. If $A$ and $B$ are closed connected subsets of $S$ with $A \cup B = S$, then $A \cap B$ is
connected. Here connected sets are nonempty by definition.

This answers Banach's Problem 46 of the Scottish Book: is the sphere in a space of type (B)
uni-coherent, that is, whenever it is the union of two continua $A$ and $B$, is $A \cap B$
connected? Continua are read as closed connected sets, the meaning of uni-coherence for
non-compact spaces: in infinite dimensions the sphere is not compact, so two compact sets could
not cover it. The statement is restricted to infinite-dimensional spaces; in dimension $1$ the
sphere is two points and in dimension $2$ it is a circle, and neither is uni-coherent (two
semicircles cover the circle and meet in two points). In infinite dimensions the sphere is an
absolute retract, and the affirmative answer follows from the theorems of Borsuk and Eilenberg
recorded in the addendum.

Source: S. Banach, Problem 46 of the Scottish Book; addendum in the
Scottish Book citing Borsuk and Eilenberg, Fund. Math. 26, p. 61; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015).
-/
theorem_wanted sphere_in_banach_space_is_unicoherent :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∀ A B : Set E, A ⊆ Metric.sphere (0 : E) 1 → B ⊆ Metric.sphere (0 : E) 1 →
        A ∪ B = Metric.sphere (0 : E) 1 → IsClosed A → IsConnected A →
        IsClosed B → IsConnected B → IsConnected (A ∩ B)

end MathlibExt.Topology.ScottishBook46Wanted
