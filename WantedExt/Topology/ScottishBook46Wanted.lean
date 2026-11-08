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
Banach, Problem 46 of the Scottish Book. Original question: is the sphere
in a space of type (B) uni-coherent? That is, whenever it is written as a
union of two continua `A` and `B`, is their intersection `A ∩ B` connected?
Here "continua" means closed connected sets (uni-coherence for non-compact
spaces), not compact connected sets: in infinite dimensions the sphere is not
compact, so requiring `A, B` compact would make the hypotheses inconsistent
and the statement vacuous. The answer is affirmative. The statement is guarded
to infinite-dimensional
spaces: in dimension 1 the sphere is two points, and in dimension 2 it is
a circle, and neither is uni-coherent (two semicircles cover the circle and
meet in two points). In infinite dimensions the sphere is an absolute
retract, and the affirmative answer follows from the theorems of Borsuk and
Eilenberg recorded in the addendum.
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
