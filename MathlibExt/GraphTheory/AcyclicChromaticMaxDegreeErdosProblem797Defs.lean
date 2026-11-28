/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Acyclic colorings: definitions
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Acyclic colorings: definitions

Acyclic colorings of a simple graph (`IsAcyclicColoring`): proper colorings in which any two color
classes induce a forest, i.e. no cycle uses only two colors. This is the definition that the
statements of `WantedExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted`, and of the
wanted modules built on it, use, moved here unchanged (name included) so that their proofs can
import it.

Source: B. Grünbaum, "Acyclic colorings of planar graphs", Israel J. Math. 14 (1973), 390-408.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted

/-- An acyclic coloring: a proper coloring in which the union of any two color classes induces a
forest, i.e. no cycle uses only two colors. -/
def IsAcyclicColoring {V : Type*} (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ i j : Fin k, (G.induce {v | c v = i ∨ c v = j}).IsAcyclic

end MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted
