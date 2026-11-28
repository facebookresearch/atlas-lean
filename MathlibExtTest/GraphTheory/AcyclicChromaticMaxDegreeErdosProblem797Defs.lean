/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Defs
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted

/-- The edgeless graph has an acyclic coloring with one color. -/
example : IsAcyclicColoring (⊥ : SimpleGraph (Fin 3)) (fun _ => (0 : Fin 1)) :=
  ⟨fun _ _ h => h.elim, fun _ _ => by simp⟩

/-- An acyclic coloring is proper: one color on an edge is not acyclic. -/
example : ¬ IsAcyclicColoring (⊤ : SimpleGraph (Fin 2)) (fun _ => (0 : Fin 1)) :=
  fun h => h.1 0 1 (by decide) rfl

/-- The proper two-coloring of the `4`-cycle is not acyclic: its two color classes induce the
whole cycle. -/
example : ¬ IsAcyclicColoring (SimpleGraph.cycleGraph 4)
    (fun v => (⟨v.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) := by
  rintro ⟨-, h⟩
  have h01 := h 0 1
  have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have hG : (SimpleGraph.cycleGraph 4).IsAcyclic :=
    h01.comap ⟨fun v => ⟨v, hall _⟩, fun hvw => hvw⟩ fun _ _ hvw => congrArg Subtype.val hvw
  exact SimpleGraph.isAcyclic_iff_free_cycleGraph.mp hG 4 (by decide) ⟨SimpleGraph.Copy.id _⟩

end MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted
