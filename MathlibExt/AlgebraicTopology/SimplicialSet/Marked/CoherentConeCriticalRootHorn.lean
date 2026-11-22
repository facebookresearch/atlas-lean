/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornCoordinatePairs

/-!
# The entire original root horn with its critical final-edge marking

The source keeps every original upper coordinate and all original lower
coordinates except the terminal one. Its marking is the exact pullback
of the actual critical coefficient marking. Every newly marked critical
edge already belongs to its original upper predecessor face, so the
original source and target retain the same marked edge while keeping
their complete original subcomplex carriers and attaching maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The SAME original critical root horn retains its whole terminal-coordinate subcomplex and exactly the marking
inherited from the whole critical cone. -/
def coneCriticalRootHornMarked (n : ℕ) : Marked.{u} :=
  comap (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))
    (coneRootCoordinateHorn (Fin.last (n + 2))).ι

/-- The entire original critical marked root horn enters its SAME full original critical cone coefficient by its
literal whole subcomplex inclusion. -/
def coneCriticalRootHornMap (n : ℕ) :
    coneCriticalRootHornMarked.{u} n ⟶ coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) :=
  comapHom (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) (coneRootCoordinateHorn (Fin.last (n + 2))).ι

/-- The same full original critical root horn map is monic on its complete unchanged simplicial carrier. -/
instance coneCriticalRootHornMap_mono (n : ℕ) : Mono (coneCriticalRootHornMap.{u} n) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneRootCoordinateHorn.{u} (Fin.last (n + 2))).ι)

/-- The original entire constant-maximum horn source enters its critical marking by its literal underlying identity. -/
def coneCriticalRootHornMark (n : ℕ) :
    coneRootCoordinateHornMarked.{u} (Fin.last (n + 2)) ⟶ coneCriticalRootHornMarked.{u} n where
  hom := 𝟙 _
  preserve he := congrArg (coneCriticalMaximumCollapse n) he

/-- The same original full horn carrier and both exact attaching maps give the actual complete critical root marking
square. -/
theorem coneCriticalRootHornMark_square (n : ℕ) :
    coneCriticalRootHornMark.{u} n ≫ coneCriticalRootHornMap n =
      coneRootCoordinateHornMap (Fin.last (n + 2)) ≫ coneCriticalMark n (⊥ : Vertex.{u} (n + 2)) := Hom.ext rfl

/-- The SAME original critical predecessor is an actual positive root coordinate in every original arity. -/
theorem coneCriticalPrevious_pos (n : ℕ) : (⊥ : Vertex.{u} (n + 2)) < coneCriticalPrevious n := by
  change 0 < n + 1
  exact Nat.zero_lt_succ n

/-- Every original full edge with the critical predecessor maximum lies in the SAME original upper-predecessor
coordinate face of the whole terminal root horn. -/
theorem coneCritical_changed_edge_mem_horn (n : ℕ)
    (e : (nerve (ConeSubset (⊥ : Vertex.{u} (n + 2)))) _⦋1⦌)
    (he : (e.obj 0).maximum = coneCriticalPrevious n) :
    e ∈ (coneRootCoordinateHorn (Fin.last (n + 2))).obj (op ⦋1⦌) := by
  have h₀ : coneCriticalPrevious n ∈ (e.obj 0).vertices := he ▸ (e.obj 0).maximum_mem
  have h₁ : coneCriticalPrevious n ∈ (e.obj 1).vertices :=
    leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 from Fin.zero_le _))) h₀
  apply (mem_coneRootCoordinateHorn_iff (Fin.last (n + 2)) _ e).mpr
  left
  refine ⟨⟨coneCriticalPrevious n, coneCriticalPrevious_pos.{u} n⟩, fun t => ?_⟩
  fin_cases t
  · exact h₀
  · exact h₁

/-- Every newly marked critical edge is retained on the complete original horn source, with its same original whole
scalar word and maximum change. -/
theorem coneCritical_new_mark_in_original_horn (n : ℕ)
    (e : (nerve (ConeSubset (⊥ : Vertex.{u} (n + 2)))) _⦋1⦌)
    (he : e ∈ (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))).marking)
    (hmax : (e.obj 0).maximum ≠ (e.obj 1).maximum) :
    e ∈ (coneRootCoordinateHorn (Fin.last (n + 2))).obj (op ⦋1⦌) := by
  rcases (coneCriticalWeight_marked_iff n _ e).mp he with h | ⟨h, _⟩
  · exact (hmax h).elim
  · exact coneCritical_changed_edge_mem_horn n e h

end SSet.Marked.CoherentWeight
