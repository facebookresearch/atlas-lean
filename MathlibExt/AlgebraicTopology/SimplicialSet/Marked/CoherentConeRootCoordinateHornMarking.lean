/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHorn
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCoverage

/-!
# Every original mark occurs in the same original root-coordinate horn

A marked original edge keeps its whole original subset maximum. A
positive such maximum is an unchanged upper coordinate throughout the
edge. At maximum root, the original nonomitted top coordinate is absent
throughout. Thus every actual original mark already lies in the original
horn and in the SAME original upper-endpoint/boundary prism source.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Every actual maximum-marked larger-root edge is already in the SAME original root-coordinate horn when its
omitted coordinate is nonterminal. -/
theorem coneRootCoordinateHorn_marked_edge_mem {n : ℕ} (j : Fin (n + 2))
    (hj : j < Fin.last (n + 1)) (e : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet _⦋1⦌)
    (he : e ∈ (coneWeight (⊥ : Vertex.{u} (n + 1))).marking) :
    e ∈ (coneRootCoordinateHorn j).obj (op ⦋1⦌) := by
  apply (mem_coneRootCoordinateHorn_iff j (op ⦋1⦌) e).mpr
  change (e.obj 0).maximum = (e.obj 1).maximum at he
  by_cases h₀ : (e.obj 0).maximum = (⊥ : Vertex.{u} (n + 1))
  · right
    have htop : (⊥ : Vertex.{u} (n + 1)) < ⊤ := by
      change 0 < n + 1
      omega
    have hne : (⊤ : Vertex.{u} (n + 1)) ≠ ULift.up j :=
      ne_of_gt (show (ULift.up j : Vertex.{u} (n + 1)) < ⊤ from hj)
    refine ⟨⟨⊤, htop, hne⟩, fun t ht => ?_⟩
    have hm : (e.obj t).maximum = (⊥ : Vertex.{u} (n + 1)) := by
      fin_cases t
      · exact h₀
      · exact he.symm.trans h₀
    have hbad : (⊤ : Vertex.{u} (n + 1)) ≤ ⊥ := hm ▸ (e.obj t).le_maximum _ ht
    exact (not_le_of_gt htop) hbad
  · left
    have hpos : (⊥ : Vertex.{u} (n + 1)) < (e.obj 0).maximum :=
      lt_of_le_of_ne bot_le (Ne.symm h₀)
    refine ⟨⟨(e.obj 0).maximum, hpos⟩, fun t => ?_⟩
    fin_cases t
    · exact (e.obj 0).maximum_mem
    · have hsub : e.obj 0 ≤ e.obj 1 :=
        leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
      exact hsub (e.obj 0).maximum_mem

/-- The same original root-horn marked inclusion covers every original target mark, retaining its whole original
edge and literal inclusion. -/
theorem coneRootCoordinateHornMap_markingSurjective {n : ℕ} (j : Fin (n + 2))
    (hj : j < Fin.last (n + 1)) : MarkingSurjective (coneRootCoordinateHornMap.{u} j) := by
  intro e he
  let a : (coneRootCoordinateHorn j).toSSet _⦋1⦌ := ⟨e, coneRootCoordinateHorn_marked_edge_mem j hj e he⟩
  exact ⟨a, he, rfl⟩

/-- Every actual inherited original mark of the complete coordinate prism already lies in its SAME original
upper-endpoint and smaller-root coordinate-boundary source. -/
theorem coneRootCoordinateWholeAmbient_marks_mem {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1))
    (e : (coneRootCoordinateWholeAmbient j hj).toSSet _⦋1⦌)
    (he : e ∈ (coneRootCoordinateWholeAmbient j hj).marking) :
    e ∈ (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1))
      (coneCoordinateBoundary (⊥ : Vertex.{u} n))).obj (op ⦋1⦌) := by
  have h : e ∈ ((coneRootCoordinateHorn j).preimage (coneRootCoordinateWholeMap j hj)).obj (op ⦋1⦌) :=
    coneRootCoordinateHorn_marked_edge_mem j hj' ((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌) e) he
  exact (congrArg (fun A : (coneRootCoordinateWholeAmbient j hj).toSSet.Subcomplex => e ∈ A.obj (op ⦋1⦌))
    (coneRootCoordinateHorn_preimage j hj)).to_iff.mp h

end SSet.Marked.CoherentWeight
