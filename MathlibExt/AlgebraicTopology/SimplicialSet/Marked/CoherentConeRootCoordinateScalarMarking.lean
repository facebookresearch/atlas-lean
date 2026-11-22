/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateInsertion
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Actual inherited marks of original root-coordinate scalar cells

The same whole coface scalar word reads its original maxima at every
scalar vertex. A nonterminal inserted coordinate leaves the actual final
scalar maximum unchanged. Every marked edge of the original scalar cell
already lies in its original endpoint/boundary source; in dimension one
the only missing scalar edge crosses distinct original maxima.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original nonterminal coface preserves the unchanged original final ordinal vertex. -/
theorem coneRootCoordinateCoface_top {n : ℕ} (j : Fin (n + 2))
    (hj : j < Fin.last (n + 1)) :
    coneCofaceEmbedding.{u} j (⊤ : Vertex.{u} n) = (⊤ : Vertex.{u} (n + 1)) := by
  apply ULift.ext
  change j.succAbove (Fin.last n) = Fin.last (n + 1)
  exact Fin.succAbove_ne_last_last (ne_of_lt hj)

/-- Every original scalar position retains exactly the original coface image of the unchanged original scalar
maximum. -/
theorem coneRootCoordinateCofaceScalar_maximum {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) (q : SimplexCategoryᵒᵖ)
    (b : (Δ[d] : SSet.{u}).obj q) (t : Fin (q.unop.len + 1)) :
    (((coneRootCofaceImage j hj).hom.app q ((yonedaEquiv.symm a).app q b)).obj t).maximum =
      coneCofaceEmbedding j (a.obj (stdSimplex.asOrderHom b t)).maximum :=
  coneRootCofaceImage_maximum j hj q ((yonedaEquiv.symm a).app q b) t

/-- Every original coordinate edge over the original final scalar vertex retains the actual same maximum and is
therefore originally marked. -/
theorem coneRootCoordinateScalarAmbient_final_edge_marked {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1))
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n))
    (e : ((Δ[1] : SSet.{u}) ⊗ Δ[d]) _⦋1⦌)
    (h₀ : stdSimplex.asOrderHom e.2 0 = Fin.last d)
    (h₁ : stdSimplex.asOrderHom e.2 1 = Fin.last d) :
    e ∈ (coneRootCoordinateScalarAmbient j hj a).marking := by
  change (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 0).maximum =
    (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 1).maximum
  have hM (t : Fin 2) (ht : stdSimplex.asOrderHom e.2 t = Fin.last d) :
      (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj t).maximum =
        (⊤ : Vertex.{u} (n + 1)) := by
    rw [coneRootCoordinateScalarMap_vertex, coneRootCoordinateLevel_maximum,
      coneRootCoordinateCofaceScalar_maximum, ht, ha, coneRootCoordinateCoface_top j hj']
    split_ifs
    · rfl
    · exact max_eq_right le_top
  exact (hM 0 h₀).trans (hM 1 h₁).symm

/-- All actual original marks lie in the same original endpoint/scalar-boundary source, retaining the original
crossing-edge obstruction in scalar dimension one. -/
theorem coneRootCoordinateScalarAmbient_marks_mem {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n))
    (e : ((Δ[1] : SSet.{u}) ⊗ Δ[d]) _⦋1⦌)
    (he : e ∈ (coneRootCoordinateScalarAmbient j hj a).marking) :
    e ∈ (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).obj (op ⦋1⦌) := by
  classical
  apply (Subcomplex.mem_unionProd_iff _ _ e).mpr
  left
  by_cases hd' : 1 < d
  · rw [boundary_obj_eq_univ 1 d hd']
    exact Set.mem_univ _
  · obtain rfl : d = 1 := by omega
    by_contra hb
    have hs : Function.Surjective (stdSimplex.asOrderHom e.2) := by
      intro v
      by_contra hv
      apply hb
      exact (mem_boundary_iff_notMem_range e.2).mpr ⟨v, hv⟩
    obtain ⟨s₀, hs₀⟩ := hs 0
    obtain ⟨s₁, hs₁⟩ := hs (Fin.last 1)
    have h₀ : stdSimplex.asOrderHom e.2 (0 : Fin 2) = 0 :=
      le_antisymm (((stdSimplex.asOrderHom e.2).monotone (Fin.zero_le s₀)).trans_eq hs₀)
        (Fin.zero_le _)
    have h₁ : stdSimplex.asOrderHom e.2 (1 : Fin 2) = Fin.last 1 :=
      le_antisymm (Fin.le_last _) (hs₁ ▸ (stdSimplex.asOrderHom e.2).monotone (Fin.le_last s₁))
    have hM₀ : (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 0).maximum ≤
        (ULift.up j : Vertex.{u} (n + 1)) := by
      rw [coneRootCoordinateScalarMap_vertex, coneRootCoordinateLevel_maximum,
        coneRootCoordinateCofaceScalar_maximum, h₀, ha₀, coneCofaceEmbedding_root j hj]
      split_ifs
      · exact bot_le
      · exact max_le le_rfl bot_le
    have hM₁ : (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 1).maximum =
        (⊤ : Vertex.{u} (n + 1)) := by
      rw [coneRootCoordinateScalarMap_vertex, coneRootCoordinateLevel_maximum,
        coneRootCoordinateCofaceScalar_maximum, h₁, ha₁, coneRootCoordinateCoface_top j hj']
      split_ifs
      · rfl
      · exact max_eq_right le_top
    have hE : (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 0).maximum =
        (((coneRootCoordinateScalarMap j hj a).app (op ⦋1⦌) e).obj 1).maximum := he
    have hbad : (⊤ : Vertex.{u} (n + 1)) ≤ (ULift.up j : Vertex.{u} (n + 1)) :=
      hM₁ ▸ hE ▸ hM₀
    exact (not_le_of_gt (show (ULift.up j : Vertex.{u} (n + 1)) < ⊤ from hj')) hbad

end SSet.Marked.CoherentWeight
