/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Degenerate
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# The original ordered-interval endpoint fibrations

The source endpoint of the original ordered interval is a Cartesian
fibration, with its empty fibre over the other endpoint. The target
endpoint is the dual cocartesian fibration. All incoming respectively
outgoing original interval edges at the supplied endpoint are identities.
These are native fibration predicates at every value universe; no marked
model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

private theorem face_singleton_full (v : Fin 2) :
    stdSimplex.face.{u} {v} =
      Subcomplex.full ({stdSimplex.obj₀Equiv.symm v} : Set ((Δ[1] : SSet.{u}) _⦋0⦌)) := by
  ext m s
  rcases m with ⟨m⟩
  induction m using SimplexCategory.rec with | _ n =>
    rw [stdSimplex.mem_face_iff, Subcomplex.mem_full_obj_iff_vertices]
    constructor
    · intro h i
      apply stdSimplex.obj₀Equiv.injective
      change s i = v
      exact Finset.mem_singleton.mp (h i)
    · intro h i
      have hi := congrArg (fun t : (Δ[1] : SSet.{u}) _⦋0⦌ => t 0) (h i)
      change s i = v at hi
      exact Finset.mem_singleton.mpr hi

private theorem endpoint_inner (ε : Fin 2) : InnerFibration (stdSimplex.{u}.δ ε) := by
  fin_cases ε
  · change InnerFibration (stdSimplex.{u}.δ (0 : Fin 2))
    let _ : InnerFibration (stdSimplex.face.{u} {1}).ι := by
      rw [face_singleton_full]
      infer_instance
    rw [← stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
    exact ⟨innerFibrations.comp_mem _ _ (innerHornInclusions.rlp_of_isIso _) InnerFibration.mem⟩
  · change InnerFibration (stdSimplex.{u}.δ (1 : Fin 2))
    let _ : InnerFibration (stdSimplex.face.{u} {0}).ι := by
      rw [face_singleton_full]
      infer_instance
    rw [← stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
    exact ⟨innerFibrations.comp_mem _ _ (innerHornInclusions.rlp_of_isIso _) InnerFibration.mem⟩

/-- The original endpoint inclusion sends every actual zero simplex to its same original ordered-interval vertex. -/
theorem stdSimplex.endpoint_vertex_image (ε : Fin 2) (y : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (stdSimplex.δ ε).app (op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (ε.succAbove 0) := by
  apply stdSimplex.ext
  intro i
  exact congrArg ε.succAbove (Fin.eq_zero (y i))

/-- The original source endpoint is a genuine Cartesian fibration of the noninvertible ordered interval. -/
theorem stdSimplex.sourceEndpoint_cartesianFibration :
    CartesianFibration (stdSimplex.{u}.δ (1 : Fin 2)) := by
  let p : (Δ[0] : SSet.{u}) ⟶ Δ[1] := stdSimplex.δ 1
  let _ : InnerFibration p := endpoint_inner 1
  refine { toInnerFibration := (inferInstance : InnerFibration p), lift := ?_ }
  intro y b e
  obtain ⟨i, hi⟩ := stdSimplex.objMk₁_surjective e.edge
  fin_cases i
  · have h := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) e.tgt_eq
    rw [← hi] at h
    have hv := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) (stdSimplex.endpoint_vertex_image 1 y)
    have hbad : (1 : Fin 2) = 0 := h.trans hv
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hbad)
  · have h := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) e.tgt_eq
    rw [← hi] at h
    have hv := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) (stdSimplex.endpoint_vertex_image 1 y)
    have hbad : (1 : Fin 2) = 0 := h.trans hv
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hbad)
  · let a := Edge.id y
    have hmap : (a.map p).edge = e.edge := by
      have hv : p.app (op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm 0 := stdSimplex.endpoint_vertex_image 1 y
      have hm : (a.map p).edge = (Edge.id (stdSimplex.obj₀Equiv.symm 0)).edge :=
        (congrArg Edge.edge (Edge.map_id y p)).trans (congrArg (fun v => (Edge.id v).edge) hv)
      have hzero : (Edge.id (stdSimplex.obj₀Equiv.symm 0 : (Δ[1] : SSet.{u}) _⦋0⦌)).edge =
          stdSimplex.objMk₁ (2 : Fin 3) := by
        apply stdSimplex.ext
        intro j
        fin_cases j <;> rfl
      exact hm.trans (hzero.trans hi)
    have hb : p.app (op ⦋0⦌) y = b := (a.map p).src_eq.symm.trans
      ((congrArg ((Δ[1] : SSet.{u}).δ (1 : Fin 2)) hmap).trans e.src_eq)
    exact ⟨y, hb, a, CartesianEdge.isPCartesian_degenerate p y, hmap⟩

/-- The original target endpoint is the genuine cocartesian fibration with the dual empty original fibre. -/
theorem stdSimplex.targetEndpoint_cocartesianFibration :
    CocartesianFibration (stdSimplex.{u}.δ (0 : Fin 2)) := by
  let p : (Δ[0] : SSet.{u}) ⟶ Δ[1] := stdSimplex.δ 0
  let _ : InnerFibration p := endpoint_inner 0
  refine { toInnerFibration := (inferInstance : InnerFibration p), lift := ?_ }
  intro y b e
  obtain ⟨i, hi⟩ := stdSimplex.objMk₁_surjective e.edge
  fin_cases i
  · let a := Edge.id y
    have hmap : (a.map p).edge = e.edge := by
      have hv : p.app (op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm 1 := stdSimplex.endpoint_vertex_image 0 y
      have hm : (a.map p).edge = (Edge.id (stdSimplex.obj₀Equiv.symm 1)).edge :=
        (congrArg Edge.edge (Edge.map_id y p)).trans (congrArg (fun v => (Edge.id v).edge) hv)
      exact hm.trans hi
    have hb : p.app (op ⦋0⦌) y = b := (a.map p).tgt_eq.symm.trans
      ((congrArg ((Δ[1] : SSet.{u}).δ (0 : Fin 2)) hmap).trans e.tgt_eq)
    exact ⟨y, hb, a, CocartesianEdge.isPCocartesian_degenerate p y, hmap⟩
  · have h := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) e.src_eq
    rw [← hi] at h
    have hv := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) (stdSimplex.endpoint_vertex_image 0 y)
    have hbad : (0 : Fin 2) = 1 := h.trans hv
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hbad)
  · have h := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) e.src_eq
    rw [← hi] at h
    have hv := congrArg (fun x : (Δ[1] : SSet.{u}) _⦋0⦌ => x 0) (stdSimplex.endpoint_vertex_image 0 y)
    have hbad : (0 : Fin 2) = 1 := h.trans hv
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hbad)

end SSet
