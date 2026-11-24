/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# The actual boundary of a paired edge and cone triangle

A whole cone on the two-point boundary and a whole base edge determine
the boundary of the cone triangle when their original base maps agree.
The child has the two old cone faces and the actual new base edge.
Filling this boundary is exactly extension of the whole old cone with
that base; the fixed apex is retained. This is the finite paired cell
used for the permitted unit/triangle step in a parental computad.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeEdgeBoundary

variable {H : SSet.{u}}

/-- The original base edge, whole two-point cone and literal common base. -/
@[ext]
structure Data (H : SSet.{u}) where
  /-- The entire new base edge. -/
  leading : (Δ[1] : SSet.{u}) ⟶ H
  /-- The entire original cone on the two-point boundary. -/
  cone : (∂Δ[1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H
  /-- Its original base agrees with the boundary of the new edge. -/
  base : joinInl (∂Δ[1] : SSet.{u}) Δ[0] ≫ cone = (boundary 1).ι ≫ leading

/-- An original simplicial map retains both entire boundary-data maps. -/
def Data.map {H' : SSet.{u}} (d : Data H) (p : H ⟶ H') : Data H' where
  leading := d.leading ≫ p
  cone := d.cone ≫ p
  base := by rw [← Category.assoc, d.base, Category.assoc]

private theorem point_source :
    stdSimplex.δ (1 : Fin 2) ≫ (joinStdSimplexIso.{u} 0 0).inv = joinInl Δ[0] Δ[0] := by
  have hf : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ (1 : Fin 2) := frontInclusion_eq 0
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, hf]

private theorem point_target :
    stdSimplex.δ (0 : Fin 2) ≫ (joinStdSimplexIso.{u} 0 0).inv = joinInr Δ[0] Δ[0] := by
  have hf : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ (0 : Fin 2) := rightVertex_zero
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, hf]

/-- The two original cone edges, normalized only by the native join isomorphism. -/
def oldFace (d : Data H) (j : Fin 2) : (Δ[1] : SSet.{u}) ⟶ H :=
  (joinStdSimplexIso 0 0).inv ≫ (join.map (boundary.ι j)).app Δ[0] ≫ d.cone

/-- Each old cone edge retains its original base endpoint. -/
theorem oldFace_source (d : Data H) (j : Fin 2) :
    stdSimplex.δ (1 : Fin 2) ≫ oldFace d j = stdSimplex.δ j ≫ d.leading := by
  dsimp only [oldFace]
  rw [← Category.assoc, point_source, ← Category.assoc,
    ← map_comp_joinInl, Category.assoc, d.base, ← Category.assoc, boundary.ι_ι]

/-- Both original cone edges retain the identical original apex. -/
theorem oldFace_target (d : Data H) (j : Fin 2) :
    stdSimplex.δ (0 : Fin 2) ≫ oldFace d j = joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ d.cone := by
  dsimp only [oldFace]
  rw [← Category.assoc, point_target, ← Category.assoc, joinInr_comp_map]

/-- The child faces are the two old cones and the new full base edge. -/
def faces (d : Data H) : Fin 3 → ((Δ[1] : SSet.{u}) ⟶ H) :=
  ![oldFace d 0, oldFace d 1, d.leading]

/-- Compatibility is proved from the actual common base and common apex. -/
theorem faces_compatible (d : Data H) : boundary.IsCompatible (faces d) := by
  rw [boundary.isCompatible_succ_iff]
  intro j k hjk
  have h0 := oldFace_source d 0
  have h1 := oldFace_source d 1
  have ht0 := oldFace_target d 0
  have ht1 := oldFace_target d 1
  fin_cases j <;> fin_cases k <;>
    simp only [faces, Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
      Fin.isValue, Matrix.cons_val] at hjk ⊢ <;> simp_all

/-- The actual standard two-simplex boundary map of the paired cell. -/
def boundary (d : Data H) : (∂Δ[2] : SSet.{u}) ⟶ H := (faces_compatible d).desc

/-- Every child boundary face is its prescribed whole original edge. -/
theorem boundary_face (d : Data H) (j : Fin 3) :
    SSet.boundary.ι j ≫ boundary d = faces d j := (faces_compatible d).ι_desc j

/-- The whole original face map commutes with the literal simplicial map. -/
theorem oldFace_map {H' : SSet.{u}} (d : Data H) (p : H ⟶ H') (j : Fin 2) :
    oldFace (d.map p) j = oldFace d j ≫ p := by simp only [oldFace, Data.map, Category.assoc]

/-- The full child boundary commutes with the literal simplicial map. -/
theorem boundary_map {H' : SSet.{u}} (d : Data H) (p : H ⟶ H') :
    boundary (d.map p) = boundary d ≫ p := by
  apply SSet.boundary.hom_ext
  intro j
  rw [boundary_face, ← Category.assoc, boundary_face]
  fin_cases j
  · exact oldFace_map d p 0
  · exact oldFace_map d p 1
  · rfl

private theorem join_edge_face (j : Fin 2) :
    (join.map (stdSimplex.δ j)).app (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso 1 0).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ j.castSucc := by
  have h := JoinHorn.Internal.joinHorn_dualFrontPush (k' := 0) (m := 0) j j.castSucc rfl rfl
  simpa only [JoinHorn.Internal.joinHornΔcast, JoinHorn.Internal.joinHornΔcastIso,
    CategoryTheory.Functor.mapIso_hom, eqToIso.hom, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp] using h

private theorem slice_read_precomp {A B : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H)
    (q : B ⟶ sliceOver H z) (i : A ⟶ B) :
    (sliceOver.homEquiv H z A (i ≫ q)).val =
      (join.map i).app Δ[0] ≫ (sliceOver.homEquiv H z B q).val := by
  simp only [sliceOver.homEquiv_apply, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- Whole cones on the two-point boundary are determined by the two whole edges
and their common original apex, through the actual slice adjunction. -/
theorem cone_hom_ext (l r : (∂Δ[1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (ha : joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ l = joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ r)
    (hf : ∀ j : Fin 2, (join.map (SSet.boundary.ι j)).app Δ[0] ≫ l =
      (join.map (SSet.boundary.ι j)).app Δ[0] ≫ r) : l = r := by
  let z : (Δ[0] : SSet.{u}) ⟶ H := joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ r
  let L : (∂Δ[1] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨l, ha⟩
  let R : (∂Δ[1] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨r, rfl⟩
  have hL : (sliceOver.homEquiv H z _ L).val = l :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hR : (sliceOver.homEquiv H z _ R).val = r :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hLR : L = R := by
    apply SSet.boundary.hom_ext
    intro j
    apply (sliceOver.homEquiv H z Δ[0]).injective
    apply Subtype.ext
    rw [slice_read_precomp, slice_read_precomp, hL, hR]
    exact hf j
  exact hL.symm.trans ((congrArg (fun q => (sliceOver.homEquiv H z _ q).val) hLR).trans hR)

/-- A filler of the actual child boundary extends the whole original cone and
has the original new base edge. Both entire maps are retained. -/
theorem extends_of_boundary (d : Data H) (h : (Δ[2] : SSet.{u}) ⟶ H)
    (hh : (SSet.boundary 2).ι ≫ h = boundary d) :
    joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary 1).ι).app Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.cone := by
  let q : (Δ[1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H := (joinStdSimplexIso 1 0).hom ≫ h
  have hface (j : Fin 3) : stdSimplex.δ j ≫ h = faces d j :=
    (SSet.boundary.ι_ι_assoc j h).symm.trans
      ((congrArg (fun q => SSet.boundary.ι j ≫ q) hh).trans (boundary_face d j))
  have hq (j : Fin 2) : (join.map (stdSimplex.δ j)).app Δ[0] ≫ q =
      (join.map (SSet.boundary.ι j)).app Δ[0] ≫ d.cone := by
    dsimp only [q]
    rw [← Category.assoc, join_edge_face, Category.assoc, hface]
    have hv : faces d j.castSucc = oldFace d j := by fin_cases j <;> rfl
    rw [hv, oldFace, Iso.hom_inv_id_assoc]
  refine ⟨?_, ?_⟩
  · have hf : joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 1 0).hom =
        stdSimplex.δ (2 : Fin 3) := frontInclusion_eq 1
    rw [← Category.assoc, hf, hface]
    rfl
  · apply cone_hom_ext
    · have ha : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
          ((join.map (stdSimplex.δ (0 : Fin 2))).app Δ[0] ≫ q) =
        joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
          ((join.map (SSet.boundary.ι (0 : Fin 2))).app Δ[0] ≫ d.cone) :=
        congrArg (fun v => joinInr Δ[0] Δ[0] ≫ v) (hq 0)
      have h0 : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
          (join.map (stdSimplex.δ (0 : Fin 2))).app Δ[0] = joinInr Δ[1] Δ[0] :=
        joinInr_comp_map _ _
      have h1 : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
          (join.map (SSet.boundary.ι (0 : Fin 2))).app Δ[0] = joinInr (∂Δ[1] : SSet.{u}) Δ[0] :=
        joinInr_comp_map _ _
      have h2 : joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫
          (join.map (SSet.boundary 1).ι).app Δ[0] = joinInr Δ[1] Δ[0] :=
        joinInr_comp_map _ _
      have haq : joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ q =
          joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ d.cone :=
        ((congrArg (fun v => v ≫ q) h0).symm.trans (Category.assoc _ _ _)).trans
          (ha.trans ((Category.assoc _ _ _).symm.trans (congrArg (fun v => v ≫ d.cone) h1)))
      change joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫
        ((join.map (SSet.boundary 1).ι).app Δ[0] ≫ q) = _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (fun v => v ≫ q) h2).trans haq)
    · intro j
      rw [← Category.assoc, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
        SSet.boundary.ι_ι]
      exact hq j

private theorem restriction_old_face (h : (Δ[2] : SSet.{u}) ⟶ H) (j : Fin 2) :
    (joinStdSimplexIso 0 0).inv ≫ (join.map (SSet.boundary.ι j)).app Δ[0] ≫
      ((join.map (SSet.boundary 1).ι).app Δ[0] ≫ (joinStdSimplexIso 1 0).hom ≫ h) =
        stdSimplex.δ j.castSucc ≫ h := by
  have hm : (join.map (SSet.boundary.ι j)).app (Δ[0] : SSet.{u}) ≫
      (join.map (SSet.boundary 1).ι).app Δ[0] = (join.map (stdSimplex.δ j)).app Δ[0] := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, SSet.boundary.ι_ι]
  calc
    _ = (joinStdSimplexIso 0 0).inv ≫
        ((join.map (SSet.boundary.ι j)).app Δ[0] ≫ (join.map (SSet.boundary 1).ι).app Δ[0]) ≫
          (joinStdSimplexIso 1 0).hom ≫ h := by simp only [Category.assoc]
    _ = (joinStdSimplexIso 0 0).inv ≫ (join.map (stdSimplex.δ j)).app Δ[0] ≫
        (joinStdSimplexIso 1 0).hom ≫ h := by rw [hm]
    _ = ((joinStdSimplexIso 0 0).inv ≫
        ((join.map (stdSimplex.δ j)).app Δ[0] ≫ (joinStdSimplexIso 1 0).hom)) ≫ h := by
      simp only [Category.assoc]
    _ = ((joinStdSimplexIso 0 0).inv ≫
        ((joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ j.castSucc)) ≫ h :=
      congrArg (fun v => ((joinStdSimplexIso 0 0).inv ≫ v) ≫ h) (join_edge_face j)
    _ = stdSimplex.δ j.castSucc ≫ h := by simp only [Iso.inv_hom_id_assoc]

/-- Extension of both original maps implies filling of the actual full child boundary. -/
theorem boundary_of_extends (d : Data H) (h : (Δ[2] : SSet.{u}) ⟶ H)
    (hb : joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.leading)
    (hc : (join.map (SSet.boundary 1).ι).app Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.cone) :
    (SSet.boundary 2).ι ≫ h = boundary d := by
  apply SSet.boundary.hom_ext
  intro j
  rw [SSet.boundary.ι_ι_assoc, boundary_face]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 3) ≫ h = oldFace d 0
    have hd := congrArg (fun v => (joinStdSimplexIso 0 0).inv ≫
      (join.map (SSet.boundary.ι (0 : Fin 2))).app Δ[0] ≫ v) hc
    exact (restriction_old_face h 0).symm.trans hd
  · change stdSimplex.δ (1 : Fin 3) ≫ h = oldFace d 1
    have hd := congrArg (fun v => (joinStdSimplexIso 0 0).inv ≫
      (join.map (SSet.boundary.ι (1 : Fin 2))).app Δ[0] ≫ v) hc
    exact (restriction_old_face h 1).symm.trans hd
  · change stdSimplex.δ (2 : Fin 3) ≫ h = d.leading
    have hf : joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 1 0).hom =
        stdSimplex.δ (2 : Fin 3) := frontInclusion_eq 1
    rw [← Category.assoc, hf] at hb
    exact hb

/-- The full standard child boundary is equivalent to extension of both entire original maps. -/
theorem fill_iff (d : Data H) (h : (Δ[2] : SSet.{u}) ⟶ H) :
    (SSet.boundary 2).ι ≫ h = boundary d ↔
      joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary 1).ι).app Δ[0] ≫ ((joinStdSimplexIso 1 0).hom ≫ h) = d.cone :=
  ⟨extends_of_boundary d h, fun h0 => boundary_of_extends d h h0.1 h0.2⟩

end SSet.WalkingAdjunction.ConeEdgeBoundary
