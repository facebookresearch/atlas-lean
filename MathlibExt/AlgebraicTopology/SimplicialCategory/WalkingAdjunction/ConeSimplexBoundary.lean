/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeEdgeBoundary
public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.RelativeTerminal

/-!
# Whole boundaries of simplex cones

A prescribed simplex and a whole cone on its boundary, with their
original common base, determine the full next-dimensional boundary.
The old coned faces and the entire new base simplex are retained.
The one-dimensional compatibility is the existing paired-edge result;
higher compatibility uses the original boundary faces and native join
isomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeSimplexBoundary

variable {H : SSet.{u}}

/-- The original simplex, whole boundary cone and their literal common base. -/
@[ext]
structure Data (n : ℕ) (H : SSet.{u}) where
  /-- The entire prescribed new base simplex. -/
  leading : (Δ[n] : SSet.{u}) ⟶ H
  /-- The entire original cone on its standard boundary. -/
  cone : (∂Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H
  /-- The original base maps agree. -/
  base : joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫ cone = (boundary n).ι ≫ leading

/-- Postcomposition retains both entire original maps and their common base. -/
def Data.map {n : ℕ} {H' : SSet.{u}} (d : Data n H) (p : H ⟶ H') : Data n H' where
  leading := d.leading ≫ p
  cone := d.cone ≫ p
  base := by rw [← Category.assoc, d.base, Category.assoc]

/-- The original apex of the whole boundary cone. -/
def apex {n : ℕ} (d : Data n H) : (Δ[0] : SSet.{u}) ⟶ H :=
  joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ d.cone

/-- A front face joined with the apex is its original front face one dimension up. -/
theorem join_face (n : ℕ) (j : Fin (n + 2)) :
    (join.map (stdSimplex.δ j)).app (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso (n + 1) 0).hom =
      (joinStdSimplexIso n 0).hom ≫ stdSimplex.δ j.castSucc := by
  have h := JoinHorn.Internal.joinHorn_dualFrontPush (k' := n) (m := 0) j j.castSucc rfl rfl
  simpa only [JoinHorn.Internal.joinHornΔcast, JoinHorn.Internal.joinHornΔcastIso,
    CategoryTheory.Functor.mapIso_hom, eqToIso.hom, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp] using h

/-- The same original face equation in the inverse join normalization. -/
theorem face_join_inv (n : ℕ) (j : Fin (n + 2)) :
    stdSimplex.δ j.castSucc ≫ (joinStdSimplexIso (n + 1) 0).inv =
      (joinStdSimplexIso n 0).inv ≫ (join.map (stdSimplex.δ j)).app (Δ[0] : SSet.{u}) := by
  apply (cancel_mono (joinStdSimplexIso (n + 1) 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, join_face, Iso.inv_hom_id_assoc]

/-- The last face of the cone is its entire original base. -/
theorem last_face_join_inv (n : ℕ) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ (joinStdSimplexIso.{u} n 0).inv =
      joinInl Δ[n] Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso n 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (frontInclusion_eq n).symm

/-- Each old coned face is its original whole face followed by the original boundary cone. -/
def oldFace {n : ℕ} (d : Data (n + 1) H) (j : Fin (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ H :=
  (joinStdSimplexIso n 0).inv ≫ (join.map (boundary.ι j)).app Δ[0] ≫ d.cone

/-- The old coned face retains its original base face. -/
theorem oldFace_base {n : ℕ} (d : Data (n + 1) H) (j : Fin (n + 2)) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ oldFace d j = stdSimplex.δ j ≫ d.leading := by
  dsimp only [oldFace]
  rw [← Category.assoc, last_face_join_inv, ← Category.assoc,
    ← map_comp_joinInl, Category.assoc, d.base, ← Category.assoc, boundary.ι_ι]

/-- All child faces: the old coned faces and the entire new base simplex. -/
def faces {n : ℕ} (d : Data (n + 1) H) (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ H :=
  if h : j = Fin.last (n + 2) then d.leading else oldFace d (j.castPred h)

/-- Each front child face is the original coned face. -/
theorem faces_castSucc {n : ℕ} (d : Data (n + 1) H) (j : Fin (n + 2)) :
    faces d j.castSucc = oldFace d j := by simp [faces]

/-- The last child face is the entire original new base. -/
theorem faces_last {n : ℕ} (d : Data (n + 1) H) :
    faces d (Fin.last (n + 2)) = d.leading := by simp [faces]

/-- Compatibility follows from the whole common base and the actual old boundary relations. -/
theorem faces_compatible {n : ℕ} (d : Data (n + 1) H) : boundary.IsCompatible (faces d) := by
  cases n with
  | zero =>
    let e : ConeEdgeBoundary.Data H := ⟨d.leading, d.cone, d.base⟩
    have h : faces d = ConeEdgeBoundary.faces e := by
      funext j
      fin_cases j <;> simp [faces, oldFace, ConeEdgeBoundary.faces,
        ConeEdgeBoundary.oldFace, e]
    rw [h]
    exact ConeEdgeBoundary.faces_compatible e
  | succ n =>
    rw [boundary.isCompatible_succ_iff]
    intro j k hjk
    obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    by_cases hk : k = Fin.last (n + 3)
    · subst k
      rw [faces_castSucc, faces_last]
      have hp : (Fin.last (n + 3)).pred (Fin.ne_zero_of_lt hjk) = Fin.last (n + 2) := by
        apply Fin.ext
        rfl
      rw [hp, Fin.castPred_castSucc]
      exact oldFace_base d j'
    · obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
      have hj'k' : j' < k' := hjk
      rw [faces_castSucc, faces_castSucc]
      have hp : k'.castSucc.pred (Fin.ne_zero_of_lt hjk) =
          (k'.pred (Fin.ne_zero_of_lt hj'k')).castSucc := by
        apply Fin.ext
        rfl
      have hj : j'.castSucc.castPred (Fin.ne_last_of_lt hjk) =
          (j'.castPred (Fin.ne_last_of_lt hj'k')).castSucc := by
        apply Fin.ext
        rfl
      rw [hp, hj]
      dsimp only [oldFace]
      rw [← Category.assoc, face_join_inv, Category.assoc,
        ← Category.assoc (stdSimplex.δ _), face_join_inv, Category.assoc]
      have h := (boundary.isCompatible_succ_iff _).mp (boundary.ι_isCompatible (n + 1)) j' k' hj'k'
      have hm := congrArg (fun f => (joinStdSimplexIso n 0).inv ≫
        (join.map f).app (Δ[0] : SSet.{u}) ≫ d.cone) h
      simpa only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc] using hm

/-- The actual full standard child boundary determined by the two whole original maps. -/
def boundary {n : ℕ} (d : Data (n + 1) H) : (∂Δ[n + 2] : SSet.{u}) ⟶ H :=
  (faces_compatible d).desc

/-- Each full child face restricts to the prescribed whole original face. -/
theorem boundary_face {n : ℕ} (d : Data (n + 1) H) (j : Fin (n + 3)) :
    SSet.boundary.ι j ≫ boundary d = faces d j := (faces_compatible d).ι_desc j

/-- Postcomposition retains every whole coned face. -/
theorem oldFace_map {n : ℕ} {H' : SSet.{u}} (d : Data (n + 1) H) (p : H ⟶ H')
    (j : Fin (n + 2)) : oldFace (d.map p) j = oldFace d j ≫ p := by
  simp only [oldFace, Data.map, Category.assoc]

/-- Postcomposition retains the entire full child boundary. -/
theorem boundary_map {n : ℕ} {H' : SSet.{u}} (d : Data (n + 1) H) (p : H ⟶ H') :
    boundary (d.map p) = boundary d ≫ p := by
  apply SSet.boundary.hom_ext
  intro j
  rw [boundary_face, ← Category.assoc, boundary_face]
  by_cases hj : j = Fin.last (n + 2)
  · subst j
    rw [faces_last, faces_last]
    rfl
  · obtain ⟨i, rfl⟩ := j.eq_castSucc_of_ne_last hj
    rw [faces_castSucc, faces_castSucc]
    exact oldFace_map d p i

private theorem slice_read_precomp {A B : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H)
    (q : B ⟶ sliceOver H z) (i : A ⟶ B) :
    (sliceOver.homEquiv H z A (i ≫ q)).val =
      (join.map i).app Δ[0] ≫ (sliceOver.homEquiv H z B q).val := by
  simp only [sliceOver.homEquiv_apply, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- Whole boundary cones are determined by their entire coned faces and identical apex. -/
theorem cone_hom_ext {n : ℕ} (l r : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (ha : joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ l =
      joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ r)
    (hf : ∀ j : Fin (n + 2), (join.map (SSet.boundary.ι j)).app Δ[0] ≫ l =
      (join.map (SSet.boundary.ι j)).app Δ[0] ≫ r) : l = r := by
  let z : (Δ[0] : SSet.{u}) ⟶ H := joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ r
  let L : (∂Δ[n + 1] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨l, ha⟩
  let R : (∂Δ[n + 1] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨r, rfl⟩
  have hL : (sliceOver.homEquiv H z _ L).val = l :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hR : (sliceOver.homEquiv H z _ R).val = r :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hLR : L = R := by
    apply SSet.boundary.hom_ext
    intro j
    apply (sliceOver.homEquiv H z Δ[n]).injective
    apply Subtype.ext
    rw [slice_read_precomp, slice_read_precomp, hL, hR]
    exact hf j
  exact hL.symm.trans ((congrArg (fun q => (sliceOver.homEquiv H z _ q).val) hLR).trans hR)

/-- A cone on the empty boundary is determined by its identical original apex. -/
theorem cone_zero_hom_ext (l r : (∂Δ[0] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (ha : joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ l = joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ r) :
    l = r := by
  let z : (Δ[0] : SSet.{u}) ⟶ H := joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ r
  let L : (∂Δ[0] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨l, ha⟩
  let R : (∂Δ[0] : SSet.{u}) ⟶ sliceOver H z := (sliceOver.homEquiv H z _).symm ⟨r, rfl⟩
  have hL : (sliceOver.homEquiv H z _ L).val = l :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hR : (sliceOver.homEquiv H z _ R).val = r :=
    congrArg Subtype.val ((sliceOver.homEquiv H z _).apply_symm_apply _)
  have hLR : L = R := SSet.boundary.hom_ext₀
  exact hL.symm.trans ((congrArg (fun q => (sliceOver.homEquiv H z _ q).val) hLR).trans hR)

/-- Filling the child boundary retains the full prescribed base and whole old boundary cone. -/
theorem extends_of_boundary {n : ℕ} (d : Data (n + 1) H) (h : (Δ[n + 2] : SSet.{u}) ⟶ H)
    (hh : (SSet.boundary (n + 2)).ι ≫ h = boundary d) :
    joinInl (Δ[n + 1] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary (n + 1)).ι).app Δ[0] ≫
        ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.cone := by
  let q : (Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H :=
    (joinStdSimplexIso (n + 1) 0).hom ≫ h
  have hface (j : Fin (n + 3)) : stdSimplex.δ j ≫ h = faces d j :=
    (SSet.boundary.ι_ι_assoc j h).symm.trans
      ((congrArg (fun q => SSet.boundary.ι j ≫ q) hh).trans (boundary_face d j))
  have hq (j : Fin (n + 2)) : (join.map (stdSimplex.δ j)).app Δ[0] ≫ q =
      (join.map (SSet.boundary.ι j)).app Δ[0] ≫ d.cone := by
    dsimp only [q]
    rw [← Category.assoc, join_face, Category.assoc, hface, faces_castSucc,
      oldFace, Iso.hom_inv_id_assoc]
  refine ⟨?_, ?_⟩
  · have hf : joinInl (Δ[n + 1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso (n + 1) 0).hom =
        stdSimplex.δ (Fin.last (n + 2)) := frontInclusion_eq (n + 1)
    rw [← Category.assoc, hf, hface, faces_last]
  · apply cone_hom_ext
    · have ha := congrArg (fun v => joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ v) (hq 0)
      simp only [← Category.assoc, joinInr_comp_map] at ha
      change joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫
        ((join.map (SSet.boundary (n + 1)).ι).app Δ[0] ≫ q) = _
      rw [← Category.assoc, joinInr_comp_map]
      exact ha
    · intro j
      rw [← Category.assoc, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
        SSet.boundary.ι_ι]
      exact hq j

private theorem restriction_old_face {n : ℕ} (h : (Δ[n + 2] : SSet.{u}) ⟶ H)
    (j : Fin (n + 2)) :
    (joinStdSimplexIso n 0).inv ≫ (join.map (SSet.boundary.ι j)).app Δ[0] ≫
      ((join.map (SSet.boundary (n + 1)).ι).app Δ[0] ≫ (joinStdSimplexIso (n + 1) 0).hom ≫ h) =
        stdSimplex.δ j.castSucc ≫ h := by
  have hm : (join.map (SSet.boundary.ι j)).app (Δ[0] : SSet.{u}) ≫
      (join.map (SSet.boundary (n + 1)).ι).app Δ[0] = (join.map (stdSimplex.δ j)).app Δ[0] := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, SSet.boundary.ι_ι]
  calc
    _ = (joinStdSimplexIso n 0).inv ≫
        ((join.map (SSet.boundary.ι j)).app Δ[0] ≫
          (join.map (SSet.boundary (n + 1)).ι).app Δ[0]) ≫
          (joinStdSimplexIso (n + 1) 0).hom ≫ h := by simp only [Category.assoc]
    _ = (joinStdSimplexIso n 0).inv ≫ (join.map (stdSimplex.δ j)).app Δ[0] ≫
        (joinStdSimplexIso (n + 1) 0).hom ≫ h := by rw [hm]
    _ = stdSimplex.δ j.castSucc ≫ h := by
      have hf := congrArg (fun q => (joinStdSimplexIso n 0).inv ≫ q ≫ h) (join_face n j)
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hf

/-- Retaining the entire original base and old cone gives the full standard child boundary. -/
theorem boundary_of_extends {n : ℕ} (d : Data (n + 1) H) (h : (Δ[n + 2] : SSet.{u}) ⟶ H)
    (hb : joinInl (Δ[n + 1] : SSet.{u}) Δ[0] ≫
      ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.leading)
    (hc : (join.map (SSet.boundary (n + 1)).ι).app Δ[0] ≫
      ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.cone) :
    (SSet.boundary (n + 2)).ι ≫ h = boundary d := by
  apply SSet.boundary.hom_ext
  intro j
  rw [SSet.boundary.ι_ι_assoc, boundary_face]
  by_cases hj : j = Fin.last (n + 2)
  · subst j
    rw [faces_last]
    have hf : joinInl (Δ[n + 1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso (n + 1) 0).hom =
        stdSimplex.δ (Fin.last (n + 2)) := frontInclusion_eq (n + 1)
    rw [← Category.assoc, hf] at hb
    exact hb
  · obtain ⟨i, rfl⟩ := j.eq_castSucc_of_ne_last hj
    rw [faces_castSucc]
    have hd := congrArg (fun v => (joinStdSimplexIso n 0).inv ≫
      (join.map (SSet.boundary.ι i)).app (Δ[0] : SSet.{u}) ≫ v) hc
    exact (restriction_old_face h i).symm.trans hd

/-- A child boundary filler is exactly extension of both entire original maps. -/
theorem fill_iff {n : ℕ} (d : Data (n + 1) H) (h : (Δ[n + 2] : SSet.{u}) ⟶ H) :
    (SSet.boundary (n + 2)).ι ≫ h = boundary d ↔
      joinInl (Δ[n + 1] : SSet.{u}) Δ[0] ≫
        ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary (n + 1)).ι).app Δ[0] ≫
        ((joinStdSimplexIso (n + 1) 0).hom ≫ h) = d.cone :=
  ⟨extends_of_boundary d h, fun h0 => boundary_of_extends d h h0.1 h0.2⟩

/-- At dimension zero the two faces are the original apex and original new base point. -/
def zeroFaces (d : Data 0 H) : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ H) := ![apex d, d.leading]

/-- The full one-boundary determined by the original empty cone and new base point. -/
def zeroBoundary (d : Data 0 H) : (∂Δ[1] : SSet.{u}) ⟶ H :=
  (show SSet.boundary.IsCompatible (zeroFaces d) from True.intro).desc

/-- Both original zero-dimensional faces are retained. -/
theorem zeroBoundary_face (d : Data 0 H) (j : Fin 2) :
    SSet.boundary.ι j ≫ zeroBoundary d = zeroFaces d j :=
  SSet.boundary.IsCompatible.ι_desc _ j

/-- At dimension zero, too, the child filler retains both whole original maps. -/
theorem fill_zero_iff (d : Data 0 H) (h : (Δ[1] : SSet.{u}) ⟶ H) :
    (SSet.boundary 1).ι ≫ h = zeroBoundary d ↔
      joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso 0 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary 0).ι).app Δ[0] ≫ ((joinStdSimplexIso 0 0).hom ≫ h) = d.cone := by
  have hbase : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ (1 : Fin 2) := frontInclusion_eq 0
  have hapex : joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫
        ((join.map (SSet.boundary 0).ι).app Δ[0] ≫ (joinStdSimplexIso 0 0).hom ≫ h) =
      stdSimplex.δ (0 : Fin 2) ≫ h := by
    rw [← Category.assoc, joinInr_comp_map]
    exact congrArg (fun q => q ≫ h) rightVertex_zero
  constructor
  · intro hh
    have hf (j : Fin 2) : stdSimplex.δ j ≫ h = zeroFaces d j :=
      (SSet.boundary.ι_ι_assoc j h).symm.trans
        ((congrArg (fun q => SSet.boundary.ι j ≫ q) hh).trans (zeroBoundary_face d j))
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, hbase]
      exact hf 1
    · apply cone_zero_hom_ext
      exact hapex.trans (hf 0)
  · rintro ⟨hb, hc⟩
    apply SSet.boundary.hom_ext
    intro j
    rw [SSet.boundary.ι_ι_assoc, zeroBoundary_face]
    fin_cases j
    · change stdSimplex.δ (0 : Fin 2) ≫ h = apex d
      exact hapex.symm.trans (congrArg (fun q => joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ q) hc)
    · rw [← Category.assoc, hbase] at hb
      exact hb

/-- The actual full child boundary in every parent dimension, including the empty old boundary. -/
def fullBoundary {n : ℕ} (d : Data n H) : (∂Δ[n + 1] : SSet.{u}) ⟶ H :=
  match n with
  | 0 => zeroBoundary d
  | _m + 1 => boundary d

/-- In every dimension the actual boundary filler retains both entire original maps. -/
theorem full_fill_iff {n : ℕ} (d : Data n H) (h : (Δ[n + 1] : SSet.{u}) ⟶ H) :
    (SSet.boundary (n + 1)).ι ≫ h = fullBoundary d ↔
      joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ ((joinStdSimplexIso n 0).hom ≫ h) = d.leading ∧
      (join.map (SSet.boundary n).ι).app Δ[0] ≫ ((joinStdSimplexIso n 0).hom ≫ h) = d.cone := by
  cases n with
  | zero => exact fill_zero_iff d h
  | succ n => exact fill_iff d h

/-- The full boundary commutes with the literal original postcomposition in every dimension. -/
theorem fullBoundary_map {n : ℕ} {H' : SSet.{u}} (d : Data n H) (p : H ⟶ H') :
    fullBoundary (d.map p) = fullBoundary d ≫ p := by
  cases n with
  | zero =>
    apply SSet.boundary.hom_ext
    intro j
    change SSet.boundary.ι j ≫ zeroBoundary (d.map p) = SSet.boundary.ι j ≫ (zeroBoundary d ≫ p)
    rw [zeroBoundary_face, ← Category.assoc, zeroBoundary_face]
    fin_cases j
    · change joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ (d.cone ≫ p) =
        (joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ d.cone) ≫ p
      exact (Category.assoc _ _ _).symm
    · rfl
  | succ n => exact boundary_map d p

private theorem rightVertex_last (n : ℕ) : rightVertex.{u} n =
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))) := by
  rw [rightVertex_eq]
  apply congrArg stdSimplex.map
  ext i : 3
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rw [inr'_toOrderHom_zero]
  rfl

/-- The original last vertex of the child boundary is the identical original cone apex. -/
theorem fullBoundary_last {n : ℕ} (d : Data n H) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
      SSet.boundary.ι (0 : Fin (n + 2)) ≫ fullBoundary d = apex d := by
  cases n with
  | zero =>
    have hi : (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (Fin.last 0)) :
        (Δ[0] : SSet.{u}) ⟶ Δ[0]) = 𝟙 _ := stdSimplex.ext₀
    rw [hi, Category.id_comp]
    exact zeroBoundary_face d 0
  | succ n =>
    change stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))) ≫
      SSet.boundary.ι (0 : Fin (n + 3)) ≫ boundary d = apex d
    have hf : faces d 0 = oldFace d 0 := faces_castSucc d (0 : Fin (n + 2))
    rw [boundary_face, hf, ← rightVertex_last]
    dsimp only [rightVertex, oldFace, apex]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, joinInr_comp_map]

/-- Intrinsic terminality supplies a genuine whole cone extension retaining the original base
and the full old boundary cone, including the empty-boundary case. -/
theorem exists_terminal_extension {n : ℕ} (d : Data n H) (ht : RightTerminalVertex (apex d)) :
    ∃ q : (Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H,
      joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ q = d.leading ∧
      (join.map (SSet.boundary n).ι).app Δ[0] ≫ q = d.cone := by
  obtain ⟨h, hh⟩ := ht n (fullBoundary d) (fullBoundary_last d)
  exact ⟨(joinStdSimplexIso n 0).hom ≫ h, (full_fill_iff d h).mp hh⟩

end SSet.WalkingAdjunction.ConeSimplexBoundary
