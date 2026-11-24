/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeBoundaryHorn

/-!
# Boundary cones and the actual last outer horn

The original coned boundary is the last outer horn. Construct its
canonical map using the original over-slice adjunction and boundary
colimit. The reverse map is the existing whole cone-to-horn readback.
Every original coned face and apex is retained in both directions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.BoundaryConeHornIso

/-- The original last vertex of the positive-dimensional last outer horn. -/
def apex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Λ[n + 2, Fin.last (n + 2)] :=
  rightVertex n ≫ horn.ι (Fin.last (n + 2)) (0 : Fin (n + 3)) (by simp)

/-- The whole original cone on one standard boundary face, inside the actual outer horn. -/
def faceCone (n : ℕ) (j : Fin (n + 2)) :
    (Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ Λ[n + 2, Fin.last (n + 2)] :=
  (joinStdSimplexIso n 0).hom ≫ horn.ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j)

/-- The original apex retains its literal last-vertex image in the standard simplex. -/
theorem apex_standard (n : ℕ) :
    apex.{u} n ≫ (horn (n + 2) (Fin.last (n + 2))).ι = rightVertex (n + 1) := by
  rw [apex, Category.assoc, horn.ι_ι]
  exact rightVertex_comp_δ_castSucc (0 : Fin (n + 2))

/-- Every coned boundary face has the identical original horn apex. -/
theorem faceCone_apex (n : ℕ) (j : Fin (n + 2)) :
    joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ faceCone n j = apex n := by
  apply (cancel_mono (horn (n + 2) (Fin.last (n + 2))).ι).mp
  rw [faceCone, Category.assoc, Category.assoc, horn.ι_ι, apex_standard]
  exact rightVertex_comp_δ_castSucc j

/-- The whole original coned face classified as a map into the actual horn over-slice. -/
def faceSlice (n : ℕ) (j : Fin (n + 2)) :
    (Δ[n] : SSet.{u}) ⟶ sliceOver (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) :=
  (sliceOver.homEquiv (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) Δ[n]).symm
    ⟨faceCone n j, faceCone_apex n j⟩

/-- The original over-slice readback retains that complete coned face. -/
theorem faceSlice_read (n : ℕ) (j : Fin (n + 2)) :
    (sliceOver.homEquiv (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) Δ[n] (faceSlice n j)).val =
      faceCone n j :=
  congrArg Subtype.val ((sliceOver.homEquiv _ _ _).apply_symm_apply _)

private theorem slice_precomp {H A B : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H)
    (q : B ⟶ sliceOver H z) (i : A ⟶ B) :
    (sliceOver.homEquiv H z A (i ≫ q)).val =
      (join.map i).app Δ[0] ≫ (sliceOver.homEquiv H z B q).val := by
  simp only [sliceOver.homEquiv_apply, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- The original over-slice face maps satisfy the full standard boundary relations. -/
theorem faceSlice_compatible (n : ℕ) : boundary.IsCompatible (faceSlice.{u} n) := by
  cases n with
  | zero => trivial
  | succ n =>
    rw [boundary.isCompatible_succ_iff]
    intro j k hjk
    apply (sliceOver.homEquiv (Λ[n + 3, Fin.last (n + 3)] : SSet.{u}) (apex (n + 1)) Δ[n]).injective
    apply Subtype.ext
    rw [slice_precomp, slice_precomp, faceSlice_read, faceSlice_read]
    dsimp only [faceCone]
    rw [← Category.assoc, ConeSimplexBoundary.join_face, Category.assoc,
      ← Category.assoc (NatTrans.app _ _), ConeSimplexBoundary.join_face, Category.assoc]
    have h := (horn.IsCompatible.of_hom (𝟙 (Λ[n + 3, Fin.last (n + 3)] : SSet.{u}))).δ_pred_comp
      j.castSucc k.castSucc (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last k) hjk
    have hp : k.castSucc.pred (Fin.ne_zero_of_lt (show j.castSucc < k.castSucc from hjk)) =
        (k.pred (Fin.ne_zero_of_lt hjk)).castSucc := by apply Fin.ext; rfl
    have hc : j.castSucc.castPred (Fin.ne_last_of_lt (show j.castSucc < k.castSucc from hjk)) =
        (j.castPred (Fin.ne_last_of_lt hjk)).castSucc := by apply Fin.ext; rfl
    simp only [Category.comp_id] at h
    rw [hp, hc] at h
    exact congrArg (fun f => (joinStdSimplexIso n 0).hom ≫ f) h

/-- Glue the original over-slice maps to the whole original standard boundary. -/
def boundarySlice (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) ⟶
    sliceOver (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) :=
  (faceSlice_compatible n).desc

/-- The canonical map from the entire original boundary cone to the actual last outer horn. -/
def toHorn (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ Λ[n + 2, Fin.last (n + 2)] :=
  (sliceOver.homEquiv (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) _ (boundarySlice n)).val

/-- The canonical map retains the identical original apex. -/
theorem toHorn_apex (n : ℕ) :
    joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ toHorn n = apex n :=
  (sliceOver.homEquiv _ _ _ (boundarySlice n)).property

/-- The canonical map retains every entire original coned face. -/
theorem toHorn_face (n : ℕ) (j : Fin (n + 2)) :
    (join.map (boundary.ι j)).app (Δ[0] : SSet.{u}) ≫ toHorn.{u} n = faceCone n j := by
  have h := congrArg (fun q =>
    (sliceOver.homEquiv (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (apex n) Δ[n] q).val)
    ((faceSlice_compatible n).ι_desc j)
  rw [slice_precomp, faceSlice_read] at h
  exact h

/-- The original reverse whole horn map uses the existing cone-face readback. -/
def fromHorn (n : ℕ) : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶
    (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) :=
  ConeBoundaryHorn.hornMap (𝟙 ((∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u})))

/-- The reverse map retains each complete original coned-face inclusion. -/
theorem fromHorn_face (n : ℕ) (j : Fin (n + 2)) :
    horn.ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j) ≫ fromHorn.{u} n =
      (joinStdSimplexIso n 0).inv ≫ (join.map (boundary.ι j)).app Δ[0] := by
  have h := ConeBoundaryHorn.hornMap_face (𝟙 ((∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}))) j
  simp only [ConeBoundaryHorn.face, Category.comp_id] at h
  exact h

/-- The reverse map retains the complete original apex inclusion. -/
theorem fromHorn_apex (n : ℕ) : apex n ≫ fromHorn n = joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] := by
  have h0 : horn.ι (Fin.last (n + 2)) (0 : Fin (n + 3)) (by simp) ≫ fromHorn.{u} n =
      (joinStdSimplexIso n 0).inv ≫ (join.map (boundary.ι (0 : Fin (n + 2)))).app Δ[0] :=
    fromHorn_face n (0 : Fin (n + 2))
  rw [apex, Category.assoc, h0]
  dsimp only [rightVertex]
  rw [Category.assoc, Iso.hom_inv_id_assoc, joinInr_comp_map]

/-- The whole coned boundary round trip is the original identity map. -/
theorem to_from (n : ℕ) : toHorn.{u} n ≫ fromHorn n = 𝟙 _ := by
  apply ConeSimplexBoundary.cone_hom_ext
  · rw [← Category.assoc, toHorn_apex, fromHorn_apex, Category.comp_id]
  · intro j
    rw [← Category.assoc, toHorn_face, faceCone, Category.assoc, fromHorn_face,
      Iso.hom_inv_id_assoc, Category.comp_id]

/-- The whole outer horn round trip is the original identity map. -/
theorem from_to (n : ℕ) : fromHorn.{u} n ≫ toHorn n = 𝟙 _ := by
  apply horn.hom_ext'
  intro j hj
  obtain ⟨i, rfl⟩ := j.eq_castSucc_of_ne_last hj
  rw [← Category.assoc, fromHorn_face, Category.assoc, toHorn_face, faceCone,
    Iso.inv_hom_id_assoc, Category.comp_id]

/-- The actual positive-dimensional boundary-cone/last-horn isomorphism retains both whole maps. -/
def iso (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ≅ Λ[n + 2, Fin.last (n + 2)] where
  hom := toHorn n
  inv := fromHorn n
  hom_inv_id := to_from n
  inv_hom_id := from_to n

/-- The canonical horn map has the entire original join-boundary inclusion as its standard-simplex image. -/
theorem toHorn_standard (n : ℕ) :
    toHorn.{u} n ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      (join.map (boundary (n + 1)).ι).app Δ[0] ≫ (joinStdSimplexIso (n + 1) 0).hom := by
  apply ConeSimplexBoundary.cone_hom_ext
  · rw [← Category.assoc, toHorn_apex, apex_standard, ← Category.assoc, joinInr_comp_map]
    rfl
  · intro j
    have hl : (join.map (boundary.ι j)).app (Δ[0] : SSet.{u}) ≫
        (toHorn n ≫ (horn (n + 2) (Fin.last (n + 2))).ι) =
        (joinStdSimplexIso n 0).hom ≫ stdSimplex.δ j.castSucc := by
      rw [← Category.assoc, toHorn_face, faceCone, Category.assoc, horn.ι_ι]
    have hr : (join.map (boundary.ι j)).app (Δ[0] : SSet.{u}) ≫
        ((join.map (boundary (n + 1)).ι).app Δ[0] ≫ (joinStdSimplexIso (n + 1) 0).hom) =
        (joinStdSimplexIso n 0).hom ≫ stdSimplex.δ j.castSucc := by
      rw [← Category.assoc, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, boundary.ι_ι]
      exact ConeSimplexBoundary.join_face n j
    exact hl.trans hr.symm

/-- The empty original boundary cone is the canonical point, using the existing join unit isomorphism. -/
def emptyConeIso : (∂Δ[0] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ≅ Δ[0] :=
  (join.flip.obj (Δ[0] : SSet.{u})).mapIso JoinHorn.Internal.joinHornBoundaryZeroIso ≪≫ botJoinIso Δ[0]

/-- The original empty-cone apex is the whole inverse point map. -/
theorem emptyCone_apex : joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫ emptyConeIso.hom = 𝟙 _ := by
  dsimp only [emptyConeIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  change joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫
    (join.map JoinHorn.Internal.joinHornBoundaryZeroIso.hom).app Δ[0] ≫ (botJoinIso Δ[0]).hom = 𝟙 _
  rw [← Category.assoc, joinInr_comp_map, joinInr_bot, Iso.inv_hom_id]

/-- The inverse empty-cone isomorphism is the entire original apex inclusion. -/
theorem emptyCone_inv : emptyConeIso.{u}.inv = joinInr (∂Δ[0] : SSet.{u}) Δ[0] := by
  apply (cancel_mono emptyConeIso.hom).mp
  rw [Iso.inv_hom_id, emptyCone_apex]

/-- The single original face of the one-horn is the canonical point isomorphism. -/
def zeroHornIso : (Δ[0] : SSet.{u}) ≅ Λ[1, Fin.last 1] where
  hom := horn.ι (Fin.last 1) (0 : Fin 2) (by decide)
  inv := stdSimplex.isTerminalObj₀.from _
  hom_inv_id := stdSimplex.ext₀
  inv_hom_id := by
    apply horn.hom_ext'
    intro j hj
    have hj0 : j = 0 := by
      fin_cases j
      · rfl
      · exact (hj rfl).elim
    subst j
    rw [← Category.assoc]
    have h : (horn.ι (Fin.last 1) (0 : Fin 2) (by decide) :
        (Δ[0] : SSet.{u}) ⟶ Λ[1, Fin.last 1]) ≫ stdSimplex.isTerminalObj₀.from _ = 𝟙 _ :=
      stdSimplex.ext₀
    rw [h, Category.id_comp, Category.comp_id]

/-- The actual cone/last-horn isomorphism in every dimension, including the empty old boundary. -/
def fullIso (n : ℕ) : (∂Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ≅ Λ[n + 1, Fin.last (n + 1)] :=
  match n with
  | 0 => emptyConeIso ≪≫ zeroHornIso
  | m + 1 => iso m

/-- In every dimension the whole canonical standard-simplex map is the original join-boundary map. -/
theorem fullIso_standard (n : ℕ) :
    (fullIso.{u} n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
      (join.map (boundary n).ι).app Δ[0] ≫ (joinStdSimplexIso n 0).hom := by
  cases n with
  | zero =>
    let _ : IsIso (joinInr (∂Δ[0] : SSet.{u}) Δ[0]) := by
      rw [← emptyCone_inv]
      infer_instance
    apply (cancel_epi (joinInr (∂Δ[0] : SSet.{u}) Δ[0])).mp
    change joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫
        (emptyConeIso.hom ≫ zeroHornIso.hom) ≫ (horn 1 (Fin.last 1)).ι =
      joinInr (∂Δ[0] : SSet.{u}) Δ[0] ≫
        ((join.map (boundary 0).ι).app Δ[0] ≫ (joinStdSimplexIso 0 0).hom)
    rw [← Category.assoc, ← Category.assoc, emptyCone_apex, Category.id_comp]
    rw [← Category.assoc, joinInr_comp_map]
    exact (horn.ι_ι (Fin.last 1) 0 (by decide)).trans rightVertex_zero.symm
  | succ n => exact toHorn_standard n

/-- The actual last horn lies in the full standard boundary. -/
theorem horn_le_boundary (n : ℕ) :
    horn.{u} (n + 1) (Fin.last (n + 1)) ≤ boundary (n + 1) := by
  rw [horn_eq_iSup, boundary_eq_iSup]
  apply iSup_le
  intro j
  exact le_iSup (fun i : Fin (n + 2) => stdSimplex.face {i}ᶜ) j.1

/-- The canonical original last-horn inclusion into the entire standard boundary. -/
def hornToBoundary (n : ℕ) : (Λ[n + 1, Fin.last (n + 1)] : SSet.{u}) ⟶ ∂Δ[n + 1] :=
  Subcomplex.homOfLE (horn_le_boundary n)

/-- The inclusion is the unchanged original standard-simplex map. -/
theorem hornToBoundary_inclusion (n : ℕ) :
    hornToBoundary.{u} n ≫ (boundary (n + 1)).ι = (horn (n + 1) (Fin.last (n + 1))).ι := rfl

/-- Each nonmissing original face has the same entire boundary inclusion. -/
theorem hornFace_boundary (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    horn.ι (Fin.last (n + 1)) j hj ≫ hornToBoundary.{u} n = boundary.ι j := by
  apply (cancel_mono (boundary (n + 1)).ι).mp
  rw [Category.assoc, hornToBoundary_inclusion, horn.ι_ι, boundary.ι_ι]

/-- Joining the original standard boundary with its actual apex retains a genuine monomorphism. -/
theorem mono_join_boundary (n : ℕ) : Mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u})) := by
  have h : Mono ((fullIso.{u} n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι) := inferInstance
  have hm : Mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso n 0).hom) :=
    fullIso_standard n ▸ h
  let _ : Mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso n 0).hom) := hm
  refine ⟨fun v w hvw => ?_⟩
  apply (cancel_mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u}) ≫
    (joinStdSimplexIso n 0).hom)).mp
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (joinStdSimplexIso n 0).hom) hvw

/-- The original last vertex followed by the zero face is the native cone apex. -/
theorem lastVertex_delta_zero (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
      stdSimplex.δ (0 : Fin (n + 2)) = rightVertex.{u} n := by
  rw [rightVertex_eq]
  change stdSimplex.map _ ≫ stdSimplex.map _ = stdSimplex.map _
  rw [← CategoryTheory.Functor.map_comp]
  apply congrArg stdSimplex.map
  ext i : 3
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rw [inr'_toOrderHom_zero]
  simp [SimplexCategory.const, SimplexCategory.δ]

/-- The actual whole base of the cone is the boundary of the missing last face. -/
theorem fullIso_base_boundary (n : ℕ) :
    joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫ (fullIso n).hom ≫ hornToBoundary n =
      (boundary n).ι ≫ boundary.ι (Fin.last (n + 1)) := by
  apply (cancel_mono (boundary (n + 1)).ι).mp
  calc
    _ = joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫
        ((fullIso n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι) := by
      rw [Category.assoc, Category.assoc, hornToBoundary_inclusion]
    _ = joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫
        ((join.map (boundary n).ι).app Δ[0] ≫ (joinStdSimplexIso n 0).hom) :=
      congrArg (fun f => joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫ f) (fullIso_standard n)
    _ = (boundary n).ι ≫ stdSimplex.δ (Fin.last (n + 1)) := by
      rw [← Category.assoc, ← map_comp_joinInl, Category.assoc]
      have h : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
          stdSimplex.δ (Fin.last (n + 1)) := frontInclusion_eq n
      rw [h]
    _ = ((boundary n).ι ≫ boundary.ι (Fin.last (n + 1))) ≫ (boundary (n + 1)).ι := by
      rw [Category.assoc, boundary.ι_ι]

/-- The actual cone apex is the identical last vertex of the entire original boundary. -/
theorem fullIso_apex_boundary (n : ℕ) :
    joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ (fullIso n).hom ≫ hornToBoundary n =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ boundary.ι (0 : Fin (n + 2)) := by
  apply (cancel_mono (boundary (n + 1)).ι).mp
  calc
    _ = joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫
        ((fullIso n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι) := by
      rw [Category.assoc, Category.assoc, hornToBoundary_inclusion]
    _ = joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫
        ((join.map (boundary n).ι).app Δ[0] ≫ (joinStdSimplexIso n 0).hom) :=
      congrArg (fun f => joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ f) (fullIso_standard n)
    _ = rightVertex n := by
      rw [← Category.assoc, joinInr_comp_map]
      rfl
    _ = (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
        boundary.ι (0 : Fin (n + 2))) ≫ (boundary (n + 1)).ι := by
      rw [Category.assoc, boundary.ι_ι]
      exact (lastVertex_delta_zero n).symm

end SSet.WalkingAdjunction.BoundaryConeHornIso
