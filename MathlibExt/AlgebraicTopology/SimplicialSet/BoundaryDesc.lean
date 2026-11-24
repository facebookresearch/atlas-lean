/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Descent from the faces of a standard boundary

A compatible family of maps on the codimension-one faces of a standard
simplex glues to a map from its boundary.  In dimension one the two faces are
vertices with empty intersection, so no compatibility equation is required.

The construction uses the multicoequalizer presentation of subcomplex covers
from Mathlib.  It is the standard-boundary analogue of the licensed horn
descent construction in
`Mathlib.AlgebraicTopology.SimplicialSet.HornColimits`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial
open scoped Simplicial

namespace SSet
namespace boundary

/-- Compatibility for maps on all codimension-one faces of
`boundary (n + 1)`.  The two faces of `boundary 1` have empty intersection. -/
protected def IsCompatible {n : ℕ} {X : SSet.{u}}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X)) : Prop :=
  match n with
  | 0 => True
  | m + 1 => ∀ (j k : Fin (m + 3)) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ faces j =
        stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ faces k

@[simp]
lemma isCompatible_zero_iff_true {X : SSet.{u}}
    (faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X)) :
    boundary.IsCompatible faces ↔ True :=
  Iff.rfl

@[simp]
lemma isCompatible_succ_iff {X : SSet.{u}} {n : ℕ}
    (faces : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X)) :
    boundary.IsCompatible faces ↔
      ∀ (j k : Fin (n + 3)) (hjk : j < k),
        stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ faces j =
          stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ faces k :=
  Iff.rfl

/-- The canonical inclusions of all codimension-one faces form a compatible
boundary family. -/
lemma ι_isCompatible (n : ℕ) :
    boundary.IsCompatible (fun r : Fin (n + 2) ↦ boundary.ι r) := by
  obtain _ | n := n
  · trivial
  · rw [boundary.isCompatible_succ_iff]
    intro r t hrt
    rw [← cancel_mono (boundary (n + 2)).ι, Category.assoc, Category.assoc,
      boundary.ι_ι, boundary.ι_ι]
    obtain ⟨r, rfl⟩ := r.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hrt)
    obtain ⟨t, rfl⟩ := t.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hrt)
    rw [Fin.pred_succ, Fin.castPred_castSucc,
      stdSimplex.δ_comp_δ (by grind)]

/-- The multicoequalizer presentation of a standard boundary by its
codimension-one faces. -/
lemma multicoequalizerDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (boundary.{u} n)
      (fun j : Fin (n + 1) ↦ stdSimplex.face (n := n) {j}ᶜ)
      (fun j k : Fin (n + 1) ↦ stdSimplex.face (n := n) {j, k}ᶜ) where
  iSup_eq := by rw [boundary_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- The canonical boundary multicoequalizer is a colimit. -/
noncomputable def isColimit (n : ℕ) :
    IsColimit ((multicoequalizerDiagram n).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram n).isColimit'

namespace IsCompatible

variable {n : ℕ} {X : SSet.{u}}
  {faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X)}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def multicofork (hf : boundary.IsCompatible faces) :
    Multicofork ((multicoequalizerDiagram (n + 1)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X
    (fun j ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ faces j) (by
      obtain _ | n := n
      · rintro ⟨⟨a, b⟩, hab⟩
        dsimp at hab ⊢
        fin_cases a <;> fin_cases b
        all_goals simp at hab
        have hbot :
            (stdSimplex.face ({0, 1} : Finset (Fin 2))ᶜ :
              (Δ[1] : SSet.{u}).Subcomplex) = ⊥ := by
          rw [show ({0, 1} : Finset (Fin 2))ᶜ = ∅ by decide,
            stdSimplex.face_empty]
        exact ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).ofIso
          (Subcomplex.eqToIso hbot).symm).hom_ext _ _
      · rintro ⟨⟨a, b⟩, hab⟩
        dsimp at hab ⊢
        rw [stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc
              _ _ hab,
          stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc
              _ _ hab,
          hf a b hab])

/-- Glue a compatible family of codimension-one faces to a map from the
standard boundary. -/
@[no_expose]
noncomputable def desc (hf : boundary.IsCompatible faces) :
    (boundary (n + 1) : SSet.{u}) ⟶ X :=
  (boundary.isColimit (n + 1)).desc hf.multicofork

/-- Restricting the glued map to face `j` recovers the given face map. -/
@[reassoc (attr := simp)]
lemma ι_desc (hf : boundary.IsCompatible faces) (j : Fin (n + 2)) :
    boundary.ι j ≫ hf.desc = faces j := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).inv]
  rw [← Category.assoc, boundary.faceSingletonComplIso_inv_ι]
  simpa [desc, multicofork, boundary.faceι] using!
    (boundary.isColimit (n + 1)).fac hf.multicofork (.right j)

end IsCompatible
end boundary
end SSet

universe v

namespace SSet

private noncomputable def boundaryOneFaces (i : Fin 2) :
    (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0] :=
  if i = 0 then coprod.inl else coprod.inr

private theorem boundaryOneFaces_compatible :
    SSet.boundary.IsCompatible boundaryOneFaces.{v} := by
  change True
  trivial

/-- The original one-boundary is the actual ordered coproduct of its two zero faces. -/
@[no_expose]
noncomputable def boundaryOneIsoTwoPoints : (∂Δ[1] : SSet.{v}) ≅ Δ[0] ⨿ Δ[0] where
  hom := boundaryOneFaces_compatible.desc
  inv := coprod.desc (SSet.boundary.ι (0 : Fin 2)) (SSet.boundary.ι (1 : Fin 2))
  hom_inv_id := by
    apply SSet.boundary.hom_ext
    intro i
    rw [← Category.assoc, SSet.boundary.IsCompatible.ι_desc]
    fin_cases i <;> simp [boundaryOneFaces]
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, SSet.boundary.IsCompatible.ι_desc]
      simp [boundaryOneFaces]
    · rw [coprod.inr_desc_assoc, SSet.boundary.IsCompatible.ι_desc]
      simp [boundaryOneFaces]

private theorem boundaryOneIsoTwoPoints_inl_inv_private :
    (coprod.inl : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) ≫ boundaryOneIsoTwoPoints.inv =
      SSet.boundary.ι (0 : Fin 2) := coprod.inl_desc _ _

/-- The inverse coproduct comparison retains the entire original first face map. -/
@[reassoc]
theorem boundaryOneIsoTwoPoints_inl_inv :
    (coprod.inl : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) ≫ boundaryOneIsoTwoPoints.inv =
      SSet.boundary.ι (0 : Fin 2) := boundaryOneIsoTwoPoints_inl_inv_private

private theorem boundaryOneIsoTwoPoints_inr_inv_private :
    (coprod.inr : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) ≫ boundaryOneIsoTwoPoints.inv =
      SSet.boundary.ι (1 : Fin 2) := coprod.inr_desc _ _

/-- The inverse coproduct comparison retains the entire original second face map. -/
@[reassoc]
theorem boundaryOneIsoTwoPoints_inr_inv :
    (coprod.inr : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) ≫ boundaryOneIsoTwoPoints.inv =
      SSet.boundary.ι (1 : Fin 2) := boundaryOneIsoTwoPoints_inr_inv_private

private theorem boundaryOneIsoTwoPoints_inv_private :
    boundaryOneIsoTwoPoints.{v}.inv =
      (coprod.desc (SSet.boundary.ι (0 : Fin 2)) (SSet.boundary.ι (1 : Fin 2)) :
        ((Δ[0] : SSet.{v}) ⨿ Δ[0]) ⟶ (∂Δ[1] : SSet.{v})) := rfl

/-- The inverse of the canonical boundary comparison is the original two-face descent. -/
theorem boundaryOneIsoTwoPoints_inv :
    boundaryOneIsoTwoPoints.{v}.inv =
      (coprod.desc (SSet.boundary.ι (0 : Fin 2)) (SSet.boundary.ι (1 : Fin 2)) :
        ((Δ[0] : SSet.{v}) ⨿ Δ[0]) ⟶ (∂Δ[1] : SSet.{v})) :=
  boundaryOneIsoTwoPoints_inv_private

end SSet
