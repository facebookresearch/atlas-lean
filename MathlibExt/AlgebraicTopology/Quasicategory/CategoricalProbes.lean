/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.HoInverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoComp

/-!
# Functor-object homotopy categories and categorical equivalences

A categorical equivalence `f : X → Y` between quasicategories induces an equivalence
between the ordinary homotopy categories of the internal-hom simplicial sets
`Fun(K, X)` and `Fun(K, Y)`, by postcomposition with `f`. The probe `K` is an arbitrary
simplicial set in the same universe as `X` and `Y`.

The comparison follows by applying internal composition to a homotopy inverse and
its two isomorphisms in functor-object homotopy categories. For this formulation of
categorical equivalence, see Stevenson, Definition 2.1.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- Fix the second argument of ordinary internal composition. -/
private def hoCompRightSlice (K : SSet.{u})
    (b : ((ihom X).obj Y).HomotopyCategory) :
    ((ihom K).obj X).HomotopyCategory ⥤ ((ihom K).obj Y).HomotopyCategory :=
  (𝟭 _).prod' ((Functor.const _).obj b) ⋙ hoComp K X Y

/-- A slice at the vertex classified by a map is actual postcomposition,
including its action on generating edge classes. -/
private theorem hoCompRightSlice_vertex (K : SSet.{u}) (φ : X ⟶ Y) :
    hoCompRightSlice K (HomotopyCategory.mk (ihomVertexEquiv X Y φ)) =
      mapHomotopyCategory ((ihom K).map φ) := by
  have hv (v : ((ihom K).obj X) _⦋0⦌) :
      (MonoidalClosed.comp K X Y).app (op ⦋0⦌)
          (v, ihomVertexEquiv X Y φ) = ((ihom K).map φ).app (op ⦋0⦌) v := by
    obtain ⟨ψ, rfl⟩ := (ihomVertexEquiv K X).surjective v
    rw [comp_app_zero_ihomVertexEquiv, ihomVertexEquiv_ihom_map]
  have he {a b : ((ihom K).obj X) _⦋0⦌} (e : Edge a b) :
      (MonoidalClosed.comp K X Y).app (op ⦋1⦌)
          (e.edge, (Edge.id (ihomVertexEquiv X Y φ)).edge) =
        ((ihom K).map φ).app (op ⦋1⦌) e.edge := by
    have hθ : (ρ_ ((ihom K).obj X)).inv ≫
        (((ihom K).obj X) ◁ MonoidalClosed.curry' φ) ≫
          MonoidalClosed.comp K X Y = (ihom K).map φ := by
      rw [MonoidalClosed.whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]
    rw [← hθ]
    rfl
  apply Truncated.HomotopyCategory.functor_ext
    (fun v => congrArg HomotopyCategory.mk (hv v))
  intro a b ε
  let e : Edge a b := Edge.ofTruncated (X := (ihom K).obj X) ε
  have transport {a₁ a₂ b₁ b₂ : ((ihom K).obj Y) _⦋0⦌}
      {e₁ : Edge a₁ b₁} {e₂ : Edge a₂ b₂}
      (ha : a₁ = a₂) (hb : b₁ = b₂) (h : e₁.edge = e₂.edge) :
      HomotopyCategory.homMk e₁ =
        eqToHom (congrArg HomotopyCategory.mk ha) ≫ HomotopyCategory.homMk e₂ ≫
          eqToHom (congrArg HomotopyCategory.mk hb).symm := by
    subst ha
    subst hb
    rw [Edge.ext h]
    simp
  exact transport (hv a) (hv b) (he e)

/-- An isomorphism of second arguments gives a genuine natural
isomorphism of slices, by functoriality on the product category. -/
private def hoCompRightSliceIso (K : SSet.{u})
    {b₁ b₂ : ((ihom X).obj Y).HomotopyCategory} (α : b₁ ≅ b₂) :
    hoCompRightSlice K b₁ ≅ hoCompRightSlice K b₂ :=
  NatIso.ofComponents (fun a => (hoComp K X Y).mapIso (Iso.prod (Iso.refl a) α))
    (fun φ => by
      simp only [hoCompRightSlice, Functor.comp_obj, Functor.prod'_obj,
        Functor.const_obj_obj, Functor.id_obj, Functor.comp_map, Functor.prod'_map,
        Functor.const_obj_map, Functor.id_map, Functor.mapIso_hom, Iso.prod_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Prod.ext <;> simp)

/-- Both inverse isomorphisms induce inverse natural isomorphisms for
postcomposition on an arbitrary probe. -/
private theorem isEquivalence_ihomMap_of_hasHoInverse
    (h : HasHoInverse f) (K : SSet.{u}) :
    (mapHomotopyCategory ((ihom K).map f)).IsEquivalence := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  have hcomp {A B C : SSet.{u}} (a : A ⟶ B) (b : B ⟶ C) :
      mapHomotopyCategory ((ihom K).map (a ≫ b)) =
        mapHomotopyCategory ((ihom K).map a) ⋙
          mapHomotopyCategory ((ihom K).map b) := by
    rw [(ihom K).map_comp]
    change (hoFunctor.map (_ ≫ _)).toFunctor = _
    rw [hoFunctor.map_comp]
    rfl
  have hid (A : SSet.{u}) :
      mapHomotopyCategory ((ihom K).map (𝟙 A)) =
        𝟭 (((ihom K).obj A).HomotopyCategory) := by
    rw [(ihom K).map_id]
    change (hoFunctor.map (𝟙 _)).toFunctor = _
    rw [hoFunctor.map_id]
    rfl
  have η := hoCompRightSliceIso K α
  have ε := hoCompRightSliceIso K β
  rw [hoCompRightSlice_vertex, hoCompRightSlice_vertex, hcomp, hid] at η ε
  exact Functor.IsEquivalence.mk' (mapHomotopyCategory ((ihom K).map g)) η.symm ε

/--
For quasicategories `X` and `Y` and a categorical equivalence `f : X → Y`,
postcomposition induces an equivalence
`h Fun(K, X) ⥤ h Fun(K, Y)` for every simplicial probe `K` in the same universe.
-/
theorem categoricalEquivalences.isEquivalence_mapHomotopyCategory_ihomMap
    [Quasicategory X] [Quasicategory Y]
    (hf : categoricalEquivalences f) (K : SSet.{u}) :
    (mapHomotopyCategory ((ihom K).map f)).IsEquivalence :=
  isEquivalence_ihomMap_of_hasHoInverse hf.hasHoInverse K

end SSet
