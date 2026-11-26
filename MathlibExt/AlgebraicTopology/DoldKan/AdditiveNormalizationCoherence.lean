/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization

/-!
# Coherence of the additive Moore normalization comparison

Let C,D,E be abelian categories, N their normalized Moore functors, and F : C → D, G : D → E
additive functors. The canonical comparisons ν_F : F_*N(X) ≅ N(X⋙F) are coherent with identity
and composition of functors, using the chain-prolongation comparison and simplicial
associators.

They are also natural in every natural transformation between additive functors. No exactness
or kernel-preservation condition on those functors is imposed, and all category universes may
be independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.DoldKan

universe uC vC uD vD uE vE

namespace AlgebraicTopology.NormalizedQuotient

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]

private theorem alternatingTransport_id (X : SimplicialObject C) :
    (alternatingFaceMapComplexCompMapHomologicalComplexIso (𝟭 C)).hom.app X ≫
        (alternatingFaceMapComplex C).map (Functor.rightUnitor X).hom =
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.down ℕ)).hom.app
        ((alternatingFaceMapComplex C).obj X) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]

/-- Let C be abelian and X a simplicial object of C. The forward normalization map ν_Id : Id_*N(X)
→ N(X⋙Id) followed by N of the simplicial right-unitor X⋙Id≅X equals the forward chain
identity-prolongation comparison at N(X). This fixes the identity coherence morphism. -/
theorem mooreCompMapIso_id_hom (X : SimplicialObject C) :
    (((mooreCompMapIso (𝟭 C)).app X)).hom ≫
        (normalizedMooreComplex C).map (Functor.rightUnitor X).hom =
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.down ℕ)).hom.app
        ((normalizedMooreComplex C).obj X) := by
  apply (cancel_mono (inclusionOfMooreComplexMap X)).1
  calc
    _ = (((mooreCompMapIso (𝟭 C)).app X)).hom ≫
        ((normalizedMooreComplex C).map (Functor.rightUnitor X).hom ≫
          inclusionOfMooreComplexMap X) := Category.assoc _ _ _
    _ = (((mooreCompMapIso (𝟭 C)).app X)).hom ≫
        (inclusionOfMooreComplexMap (X ⋙ 𝟭 C) ≫
          (alternatingFaceMapComplex C).map (Functor.rightUnitor X).hom) := by
      exact congrArg (fun z => (((mooreCompMapIso (𝟭 C)).app X)).hom ≫ z)
        ((inclusionOfMooreComplex C).naturality (Functor.rightUnitor X).hom)
    _ = (((𝟭 C).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso (𝟭 C)).hom.app X) ≫
          (alternatingFaceMapComplex C).map (Functor.rightUnitor X).hom := by
      have hIncl := mooreCompMapIso_hom_inclusion (𝟭 C) X
      change ((mooreCompMapIso (𝟭 C)).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ 𝟭 C) =
        ((𝟭 C).mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso (𝟭 C)).hom.app X at hIncl
      rw [← Category.assoc, hIncl]
    _ = ((𝟭 C).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap X) ≫
        (Functor.mapHomologicalComplexIdIso C (ComplexShape.down ℕ)).hom.app
          ((alternatingFaceMapComplex C).obj X) := by
      rw [Category.assoc, alternatingTransport_id]
    _ = _ := (Functor.mapHomologicalComplexIdIso C (ComplexShape.down ℕ)).hom.naturality
      (inclusionOfMooreComplexMap X)

/-- For an abelian category C and simplicial object X, compose the normalization isomorphism
ν_Id(X) with N applied to the right-unitor X⋙Id≅X. The resulting isomorphism equals the chain
identity-prolongation isomorphism at N(X). -/
theorem mooreCompMapIso_id (X : SimplicialObject C) :
    ((mooreCompMapIso (𝟭 C)).app X) ≪≫
        (normalizedMooreComplex C).mapIso (Functor.rightUnitor X) =
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.down ℕ)).app
        ((normalizedMooreComplex C).obj X) := by
  apply Iso.ext
  exact mooreCompMapIso_id_hom X

variable (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]

private theorem alternatingTransport_comp (X : SimplicialObject C) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.down ℕ)).hom.app ((alternatingFaceMapComplex C).obj X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso (F ⋙ G)).hom.app X =
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (X ⋙ F) ≫
        (alternatingFaceMapComplex E).map (Functor.associator X F G).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  change (𝟙 _) ≫ 𝟙 _ = G.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
  rw [G.map_id, Category.comp_id, Category.id_comp]

/-- Let F : C → D and G : D → E be additive functors between abelian categories, X a simplicial
object, ν the normalization comparisons, and Φ the chain-prolongation composition map. Then
Φ.hom≫ν_{F⋙G}(X).hom = G_*(ν_F(X).hom)≫ν_G(X⋙F).hom≫N_E(assoc(X,F,G).hom). Both maps start at
G_*F_*N_C(X), and the associator identifies (X⋙F)⋙G with X⋙(F⋙G). -/
theorem mooreCompMapIso_comp_hom (X : SimplicialObject C) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.down ℕ)).hom.app ((normalizedMooreComplex C).obj X) ≫
        (((mooreCompMapIso (F ⋙ G)).app X)).hom =
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (((mooreCompMapIso F).app X)).hom ≫
        (((mooreCompMapIso G).app (X ⋙ F))).hom ≫
        (normalizedMooreComplex E).map (Functor.associator X F G).hom := by
  let χ := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)
  have hχ := χ.hom.naturality (inclusionOfMooreComplexMap X)
  apply (cancel_mono (inclusionOfMooreComplexMap (X ⋙ F ⋙ G))).1
  calc
    _ = χ.hom.app ((normalizedMooreComplex C).obj X) ≫
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso (F ⋙ G)).hom.app X) := by
      have hIncl := mooreCompMapIso_hom_inclusion (F ⋙ G) X
      change ((mooreCompMapIso (F ⋙ G)).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ F ⋙ G) =
        ((F ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso (F ⋙ G)).hom.app X at hIncl
      rw [Category.assoc, hIncl]
    _ = ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X))) ≫
        (χ.hom.app ((alternatingFaceMapComplex C).obj X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso (F ⋙ G)).hom.app X) := by
      rw [← Category.assoc, ← hχ, Category.assoc]
      rfl
    _ = (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)) ≫
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (X ⋙ F) ≫
          (alternatingFaceMapComplex E).map (Functor.associator X F G).hom) := by
      rw [alternatingTransport_comp]
    _ = (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (X ⋙ F) ≫
          (alternatingFaceMapComplex E).map (Functor.associator X F G).hom := by
      rw [(G.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp]
      simp only [Category.assoc]
    _ = (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((((mooreCompMapIso F).app X)).hom ≫ inclusionOfMooreComplexMap (X ⋙ F)) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (X ⋙ F) ≫
        (alternatingFaceMapComplex E).map (Functor.associator X F G).hom := by
      have hIncl := mooreCompMapIso_hom_inclusion F X
      change ((mooreCompMapIso F).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ F) =
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X at hIncl
      rw [hIncl]
    _ = (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (((mooreCompMapIso F).app X)).hom ≫
        ((((mooreCompMapIso G).app (X ⋙ F))).hom ≫
          inclusionOfMooreComplexMap ((X ⋙ F) ⋙ G)) ≫
        (alternatingFaceMapComplex E).map (Functor.associator X F G).hom := by
      have hIncl := mooreCompMapIso_hom_inclusion G (X ⋙ F)
      change ((mooreCompMapIso G).app (X ⋙ F)).hom ≫ inclusionOfMooreComplexMap ((X ⋙ F) ⋙ G) =
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap (X ⋙ F)) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso G).hom.app (X ⋙ F) at hIncl
      rw [(G.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp, hIncl]
      simp only [Category.assoc]
    _ = (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (((mooreCompMapIso F).app X)).hom ≫
        (((mooreCompMapIso G).app (X ⋙ F))).hom ≫
        ((normalizedMooreComplex E).map (Functor.associator X F G).hom ≫
          inclusionOfMooreComplexMap (X ⋙ F ⋙ G)) := by
      have hIncl : (normalizedMooreComplex E).map (Functor.associator X F G).hom ≫
          inclusionOfMooreComplexMap (X ⋙ F ⋙ G) =
            inclusionOfMooreComplexMap ((X ⋙ F) ⋙ G) ≫
              (alternatingFaceMapComplex E).map (Functor.associator X F G).hom :=
        (inclusionOfMooreComplex E).naturality (Functor.associator X F G).hom
      exact (congrArg (fun z => (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((mooreCompMapIso F).app X)).hom ≫ z) (Category.assoc _ _ _)).trans
          (congrArg (fun z => (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
            (((mooreCompMapIso F).app X)).hom ≫
              (((mooreCompMapIso G).app (X ⋙ F))).hom ≫ z) hIncl.symm)
    _ = _ := by simp only [Category.assoc]

/-- For additive F : C → D and G : D → E between abelian categories and a simplicial object X, the
chain-composition isomorphism followed by ν_{F⋙G}(X) equals G_* applied to ν_F(X), followed by
ν_G(X⋙F), then N_E of the simplicial associator. This is equality of the complete chain
isomorphisms. -/
theorem mooreCompMapIso_comp (X : SimplicialObject C) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.down ℕ)).app ((normalizedMooreComplex C).obj X) ≪≫
        ((mooreCompMapIso (F ⋙ G)).app X) =
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso (((mooreCompMapIso F).app X)) ≪≫
        ((mooreCompMapIso G).app (X ⋙ F)) ≪≫
        (normalizedMooreComplex E).mapIso (Functor.associator X F G) := by
  apply Iso.ext
  exact mooreCompMapIso_comp_hom F G X

section FunctorTransformations

variable {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂)

private theorem alternatingTransport_natTrans (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app
        ((alternatingFaceMapComplex C).obj X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F₂).hom.app X =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F₁).hom.app X ≫
        (alternatingFaceMapComplex D).map (Functor.whiskerLeft X τ) := by
  apply HomologicalComplex.hom_ext
  intro n
  change τ.app _ ≫ 𝟙 _ = 𝟙 _ ≫ τ.app _
  rw [Category.comp_id, Category.id_comp]

/-- Let C,D be abelian, F₁,F₂ : C → D additive, and τ : F₁ → F₂ any natural transformation. For a
simplicial object X, τ_* at N_C(X) followed by ν_{F₂}(X).hom equals ν_{F₁}(X).hom followed by
N_D(X◁τ). No exactness hypothesis on the functors is required. -/
@[reassoc]
theorem mooreCompMapIso_natTrans (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app
        ((normalizedMooreComplex C).obj X) ≫ (((mooreCompMapIso F₂).app X)).hom =
      (((mooreCompMapIso F₁).app X)).hom ≫
        (normalizedMooreComplex D).map (Functor.whiskerLeft X τ) := by
  apply (cancel_mono (inclusionOfMooreComplexMap (X ⋙ F₂))).1
  have hτ := NatTrans.mapHomologicalComplex_naturality τ (inclusionOfMooreComplexMap X)
  calc
    _ = (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app
        ((normalizedMooreComplex C).obj X) ≫
        ((F₂.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F₂).hom.app X) := by
      have hIncl := mooreCompMapIso_hom_inclusion F₂ X
      change ((mooreCompMapIso F₂).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ F₂) =
        (F₂.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F₂).hom.app X at hIncl
      rw [Category.assoc, hIncl]
    _ = (F₁.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex C).obj X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F₂).hom.app X) := by
      rw [← Category.assoc, ← hτ, Category.assoc]
    _ = (F₁.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F₁).hom.app X ≫
          (alternatingFaceMapComplex D).map (Functor.whiskerLeft X τ)) := by
      rw [alternatingTransport_natTrans]
    _ = ((((mooreCompMapIso F₁).app X)).hom ≫ inclusionOfMooreComplexMap (X ⋙ F₁)) ≫
        (alternatingFaceMapComplex D).map (Functor.whiskerLeft X τ) := by
      have hIncl := mooreCompMapIso_hom_inclusion F₁ X
      change ((mooreCompMapIso F₁).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ F₁) =
        (F₁.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F₁).hom.app X at hIncl
      rw [hIncl, Category.assoc]
    _ = (((mooreCompMapIso F₁).app X)).hom ≫
        ((normalizedMooreComplex D).map (Functor.whiskerLeft X τ) ≫
          inclusionOfMooreComplexMap (X ⋙ F₂)) := by
      have hIncl : (normalizedMooreComplex D).map (Functor.whiskerLeft X τ) ≫
          inclusionOfMooreComplexMap (X ⋙ F₂) =
            inclusionOfMooreComplexMap (X ⋙ F₁) ≫
              (alternatingFaceMapComplex D).map (Functor.whiskerLeft X τ) :=
        (inclusionOfMooreComplex D).naturality (Functor.whiskerLeft X τ)
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => (((mooreCompMapIso F₁).app X)).hom ≫ z) hIncl.symm)
    _ = _ := (Category.assoc _ _ _).symm

end FunctorTransformations

end AlgebraicTopology.NormalizedQuotient
