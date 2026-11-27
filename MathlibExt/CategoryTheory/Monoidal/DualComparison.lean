/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.TracedFunctor

/-!
# Canonical dual comparisons for strong monoidal functors

A strong monoidal functor carries a chosen dual to a dual of the image. Comparing
this mapped pairing with a chosen target pairing gives the canonical dual
comparison, compatible with evaluation, coevaluation and morphisms.

The preservation statement is Etingof, Gelaki, Nikshych and Ostrik,
Tensor Categories, Exercise 2.10.6, https://math.mit.edu/~etingof/egnobookfinal.pdf.
Mathlib calls the pairing with evaluation `Y ⊗ X ⟶ 𝟙` and coevaluation
`𝟙 ⟶ X ⊗ Y` a right dual; the book calls it a left dual. No braiding is assumed.
-/

@[expose] public section
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The canonical isomorphism of named right duals preserves coevaluation. -/
@[reassoc] theorem coevaluation_comp_rightDualIso {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    p₁.coevaluation' ≫ X ◁ (rightDualIso p₁ p₂).hom = p₂.coevaluation' := by
  let a : HasRightDual X := { rightDual := Y₂, exact := p₂ }
  let b : HasRightDual X := { rightDual := Y₁, exact := p₁ }
  have h := @coevaluation_comp_rightAdjointMate C _ _ X X a b (𝟙 X)
  change p₁.coevaluation' ≫ X ◁ (rightDualIso p₁ p₂).hom =
    p₂.coevaluation' ≫ (𝟙 X) ▷ Y₂ at h
  simpa only [id_whiskerRight, Category.comp_id] using h

/-- The canonical isomorphism of named right duals preserves evaluation. -/
@[reassoc] theorem rightDualIso_comp_evaluation {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).hom ▷ X ≫ p₂.evaluation' = p₁.evaluation' := by
  let a : HasRightDual X := { rightDual := Y₂, exact := p₂ }
  let b : HasRightDual X := { rightDual := Y₁, exact := p₁ }
  have h := @rightAdjointMate_comp_evaluation C _ _ X X a b (𝟙 X)
  change (rightDualIso p₁ p₂).hom ▷ X ≫ p₂.evaluation' =
    Y₁ ◁ (𝟙 X) ≫ p₁.evaluation' at h
  simpa only [whiskerLeft_id, Category.id_comp] using h

/-- A map of right duals preserving coevaluation is the canonical comparison. -/
theorem rightDualIso_hom_unique {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) (f : Y₁ ⟶ Y₂)
    (h : p₁.coevaluation' ≫ X ◁ f = p₂.coevaluation') : f = (rightDualIso p₁ p₂).hom := by
  let _ := p₁
  have he := h.trans (coevaluation_comp_rightDualIso p₁ p₂).symm
  change η_ X Y₁ ≫ X ◁ f = η_ X Y₁ ≫ X ◁ (rightDualIso p₁ p₂).hom at he
  have hm := congrArg (tensorLeftHomEquiv (𝟙_ C) X Y₁ Y₂).symm he
  simpa only [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft,
    cancel_epi] using hm

namespace Functor
variable (F : C ⥤ D) [F.Monoidal]

/-- The image of a chosen right dual is canonically isomorphic to the chosen image dual. -/
def mapRightDualIso (X : C) [HasRightDual X] [HasRightDual (F.obj X)] :
    F.obj (Xᘁ) ≅ (F.obj X)ᘁ :=
  rightDualIso (ExactPairing.map F X (Xᘁ)) HasRightDual.exact

/-- The canonical comparison preserves the mapped coevaluation. -/
@[reassoc] theorem mapRightDualIso_coevaluation (X : C) [HasRightDual X]
    [HasRightDual (F.obj X)] :
    (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫ F.obj X ◁ (F.mapRightDualIso X).hom =
      η_ (F.obj X) ((F.obj X)ᘁ) :=
  coevaluation_comp_rightDualIso (ExactPairing.map F X (Xᘁ)) HasRightDual.exact

/-- The canonical comparison preserves the mapped evaluation. -/
@[reassoc] theorem mapRightDualIso_evaluation (X : C) [HasRightDual X]
    [HasRightDual (F.obj X)] :
    (F.mapRightDualIso X).hom ▷ F.obj X ≫ ε_ (F.obj X) ((F.obj X)ᘁ) =
      μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F :=
  rightDualIso_comp_evaluation (ExactPairing.map F X (Xᘁ)) HasRightDual.exact

/-- Coevaluation compatibility uniquely characterizes the dual comparison map. -/
theorem mapRightDualIso_hom_unique (X : C) [HasRightDual X] [HasRightDual (F.obj X)]
    (f : F.obj (Xᘁ) ⟶ (F.obj X)ᘁ)
    (h : (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫ F.obj X ◁ f =
      η_ (F.obj X) ((F.obj X)ᘁ)) : f = (F.mapRightDualIso X).hom :=
  rightDualIso_hom_unique (ExactPairing.map F X (Xᘁ)) HasRightDual.exact f h

private theorem map_coevaluation_mate {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) :
    (ExactPairing.map F Y (Yᘁ)).coevaluation' ≫ F.obj Y ◁ F.map (fᘁ) =
      (ExactPairing.map F X (Xᘁ)).coevaluation' ≫ F.map f ▷ F.obj (Xᘁ) := by
  have h := congrArg (fun k => ε F ≫ F.map k ≫ δ F Y (Xᘁ))
    (coevaluation_comp_rightAdjointMate f)
  change (ε F ≫ F.map (η_ Y (Yᘁ)) ≫ δ F Y (Yᘁ)) ≫ _ =
    (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫ _
  simpa only [Functor.map_comp, map_whiskerLeft, map_whiskerRight,
    Category.assoc, δ_μ_assoc, μ_δ, Category.comp_id] using h

/-- The dual comparison is natural for the contravariant dual maps. -/
@[reassoc] theorem mapRightDualIso_naturality {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual (F.obj X)] [HasRightDual (F.obj Y)] (f : X ⟶ Y) :
    F.map (fᘁ) ≫ (F.mapRightDualIso X).hom =
      (F.mapRightDualIso Y).hom ≫ (F.map f)ᘁ := by
  let _ := ExactPairing.map F Y (Yᘁ)
  have hx : (ExactPairing.map F X (Xᘁ)).coevaluation' ≫
      F.obj X ◁ (F.mapRightDualIso X).hom = η_ (F.obj X) ((F.obj X)ᘁ) :=
    F.mapRightDualIso_coevaluation X
  have hy : (ExactPairing.map F Y (Yᘁ)).coevaluation' ≫
      F.obj Y ◁ (F.mapRightDualIso Y).hom = η_ (F.obj Y) ((F.obj Y)ᘁ) :=
    F.mapRightDualIso_coevaluation Y
  have he : η_ (F.obj Y) (F.obj (Yᘁ)) ≫
      F.obj Y ◁ (F.map (fᘁ) ≫ (F.mapRightDualIso X).hom) =
    η_ (F.obj Y) (F.obj (Yᘁ)) ≫
      F.obj Y ◁ ((F.mapRightDualIso Y).hom ≫ (F.map f)ᘁ) := by
    change (ExactPairing.map F Y (Yᘁ)).coevaluation' ≫ _ =
      (ExactPairing.map F Y (Yᘁ)).coevaluation' ≫ _
    rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc, map_coevaluation_mate,
      Category.assoc, ← MonoidalCategory.whisker_exchange]
    rw [← Category.assoc, hx]
    rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc, hy,
      coevaluation_comp_rightAdjointMate]
  have hm := congrArg (tensorLeftHomEquiv (𝟙_ D) (F.obj Y) (F.obj (Yᘁ)) ((F.obj X)ᘁ)).symm he
  simpa only [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft, cancel_epi] using hm

local instance (X : C) [HasRightDual X] : HasRightDual ((𝟭 C).obj X) :=
  inferInstanceAs (HasRightDual X)

/-- The identity functor has the identity dual comparison. -/
@[simp] theorem mapRightDualIso_id (X : C) [HasRightDual X] :
    (𝟭 C).mapRightDualIso X = Iso.refl (Xᘁ) := by
  apply Iso.ext
  exact ((𝟭 C).mapRightDualIso_hom_unique X (𝟙 _) (by simp)).symm

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

local instance (G : D ⥤ E) (X : C) [HasRightDual (G.obj (F.obj X))] :
    HasRightDual ((F ⋙ G).obj X) := inferInstanceAs (HasRightDual (G.obj (F.obj X)))

/-- Dual comparisons compose compatibly with strong monoidal functors. -/
theorem mapRightDualIso_comp (G : D ⥤ E) [G.Monoidal] (X : C)
    [HasRightDual X] [HasRightDual (F.obj X)] [HasRightDual (G.obj (F.obj X))] :
    (F ⋙ G).mapRightDualIso X = G.mapIso (F.mapRightDualIso X) ≪≫ G.mapRightDualIso (F.obj X) := by
  apply Iso.ext
  symm
  apply (F ⋙ G).mapRightDualIso_hom_unique X
  have h := congrArg (fun k => ε G ≫ G.map k ≫ δ G (F.obj X) ((F.obj X)ᘁ))
    (F.mapRightDualIso_coevaluation X)
  simp only [Functor.map_comp, map_whiskerLeft, Category.assoc, μ_δ, Category.comp_id] at h
  change (ε (F ⋙ G) ≫ (F ⋙ G).map (η_ X (Xᘁ)) ≫ δ (F ⋙ G) X (Xᘁ)) ≫
    G.obj (F.obj X) ◁ (G.map (F.mapRightDualIso X).hom ≫ (G.mapRightDualIso (F.obj X)).hom) = _
  simp only [Functor.LaxMonoidal.comp_ε, Functor.OplaxMonoidal.comp_δ,
    Functor.comp_map, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  calc
    _ = (ε G ≫ G.map (η_ (F.obj X) ((F.obj X)ᘁ)) ≫
        δ G (F.obj X) ((F.obj X)ᘁ)) ≫
          G.obj (F.obj X) ◁ (G.mapRightDualIso (F.obj X)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ G.obj (F.obj X) ◁ (G.mapRightDualIso (F.obj X)).hom) h
    _ = _ := G.mapRightDualIso_coevaluation (F.obj X)

end Functor
end CategoryTheory
