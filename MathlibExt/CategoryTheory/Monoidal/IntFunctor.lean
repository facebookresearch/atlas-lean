/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntConstruction
public import MathlibExt.CategoryTheory.Monoidal.TracedFunctor

/-!
# Functoriality of the Int construction

Trace-preserving strong symmetric monoidal functors act on crossed morphisms
using their monoidal comparison maps. This is the functorial construction
underlying Joyal–Street–Verity, Traced monoidal categories (1996), Section 4,
https://doi.org/10.1017/S0305004100074338.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
namespace IntConstruction
variable (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided]

/-- Apply a strong monoidal functor to a crossed morphism. -/
def mapCrossed {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    F.obj A ⊗ F.obj V ⟶ F.obj B ⊗ F.obj U := μ F A V ≫ F.map f ≫ δ F B U

@[simp] theorem mapCrossed_id (A U : C) :
    mapCrossed F (𝟙 (A ⊗ U)) = 𝟙 (F.obj A ⊗ F.obj U) := by
  simp [mapCrossed]

/-- Trace preservation makes the crossed-morphism map compatible with feedback composition. -/
theorem mapCrossed_compose (hF : T.Preserves S F) {A B E U V W : C}
    (f : A ⊗ V ⟶ B ⊗ U) (g : B ⊗ W ⟶ E ⊗ V) :
    mapCrossed F (compose T f g) = compose S (mapCrossed F f) (mapCrossed F g) := by
  unfold mapCrossed compose
  rw [hF]
  rw [← S.naturality]
  congr 1
  simp only [exchange, Functor.map_comp, map_whiskerLeft, map_whiskerRight,
    map_associator, map_associator_inv, Functor.map_braiding,
    whiskerLeft_comp, comp_whiskerRight, Category.assoc,
    μ_δ_assoc, whiskerLeft_μ_δ_assoc, whiskerRight_μ_δ_assoc,
    whiskerRight_μ_δ, tensorHom_id, Category.comp_id]

/-- The functor induced on Int by a trace-preserving strong symmetric monoidal functor. -/
def map (hF : T.Preserves S F) : IntConstruction T ⥤ IntConstruction S where
  obj X := ⟨F.obj X.positive, F.obj X.negative⟩
  map f := ofHom S (mapCrossed F (hom T f))
  map_id X := mapCrossed_id F X.positive X.negative
  map_comp f g := mapCrossed_compose T S F hF (hom T f) (hom T g)

end IntConstruction
end CategoryTheory
