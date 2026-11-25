/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.TracedFunctor
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]

example (T : SymmetricTrace C) : T.Preserves T (𝟭 C) :=
  T.preserves_id

example (T : SymmetricTrace C) (S : SymmetricTrace D) (R : SymmetricTrace E)
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]
    (hF : T.Preserves S F) (hG : S.Preserves R G) : T.Preserves R (F ⋙ G) :=
  hF.comp hG

-- Chosen duals need not be preserved definitionally by the functor.
example [RightRigidCategory C] [RightRigidCategory D]
    (F : C ⥤ D) [F.Braided] :
    (symmetricTraceOfRigid C).Preserves (symmetricTraceOfRigid D) F :=
  SymmetricTrace.preserves_of_rigid F

-- The preservation equation includes both comparison maps; it is not a
-- statement that the raw image of a tensor morphism has the same type.
example [RightRigidCategory C] [RightRigidCategory D]
    (F : C ⥤ D) [F.Braided] {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    F.map ((symmetricTraceOfRigid C).trace f) =
      (symmetricTraceOfRigid D).trace
        (Functor.LaxMonoidal.μ F X U ≫ F.map f ≫ Functor.OplaxMonoidal.δ F Y U) :=
  SymmetricTrace.preserves_of_rigid F f

-- An image pairing exists without assuming rigidity of the target category.
example (F : C ⥤ D) [F.Monoidal] (U V : C) [ExactPairing U V] :
    ExactPairing (F.obj U) (F.obj V) := ExactPairing.map F U V

-- The image of the unit pairing satisfies an actual triangle identity.
example (F : C ⥤ D) [F.Monoidal] :
    letI := ExactPairing.map F (𝟙_ C) (𝟙_ C)
    η_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) ▷ F.obj (𝟙_ C) ≫
        (α_ _ _ _).hom ≫ F.obj (𝟙_ C) ◁ ε_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) =
      (λ_ (F.obj (𝟙_ C))).hom ≫ (ρ_ (F.obj (𝟙_ C))).inv := by
  let := ExactPairing.map F (𝟙_ C) (𝟙_ C)
  exact ExactPairing.evaluation_coevaluation _ _

open MonoidalOpposite

local instance : SymmetricCategory Cᴹᵒᵖ where
  symmetry X Y := by
    apply Quiver.Hom.unmop_inj
    exact SymmetricCategory.symmetry (unmop Y) (unmop X)

-- Reversing tensor order uses the braiding as a nontrivial comparison map.
example {X Y U V : C} [ExactPairing U V] (f : X ⊗ U ⟶ Y ⊗ U) :
    letI : ExactPairing (mop U) (mop V) := ExactPairing.map (mopFunctor C) U V
    (SymmetricTrace.traceOfPairing V f).mop =
      SymmetricTrace.traceOfPairing (mop V)
        ((β_ (mop X) (mop U)).hom ≫ f.mop ≫ (β_ (mop Y) (mop U)).inv) := by
  exact SymmetricTrace.map_traceOfPairing (mopFunctor C) f

-- In a concrete linear category the comparison really swaps the two vectors.
example (v w : Fin 2 → ℚ) :
    ((Functor.LaxMonoidal.μ (mopFunctor (FGModuleCat ℚ))
      (FGModuleCat.of ℚ (Fin 2 → ℚ)) (FGModuleCat.of ℚ (Fin 2 → ℚ))).unmop).hom.hom
        (v ⊗ₜ[ℚ] w) = w ⊗ₜ[ℚ] v := by
  rfl

-- Forgetting finite generation lands in all modules, which are not rigid.
example (X Y U : FGModuleCat ℚ) (f : X ⊗ U ⟶ Y ⊗ U) :
    let F := (ModuleCat.isFG ℚ).ι
    letI := ExactPairing.map F U (Uᘁ)
    F.map (SymmetricTrace.traceOfPairing (Uᘁ) f) =
      SymmetricTrace.traceOfPairing (F.obj (Uᘁ))
        (Functor.LaxMonoidal.μ F X U ≫ F.map f ≫ Functor.OplaxMonoidal.δ F Y U) := by
  exact SymmetricTrace.map_traceOfPairing (ModuleCat.isFG ℚ).ι f

-- Zero maps remain zero under the transported pairing, by direct reduction.
example (X Y U : FGModuleCat ℚ) :
    let F := (ModuleCat.isFG ℚ).ι
    letI := ExactPairing.map F U (Uᘁ)
    SymmetricTrace.traceOfPairing (F.obj (Uᘁ))
      (0 : F.obj X ⊗ F.obj U ⟶ F.obj Y ⊗ F.obj U) = 0 := by
  simp [SymmetricTrace.traceOfPairing]

#print axioms CategoryTheory.ExactPairing.map
#print axioms CategoryTheory.SymmetricTrace.preserves_of_rigid
