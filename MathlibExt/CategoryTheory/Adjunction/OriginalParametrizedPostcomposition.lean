/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Whole original parameterized adjunction postcomposition

Composing the actual left functors with a supplied left adjoint retains
the original parameterized scalar maps. Both complete original Hom
bijections and their scalar naturality are used directly.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.ParametrizedAdjunction.OriginalPostcomposition

variable {S : Type u₁} {C : Type u₂} {D : Type u₃} {E : Type u₄}
variable [Category.{v₁} S] [Category.{v₂} C] [Category.{v₃} D] [Category.{v₄} E]
variable {F : S ⥤ C ⥤ D} {G : Sᵒᵖ ⥤ D ⥤ C}
variable {L : D ⥤ E} {R : E ⥤ D}

/-- The complete original left bifunctor is postcomposed with the actual left adjoint. -/
def left : S ⥤ C ⥤ E := F ⋙ (Functor.whiskeringRight C D E).obj L

/-- The complete original right bifunctor is precomposed with the actual right adjoint. -/
def right : Sᵒᵖ ⥤ E ⥤ C := G ⋙ (Functor.whiskeringLeft E D C).obj R

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual entire original parameterized adjunction is retained under complete
adjunction composition. -/
def adjunction (adj₂ : F ⊣₂ G) (adj : L ⊣ R) : left (F := F) (L := L) ⊣₂ right (G := G) (R := R) :=
  ParametrizedAdjunction.mk' (fun K => (adj₂.adj K).comp adj) (fun {K M} i {A B} f => by
    simp only [Adjunction.comp_homEquiv]
    change (adj₂.adj K).homEquiv A (R.obj B)
        (adj.homEquiv _ B (L.map ((F.map i).app A) ≫ f)) =
      (adj₂.adj M).homEquiv A (R.obj B) (adj.homEquiv _ B f) ≫
        ((G.map i.op).app (R.obj B))
    rw [adj.homEquiv_naturality_left]
    exact adj₂.homEquiv_naturality_one i (adj.homEquiv _ B f))

end CategoryTheory.ParametrizedAdjunction.OriginalPostcomposition
