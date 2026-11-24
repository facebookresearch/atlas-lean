/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice

/-!
# Tests for general join slices

Consumer checks for join slices under arbitrary simplicial diagrams, their
whole-map descriptions, projection, postcomposition and restriction laws, and
the structured fixed-factor join and division functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.GeneralJoinSliceTest

variable {K₀ K X Y Z A B : SSet.{u}}
variable (f : K ⟶ X) (i : K₀ ⟶ K)

/-! The slice objects retain the full fixed diagram. -/

example : SSet.{u} := SSet.sliceUnder X f

example : SSet.{u} := SSet.sliceOver X f

example (n : ℕ) :
    (SSet.sliceUnder X f).obj (op ⦋n⦌) ≃
      { g : K ⋆ Δ[n] ⟶ X // SSet.joinInl K Δ[n] ≫ g = f } :=
  SSet.sliceUnder.simplexEquiv X f n

example (n : ℕ) :
    (SSet.sliceOver X f).obj (op ⦋n⦌) ≃
      { g : Δ[n] ⋆ K ⟶ X // SSet.joinInr Δ[n] K ≫ g = f } :=
  SSet.sliceOver.simplexEquiv X f n

example {n : SimplexCategoryᵒᵖ} (g : (SSet.sliceUnder X f).obj n) :
    SSet.joinInl K (SSet.stdSimplex.obj n.unop) ≫ g.1 = f :=
  SSet.sliceUnder.condition X f g

example {n : SimplexCategoryᵒᵖ} (g : (SSet.sliceOver X f).obj n) :
    SSet.joinInr (SSet.stdSimplex.obj n.unop) K ≫ g.1 = f :=
  SSet.sliceOver.condition X f g

/-! Projections and functoriality expose their characteristic equations. -/

example : SSet.sliceUnder X f ⟶ X := SSet.sliceUnder.proj X f

example : SSet.sliceOver X f ⟶ X := SSet.sliceOver.proj X f

example (p : X ⟶ Y) :
    SSet.sliceUnder.map X f p ≫ SSet.sliceUnder.proj Y (f ≫ p) =
      SSet.sliceUnder.proj X f ≫ p :=
  SSet.sliceUnder.map_proj X f p

example (p : X ⟶ Y) :
    SSet.sliceOver.map X f p ≫ SSet.sliceOver.proj Y (f ≫ p) =
      SSet.sliceOver.proj X f ≫ p :=
  SSet.sliceOver.map_proj X f p

example : SSet.sliceUnder.map X f (𝟙 X) = 𝟙 (SSet.sliceUnder X f) :=
  SSet.sliceUnder.map_id X f

example (p : X ⟶ Y) (q : Y ⟶ Z) :
    SSet.sliceOver.map X f (p ≫ q) =
      SSet.sliceOver.map X f p ≫ SSet.sliceOver.map Y (f ≫ p) q :=
  SSet.sliceOver.map_comp X f p q

/-! Restriction changes the fixed diagram and commutes with projection and
postcomposition. -/

example : SSet.sliceUnder X f ⟶ SSet.sliceUnder X (i ≫ f) :=
  SSet.sliceUnder.restrict X f i

example : SSet.sliceOver X f ⟶ SSet.sliceOver X (i ≫ f) :=
  SSet.sliceOver.restrict X f i

example :
    SSet.sliceUnder.restrict X f i ≫ SSet.sliceUnder.proj X (i ≫ f) =
      SSet.sliceUnder.proj X f :=
  SSet.sliceUnder.restrict_proj X f i

example :
    SSet.sliceOver.restrict X f i ≫ SSet.sliceOver.proj X (i ≫ f) =
      SSet.sliceOver.proj X f :=
  SSet.sliceOver.restrict_proj X f i

example (p : X ⟶ Y) :
    SSet.sliceUnder.restrict X f i ≫
        SSet.sliceUnder.map X (i ≫ f) p =
      SSet.sliceUnder.map X f p ≫
        SSet.sliceUnder.restrict Y (f ≫ p) i :=
  SSet.sliceUnder.restrict_map X f i p

example (p : X ⟶ Y) :
    SSet.sliceOver.restrict X f i ≫
        SSet.sliceOver.map X (i ≫ f) p =
      SSet.sliceOver.map X f p ≫
        SSet.sliceOver.restrict Y (f ≫ p) i :=
  SSet.sliceOver.restrict_map X f i p

/-! Fixed-factor joins land in the structured under-category. -/

example : SSet.{u} ⥤ Under K := SSet.joinUnder K

example : SSet.{u} ⥤ Under K := SSet.joinOver K

example : ((SSet.joinUnder K).obj A).hom = SSet.joinInl K A :=
  SSet.joinUnder_obj_hom K A

example : ((SSet.joinOver K).obj A).hom = SSet.joinInr A K :=
  SSet.joinOver_obj_hom K A

example (a : A ⟶ B) :
    ((SSet.joinUnder K).map a).right = (SSet.join.obj K).map a :=
  SSet.joinUnder_map_right K a

example (a : A ⟶ B) :
    ((SSet.joinOver K).map a).right = (SSet.join.map a).app K :=
  SSet.joinOver_map_right K a

/-! Join-division is functorial on structured targets. -/

example : Under K ⥤ SSet.{u} := SSet.joinLeftDivision K

example : Under K ⥤ SSet.{u} := SSet.joinRightDivision K

example {P Q : Under K} (q : P ⟶ Q) :
    SSet.sliceUnder P.right P.hom ⟶ SSet.sliceUnder Q.right Q.hom :=
  SSet.sliceUnder.mapUnder q

example {P Q : Under K} (q : P ⟶ Q) :
    SSet.sliceOver P.right P.hom ⟶ SSet.sliceOver Q.right Q.hom :=
  SSet.sliceOver.mapUnder q

example {P Q : Under K} (q : P ⟶ Q)
    {n : SimplexCategoryᵒᵖ}
    (g : (SSet.sliceUnder P.right P.hom).obj n) :
    ((SSet.sliceUnder.mapUnder q).app n g).1 = g.1 ≫ q.right :=
  SSet.sliceUnder.mapUnder_app_val q g

example {P Q : Under K} (q : P ⟶ Q)
    {n : SimplexCategoryᵒᵖ}
    (g : (SSet.sliceOver P.right P.hom).obj n) :
    ((SSet.sliceOver.mapUnder q).app n g).1 = g.1 ≫ q.right :=
  SSet.sliceOver.mapUnder_app_val q g

end MathlibExtTest.AlgebraicTopology.SimplicialSet.GeneralJoinSliceTest

end
