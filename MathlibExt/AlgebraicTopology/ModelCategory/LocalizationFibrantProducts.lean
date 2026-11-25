/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationCofibrantRepresentatives
import MathlibExt.AlgebraicTopology.ModelCategory.LeftHomotopyProduct

/-!
# Original fibrant products are genuine products after model localization

The actual fundamental lemma represents every localized arrow from a
cofibrant representative. Original product lifts give existence, and
the proved projected left-homotopy criterion gives uniqueness. The
complete original cone is therefore limiting in any model localization.
No Cartesian pushout-product law or raw internal-power fibrancy is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v uH vH
open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.ModelLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]

/-- The whole original product cone projected by the actual model localization. -/
def productCone (Y Z : C) : BinaryFan (Q.obj Y) (Q.obj Z) :=
  BinaryFan.mk (Q.map (prod.fst : Y ⨯ Z ⟶ Y)) (Q.map (prod.snd : Y ⨯ Z ⟶ Z))

/-- Both actual localized product projections detect equality of original maps from a cofibrant
source. -/
theorem raw_product_hom_ext {X Y Z : C} [IsCofibrant X] [IsFibrant Y] [IsFibrant Z]
    (f g : X ⟶ Y ⨯ Z)
    (h₁ : Q.map f ≫ Q.map prod.fst = Q.map g ≫ Q.map prod.fst)
    (h₂ : Q.map f ≫ Q.map prod.snd = Q.map g ≫ Q.map prod.snd) : Q.map f = Q.map g := by
  let _ : IsFibrant (Y ⨯ Z) := isFibrant_of_fibration (prod.snd : Y ⨯ Z ⟶ Z)
  apply (LeftHomotopyRel.iff_map_eq Q X (Y ⨯ Z)).mp
  apply (LeftHomotopyRel.prod_iff f g).mpr
  constructor
  · apply (LeftHomotopyRel.iff_map_eq Q X Y).mpr
    simpa only [Functor.map_comp] using h₁
  · apply (LeftHomotopyRel.iff_map_eq Q X Z).mpr
    simpa only [Functor.map_comp] using h₂

variable (Y Z : C) [IsFibrant Y] [IsFibrant Z]

/-- Original representing arrows and their actual product lift give the complete localized product
mediator. -/
def productLift {K : H} (f : K ⟶ Q.obj Y) (g : K ⟶ Q.obj Z) : K ⟶ Q.obj (Y ⨯ Z) :=
  (cofibrantRepresentativeIso Q K).inv ≫ Q.map (prod.lift (liftToFibrant Q f) (liftToFibrant Q g))

/-- The first whole original projected product leg reads exactly the prescribed localized arrow. -/
theorem productLift_fst {K : H} (f : K ⟶ Q.obj Y) (g : K ⟶ Q.obj Z) :
    productLift Q Y Z f g ≫ Q.map (prod.fst : Y ⨯ Z ⟶ Y) = f := by
  rw [productLift, Category.assoc, ← Functor.map_comp, prod.lift_fst, liftToFibrant_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The second whole original projected product leg reads exactly the prescribed localized arrow. -/
theorem productLift_snd {K : H} (f : K ⟶ Q.obj Y) (g : K ⟶ Q.obj Z) :
    productLift Q Y Z f g ≫ Q.map (prod.snd : Y ⨯ Z ⟶ Z) = g := by
  rw [productLift, Category.assoc, ← Functor.map_comp, prod.lift_snd, liftToFibrant_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Both complete original projected product legs detect every localized mediator. -/
theorem product_hom_ext {K : H} (f g : K ⟶ Q.obj (Y ⨯ Z))
    (h₁ : f ≫ Q.map prod.fst = g ≫ Q.map prod.fst)
    (h₂ : f ≫ Q.map prod.snd = g ≫ Q.map prod.snd) : f = g := by
  let _ : IsFibrant (Y ⨯ Z) := isFibrant_of_fibration (prod.snd : Y ⨯ Z ⟶ Z)
  apply (cancel_epi (cofibrantRepresentativeIso Q K).hom).mp
  have hFirst : Q.map (liftToFibrant Q f) ≫ Q.map prod.fst =
      Q.map (liftToFibrant Q g) ≫ Q.map prod.fst := by
    rw [liftToFibrant_fac, liftToFibrant_fac, Category.assoc, Category.assoc, h₁]
  have hSecond : Q.map (liftToFibrant Q f) ≫ Q.map prod.snd =
      Q.map (liftToFibrant Q g) ≫ Q.map prod.snd := by
    rw [liftToFibrant_fac, liftToFibrant_fac, Category.assoc, Category.assoc, h₂]
  have h := raw_product_hom_ext Q (liftToFibrant Q f) (liftToFibrant Q g) hFirst hSecond
  rwa [liftToFibrant_fac, liftToFibrant_fac] at h

/-- The SAME complete original product cone is limiting in the given model localization. -/
def productIsLimit : IsLimit (productCone Q Y Z) :=
  BinaryFan.IsLimit.mk _ (fun f g => productLift Q Y Z f g)
    (fun f g => productLift_fst Q Y Z f g) (fun f g => productLift_snd Q Y Z f g)
    (fun f g m h₁ h₂ => product_hom_ext Q Y Z m (productLift Q Y Z f g)
      (h₁.trans (productLift_fst Q Y Z f g).symm) (h₂.trans (productLift_snd Q Y Z f g).symm))

end HomotopicalAlgebra.ModelLocalization
