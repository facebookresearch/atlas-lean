/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback

/-!
# Transport Left Augment

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.TransportAugment
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] (E : C ≌ D)

/-- The transported left-unit tensor word equals the image of the source tensor word with its
equivalence units and counit. -/
def LeftWordFormula {P Q R : C} {A B T N : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (e : P ⊗ Q ≅ R) : Prop :=
  letI := Monoidal.transport E
  ∀ (f : A ⟶ 𝟙_ D) (g : B ⟶ N),
    (Primitive.ofIso E eP eQ eR e).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom =
      eR.inv ≫ E.functor.map
        (e.inv ≫
          ((E.unitIso.hom.app P ≫ E.inverse.map (eP.hom ≫ f) ≫ E.unitIso.inv.app (𝟙_ C)) ⊗ₘ
            (E.unitIso.hom.app Q ≫ E.inverse.map (eQ.hom ≫ g))) ≫
          (λ_ (E.inverse.obj N)).hom) ≫ E.counitIso.hom.app N

/-- The original transported left-unit word retains both complete equivalence units and all
three input/output pair comparisons. -/
theorem left_word {P Q R : C} {A B T N : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (e : P ⊗ Q ≅ R) :
    LeftWordFormula E (N := N) eP eQ eR e := by
  let := Monoidal.transport E
  intro f g
  have hUnitor : (λ_ N).hom = E.functor.map
      ((E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj N) ≫ (λ_ (E.inverse.obj N)).hom) ≫
      E.counitIso.hom.app N := rfl
  have hTensor : (eP.hom ⊗ₘ eQ.hom) ≫ (f ⊗ₘ g) =
      (eP.hom ≫ f) ⊗ₘ (eQ.hom ≫ g) := tensorHom_comp_tensorHom _ _ _ _
  have hMappedTensor : ((eP.hom ≫ f) ⊗ₘ (eQ.hom ≫ g)) = E.functor.map
      (E.inverse.map (eP.hom ≫ f) ⊗ₘ E.inverse.map (eQ.hom ≫ g)) := rfl
  have hSource :
      (E.unitIso.hom.app P ⊗ₘ E.unitIso.hom.app Q) ≫
        (E.inverse.map (eP.hom ≫ f) ⊗ₘ E.inverse.map (eQ.hom ≫ g)) ≫
        (E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj N) ≫ (λ_ (E.inverse.obj N)).hom =
      ((E.unitIso.hom.app P ≫ E.inverse.map (eP.hom ≫ f) ≫ E.unitIso.inv.app (𝟙_ C)) ⊗ₘ
        (E.unitIso.hom.app Q ≫ E.inverse.map (eQ.hom ≫ g))) ≫
        (λ_ (E.inverse.obj N)).hom := by
    slice_lhs 1 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  calc
    _ = eR.inv ≫ E.functor.map e.inv ≫
        E.functor.map (E.unitIso.hom.app P ⊗ₘ E.unitIso.hom.app Q) ≫
        ((eP.hom ⊗ₘ eQ.hom) ≫ (f ⊗ₘ g)) ≫ (λ_ N).hom := by
      rw [Primitive.ofIso_inv]
      simp only [Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫
        E.functor.map (E.unitIso.hom.app P ⊗ₘ E.unitIso.hom.app Q) ≫
        E.functor.map (E.inverse.map (eP.hom ≫ f) ⊗ₘ E.inverse.map (eQ.hom ≫ g)) ≫
        E.functor.map ((E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj N) ≫
          (λ_ (E.inverse.obj N)).hom) ≫ E.counitIso.hom.app N := by
      rw [hTensor, hMappedTensor, hUnitor]
    _ = _ := by
      slice_lhs 2 5 =>
        rw [← E.functor.map_comp, ← E.functor.map_comp, ← E.functor.map_comp]
      rw [hSource]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.TransportAugment
