/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.CommaRightComparison
public import MathlibExt.CategoryTheory.CategoryBar.Functoriality

/-!
# Right-comma point naturality for the bar comparison

For `F : C ⥤ D`, the right-comma bar comparison is covariantly natural in the
point: pushing coefficients forward along `commaCoeffRMap F g` and then comparing
agrees with comparing and then pushing nerves forward along
`CostructuredArrow.map g`.

Nonclaims: no functor/natural-transformation naturality, no source or target change,
no opposites/reversal comparison, no contraction, no homotopy, no realization,
and no KQ statement.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace CategoryBar

/-- Covariant point-naturality of the right-comma bar comparison.

For fixed `F : C ⥤ D`, pushing bar coefficients forward along `commaCoeffRMap F g`
and then comparing agrees with comparing and then pushing nerves forward along
`CostructuredArrow.map g`. -/
theorem barRightComma_naturality_d
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    categoryBarMap (commaCoeffRMap F g) (𝟙 (unitCoeffL C)) ≫
        (barRightCommaSimplicialIso F d').hom =
      (barRightCommaSimplicialIso F d).hom ≫
        nerveMap (CostructuredArrow.map g) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  have hDeg : ∀ y : barObj C (commaCoeffR F d) (unitCoeffL C) n,
      barRightCommaEquiv F d' n
          (barCoeffMap (commaCoeffRMap F g) (𝟙 (unitCoeffL C)) y) =
        (nerveMap (CostructuredArrow.map g)).app (op (SimplexCategory.mk n))
          (barRightCommaEquiv F d n y) := by
    intro y
    obtain ⟨G, l, h⟩ := y
    have hBarMap : barCoeffMap (commaCoeffRMap F g) (𝟙 (unitCoeffL C))
        (⟨G, l, h⟩ : barObj C (commaCoeffR F d) (unitCoeffL C) n) =
        ⟨G, l, h ≫ g⟩ := rfl
    rw [hBarMap]
    refine Functor.ext (fun i => ?_) (fun i j f => ?_)
    · have hl : ((barRightCommaEquiv F d' n
            (⟨G, l, h ≫ g⟩ : barObj C (commaCoeffR F d') (unitCoeffL C) n)).obj
            i).left =
          (((nerveMap (CostructuredArrow.map g)).app (op (SimplexCategory.mk n))
            (barRightCommaEquiv F d n ⟨G, l, h⟩)).obj i).left := rfl
      refine CostructuredArrow.obj_ext _ _ hl ?_
      cases hl
      change F.map (eqToHom rfl) ≫ ((F.map (G.map' i.val n) ≫ h) ≫ g) =
        F.map (G.map' i.val n) ≫ (h ≫ g)
      simp only [eqToHom_refl, F.map_id, Category.id_comp]
      exact Category.assoc (F.map (G.map' i.val n)) h g
    · apply CostructuredArrow.hom_ext
      have hEq : ∀ {x y : CostructuredArrow F d'} (h : x = y),
          (eqToHom h).left = eqToHom (congrArg CostructuredArrow.left h) := by
        intro x y h
        cases h
        rfl
      rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
      change G.map f = 𝟙 _ ≫ G.map f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  exact hDeg x

end CategoryBar

end CategoryTheory
