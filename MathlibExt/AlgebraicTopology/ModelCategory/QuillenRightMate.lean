/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Weak equivalence of the actual right adjunction mate

The original adjunct functions identify postcomposition by the native
right mate with precomposition by the original left component. The
existing ordinary Ho Hom equivalences carry this whole equation to
localization. The two right-adjoint objects then construct an inverse
of the localized mate. Weak detection returns the original weak map.
Only those two source objects need cofibrancy.
-/

@[expose] public section

noncomputable section

universe u₀ u₁ v₀ v₁

open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.QuillenRightMate

variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
  {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C} (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)

private theorem adjunct_mate (α : L₀ ⟶ L₁) {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    adj₀.homEquiv X Y (α.app X ≫ f) =
      adj₁.homEquiv X Y f ≫ (conjugateEquiv adj₁ adj₀ α).app Y := by
  let β := conjugateEquiv adj₁ adj₀ α
  have hunit := unit_conjugateEquiv adj₁ adj₀ α X
  calc
    adj₀.homEquiv X Y (α.app X ≫ f) = adj₀.unit.app X ≫ R₀.map (α.app X) ≫ R₀.map f := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
    _ = (adj₀.unit.app X ≫ R₀.map (α.app X)) ≫ R₀.map f := (Category.assoc _ _ _).symm
    _ = (adj₁.unit.app X ≫ β.app (L₁.obj X)) ≫ R₀.map f := by rw [hunit]
    _ = adj₁.unit.app X ≫ β.app (L₁.obj X) ≫ R₀.map f := Category.assoc _ _ _
    _ = adj₁.unit.app X ≫ R₁.map f ≫ β.app Y := by rw [β.naturality f]
    _ = (adj₁.unit.app X ≫ R₁.map f) ≫ β.app Y := (Category.assoc _ _ _).symm
    _ = adj₁.homEquiv X Y f ≫ β.app Y := by rw [Adjunction.homEquiv_unit]

section Model

variable [ModelCategory C] [ModelCategory D]
  [Adjunction.IsQuillenAdjunction adj₀] [Adjunction.IsQuillenAdjunction adj₁]

local notation "HC" => CategoryTheory.MorphismProperty.Q (weakEquivalences C)
local notation "HD" => CategoryTheory.MorphismProperty.Q (weakEquivalences D)

/-- The whole ordinary Ho adjunct square uses the original left component and its actual native
right mate. -/
theorem homEquiv_conjugate (α : L₀ ⟶ L₁)
    (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : (HD).obj (L₁.obj X) ⟶ (HD).obj Y) :
    QuillenOrdinaryHoHom.homEquiv adj₀ X Y ((HD).map (α.app X) ≫ f) =
      QuillenOrdinaryHoHom.homEquiv adj₁ X Y f ≫ (HC).map ((conjugateEquiv adj₁ adj₀ α).app Y) := by
  let _ : IsCofibrant (L₁.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj₁) inferInstance
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization HD (L₁.obj X) Y f
  rw [← (HD).map_comp, QuillenOrdinaryHoHom.homEquiv_map,
    QuillenOrdinaryHoHom.homEquiv_map, ← (HC).map_comp]
  exact congrArg (HC).map (adjunct_mate adj₀ adj₁ α f)

/-- A weak original left component makes postcomposition by the localized native right mate
bijective on this actual Hom set. -/
theorem bijective_postcomp_conjugate (α : L₀ ⟶ L₁)
    (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] [WeakEquivalence (α.app X)] :
    Function.Bijective (fun f : (HC).obj X ⟶ (HC).obj (R₁.obj Y) =>
      f ≫ (HC).map ((conjugateEquiv adj₁ adj₀ α).app Y)) := by
  let _ : IsIso ((HD).map (α.app X)) :=
    (weakEquivalence_iff_isIso_map_of_isLocalization HD (α.app X)).mp (mem_weakEquivalences _)
  let e₀ := QuillenOrdinaryHoHom.homEquiv adj₀ X Y
  let e₁ := QuillenOrdinaryHoHom.homEquiv adj₁ X Y
  let k := (asIso ((HD).map (α.app X))).symm.homCongr (Iso.refl ((HD).obj Y))
  let e := e₁.symm.trans (k.trans e₀)
  have he (f : (HC).obj X ⟶ (HC).obj (R₁.obj Y)) :
      e f = f ≫ (HC).map ((conjugateEquiv adj₁ adj₀ α).app Y) := by
    change e₀ ((HD).map (α.app X) ≫ e₁.symm f ≫ 𝟙 ((HD).obj Y)) = _
    rw [Category.comp_id]
    change QuillenOrdinaryHoHom.homEquiv adj₀ X Y ((HD).map (α.app X) ≫ e₁.symm f) = _
    rw [homEquiv_conjugate adj₀ adj₁ α, Equiv.apply_symm_apply]
  have hf : (fun f : (HC).obj X ⟶ (HC).obj (R₁.obj Y) =>
      f ≫ (HC).map ((conjugateEquiv adj₁ adj₀ α).app Y)) = e :=
    funext (fun f => (he f).symm)
  rw [hf]
  exact e.bijective

/-- Weakness of the two original left components at the cofibrant right-adjoint objects derives
weakness of the actual native right mate at a fibrant target. -/
theorem weakEquivalence_conjugate (α : L₀ ⟶ L₁) (Y : D) [IsFibrant Y]
    [IsCofibrant (R₀.obj Y)] [IsCofibrant (R₁.obj Y)]
    [WeakEquivalence (α.app (R₀.obj Y))] [WeakEquivalence (α.app (R₁.obj Y))] :
    WeakEquivalence ((conjugateEquiv adj₁ adj₀ α).app Y) := by
  let β := (conjugateEquiv adj₁ adj₀ α).app Y
  have h₀ := bijective_postcomp_conjugate adj₀ adj₁ α (R₀.obj Y) Y
  have h₁ := bijective_postcomp_conjugate adj₀ adj₁ α (R₁.obj Y) Y
  obtain ⟨g, hg⟩ := h₀.surjective (𝟙 _)
  change g ≫ (HC).map β = 𝟙 _ at hg
  have hβg : (HC).map β ≫ g = 𝟙 _ := by
    apply h₁.injective
    change ((HC).map β ≫ g) ≫ (HC).map β = 𝟙 _ ≫ (HC).map β
    rw [Category.assoc, hg, Category.comp_id, Category.id_comp]
  let _ : IsIso ((HC).map β) := ⟨⟨g, hβg, hg⟩⟩
  exact (weakEquivalence_iff _).mpr
    ((weakEquivalence_iff_isIso_map_of_isLocalization HC β).mpr inferInstance)

end Model

end HomotopicalAlgebra.QuillenRightMate
