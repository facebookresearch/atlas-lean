/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionComparison

/-!
# Naturality of cohomology-to-derived augmented comparisons

Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. Any coaugmentation-preserving map from an exact
coaugmented complex into an injective resolution computes its canonical
map to `R^nF`. A map between coaugmented complexes over `f : X → Y`
gives the corresponding square with `R^nF(f)`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For a quasi-isomorphism `ι : X[0] → I`, any map
`a : I → J` to any injective resolution `J` of `X` with `ι ≫ a = ι_J`
computes `Hⁿ(F(I)) → R^nF(X)` by `Hⁿ(F(a))` followed by the inverse
comparison for `J`. -/
theorem augmentedResolutionToRightDerivedHom_eq_of_injectiveTarget
    (F : C ⥤ D) [F.Additive] {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (J : InjectiveResolution X) (a : I ⟶ J.cocomplex) (ha : ι ≫ a = J.ι) (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom I ι n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n ≫
        (J.isoRightDerivedObj F n).inv := by
  let b := InjectiveResolution.desc (𝟙 X) (injectiveResolution X) J
  have hb : J.ι ≫ b = (injectiveResolution X).ι :=
    (InjectiveResolution.desc_commutes (𝟙 X) (injectiveResolution X) J).trans
      (by simp only [Functor.map_id, Category.id_comp])
  have hab : ι ≫ (a ≫ b) = (injectiveResolution X).ι := by
    rw [← Category.assoc, ha, hb]
  rw [F.augmentedResolutionToRightDerivedHom_eq I ι (a ≫ b) hab n]
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 X) J (injectiveResolution X) b
    (InjectiveResolution.desc_commutes_zero (𝟙 X) (injectiveResolution X) J) F n
  have h' : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map b) n ≫
      ((injectiveResolution X).isoRightDerivedObj F n).inv = (J.isoRightDerivedObj F n).inv :=
    h.symm.trans (by simp only [Functor.map_id, Category.comp_id])
  let H := F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  change H.map (a ≫ b) ≫ ((injectiveResolution X).isoRightDerivedObj F n).inv =
    H.map a ≫ (J.isoRightDerivedObj F n).inv
  change H.map b ≫ ((injectiveResolution X).isoRightDerivedObj F n).inv =
    (J.isoRightDerivedObj F n).inv at h'
  exact (congrArg (fun q => q ≫ ((injectiveResolution X).isoRightDerivedObj F n).inv)
    (H.map_comp a b)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun q => H.map a ≫ q) h'))

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. Let `ι : X[0] → I`, `κ : Y[0] → J` be quasi-isomorphisms.
If `a : I → J` lies over `f : X → Y`, so `ι ≫ a = f[0] ≫ κ`,
then `Hⁿ(F(a)) ≫ comparison_J = comparison_I ≫ R^nF(f)`. -/
theorem augmentedResolutionToRightDerivedHom_naturality
    (F : C ⥤ D) [F.Additive] {X Y : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj Y ⟶ J) [QuasiIso ι] [QuasiIso κ]
    (f : X ⟶ Y) (a : I ⟶ J) (ha : ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ)
    (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n ≫
        F.augmentedResolutionToRightDerivedHom J κ n =
      F.augmentedResolutionToRightDerivedHom I ι n ≫ (F.rightDerived n).map f := by
  let rX := augmentedResolutionComparison I ι
  let rY := augmentedResolutionComparison J κ
  let b := InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)
  have h₁ : ι ≫ (a ≫ rY.val) = (CochainComplex.single₀ C).map f ≫ (injectiveResolution Y).ι := by
    rw [← Category.assoc, ha, Category.assoc, rY.property]
  have h₂ : ι ≫ (rX.val ≫ b) = (CochainComplex.single₀ C).map f ≫ (injectiveResolution Y).ι := by
    rw [← Category.assoc, rX.property]
    exact InjectiveResolution.desc_commutes f _ _
  have hH := augmentedExactComparison_homologyMap_eq F ι
    (CochainComplex.coaugmentation_exact_and_mono ι).1
    (CochainComplex.coaugmentation_exact_succ ι) (injectiveResolution Y).injective
    (a ≫ rY.val) (rX.val ≫ b) (h₁.trans h₂.symm) n
  have hN := InjectiveResolution.isoRightDerivedObj_inv_naturality
    f (injectiveResolution X) (injectiveResolution Y) b
    (InjectiveResolution.desc_commutes_zero f _ _) F n
  let H := F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  change H.map (a ≫ rY.val) = H.map (rX.val ≫ b) at hH
  change H.map a ≫ (H.map rY.val ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv) =
    (H.map rX.val ≫ ((injectiveResolution X).isoRightDerivedObj F n).inv) ≫
      (F.rightDerived n).map f
  calc
    _ = (H.map a ≫ H.map rY.val) ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv :=
      (Category.assoc _ _ _).symm
    _ = H.map (a ≫ rY.val) ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv :=
      congrArg (fun q => q ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv)
        (H.map_comp a rY.val).symm
    _ = H.map (rX.val ≫ b) ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv :=
      congrArg (fun q => q ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv) hH
    _ = (H.map rX.val ≫ H.map b) ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv :=
      congrArg (fun q => q ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv)
        (H.map_comp rX.val b)
    _ = H.map rX.val ≫ (H.map b ≫ ((injectiveResolution Y).isoRightDerivedObj F n).inv) :=
      Category.assoc _ _ _
    _ = H.map rX.val ≫ (((injectiveResolution X).isoRightDerivedObj F n).inv ≫
        (F.rightDerived n).map f) := congrArg (fun q => H.map rX.val ≫ q) hN.symm
    _ = _ := (Category.assoc _ _ _).symm

end CategoryTheory.Functor
