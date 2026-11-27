/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainCoaugmentationExact
public import MathlibExt.CategoryTheory.Abelian.Injective.AugmentedExactComparisonExistence
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Augmented cochain complexes and right-derived cohomology

For an abelian category `C` with injective resolutions, a coaugmentation
quasi-isomorphism `X[0] → I` admits a coaugmentation-preserving map to
the chosen injective resolution of `X`. An additive `F : C → D` into
an abelian category then gives `Hⁿ(F(I)) → R^nF(X)`. This map is
independent of the comparison chosen and agrees with the inverse
resolution comparison when `I` itself is an injective resolution.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Let `C` be abelian with injective resolutions. For a nonnegative
cochain complex `I` and a quasi-isomorphism `ι : X[0] → I`, there is a
cochain map `a : I → I(X)` to the chosen injective resolution satisfying
`ι ≫ a = ι_(I(X))`. The terms of `I` need not be injective. -/
def augmentedResolutionComparison {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι] :
    {a : I ⟶ (injectiveResolution X).cocomplex // ι ≫ a = (injectiveResolution X).ι} := by
  let : Mono (ι.f 0) := (CochainComplex.coaugmentation_exact_and_mono ι).2
  let h := exists_augmentedExactComparison ι (injectiveResolution X).ι
    (CochainComplex.coaugmentation_exact_and_mono ι).1
    (CochainComplex.coaugmentation_exact_succ ι)
    (injectiveResolution X).injective (𝟙 X)
  exact ⟨h.choose, h.choose_spec.trans (by simp only [Functor.map_id, Category.id_comp])⟩

namespace Functor
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For a coaugmentation quasi-isomorphism `ι : X[0] → I`, mapping
a comparison into an injective resolution and taking cohomology gives
the canonical map `Hⁿ(F(I)) → R^nF(X)`. -/
def augmentedResolutionToRightDerivedHom (F : C ⥤ D) [F.Additive]
    {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι] (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n ⟶
      (F.rightDerived n).obj X :=
  HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (augmentedResolutionComparison I ι).val) n ≫
    ((injectiveResolution X).isoRightDerivedObj F n).inv

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For `ι : X[0] → I` a quasi-isomorphism, any map
`a : I → I(X)` preserving the coaugmentation computes the same map
`Hⁿ(F(I)) → R^nF(X)`: it is `Hⁿ(F(a))` followed by the inverse
injective-resolution comparison. -/
theorem augmentedResolutionToRightDerivedHom_eq (F : C ⥤ D) [F.Additive]
    {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (a : I ⟶ (injectiveResolution X).cocomplex) (ha : ι ≫ a = (injectiveResolution X).ι)
    (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom I ι n =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n ≫
      ((injectiveResolution X).isoRightDerivedObj F n).inv := by
  exact congrArg (fun q => q ≫ ((injectiveResolution X).isoRightDerivedObj F n).inv)
    (augmentedExactComparison_homologyMap_eq F ι
      (CochainComplex.coaugmentation_exact_and_mono ι).1
      (CochainComplex.coaugmentation_exact_succ ι) (injectiveResolution X).injective
      (augmentedResolutionComparison I ι).val a
      ((augmentedResolutionComparison I ι).property.trans ha.symm) n)

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For an injective resolution `J` of `X`, the augmented comparison
`Hⁿ(F(J)) → R^nF(X)` is the inverse of its canonical
right-derived resolution isomorphism. -/
theorem augmentedResolutionToRightDerivedHom_injectiveResolution
    (F : C ⥤ D) [F.Additive] {X : C} (J : InjectiveResolution X) (n : ℕ) :
    F.augmentedResolutionToRightDerivedHom J.cocomplex J.ι n =
      (J.isoRightDerivedObj F n).inv := by
  let a := InjectiveResolution.desc (𝟙 X) (injectiveResolution X) J
  have ha : J.ι ≫ a = (injectiveResolution X).ι := by
    exact (InjectiveResolution.desc_commutes (𝟙 X) (injectiveResolution X) J).trans
      (by simp only [Functor.map_id, Category.id_comp])
  rw [F.augmentedResolutionToRightDerivedHom_eq J.cocomplex J.ι a ha n]
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 X) J (injectiveResolution X) a
    (InjectiveResolution.desc_commutes_zero (𝟙 X) (injectiveResolution X) J) F n
  exact h.symm.trans (by simp only [Functor.map_id, Category.comp_id])

end Functor
end CategoryTheory
