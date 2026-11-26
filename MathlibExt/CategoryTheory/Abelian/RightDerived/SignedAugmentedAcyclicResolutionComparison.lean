/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolutionSignedNormalization
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolutionNaturality

/-!
# Normalized acyclic comparisons and injective targets

For an additive left-exact functor between abelian categories, correcting
an acyclic-resolution comparison by `σ_n=(-1)^(n(n+1)/2)` gives an
unsigned comparison square with any coaugmentation-preserving map to
an injective resolution. On an injective resolution, the corrected
isomorphism is its canonical right-derived comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. Multiplying the source by `σ_n=(-1)^(n(n+1)/2)` corrects the
acyclic comparison to an isomorphism `R^nF(X) ≅ Hⁿ(F(I))`
normalized to agree with injective-resolution comparisons. -/
def rightDerivedNormalizedAcyclicComparison (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X : C} (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    [QuasiIso ι] (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) (n : ℕ) :
    (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n :=
  ((F.rightDerived n).acyclicResolutionNormalizationIso n).app X ≪≫
    F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. For an injective resolution `J` of `Y` and a map `a : I → J`
over `f : X → Y`, the forward acyclic comparison followed by
`Hⁿ(F(a))` equals `σ_n` times `R^nF(f)` followed by the canonical
comparison for `J`, where `σ_n=(-1)^(n(n+1)/2)`. -/
theorem rightDerivedAcyclicComparison_toInjective_signed (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X Y : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q)))
    (J : InjectiveResolution Y) (f : X ⟶ Y) (a : I ⟶ J.cocomplex)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n =
    ProjectiveResolution.acyclicResolutionNormalizationSign n •
      ((F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom) := by
  let hJ := InjectiveResolution.normalizationInjectiveTerms_acyclic J F
  have hn := F.rightDerivedObjIsoHomologyOfAcyclicResolution_naturality
    I J.cocomplex ι J.ι hI hJ f a h n
  have hs := InjectiveResolution.normalizationAcyclicInjective_hom J F hJ n
  exact hn.symm.trans
    ((congrArg (fun t => (F.rightDerived n).map f ≫ t) hs).trans
      (comp_zsmul _ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. For an injective resolution `J` of `Y` and a map `a : I → J`
over `f : X → Y`, the normalized comparison followed by `Hⁿ(F(a))`
equals `R^nF(f)` followed by the canonical comparison for `J`. -/
theorem rightDerivedNormalizedAcyclicComparison_toInjective (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X Y : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q)))
    (J : InjectiveResolution Y) (f : X ⟶ Y) (a : I ⟶ J.cocomplex)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (F.rightDerivedNormalizedAcyclicComparison I ι hI n).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n =
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom := by
  have hs := F.rightDerivedAcyclicComparison_toInjective_signed I ι hI J f a h n
  change ((ProjectiveResolution.acyclicResolutionNormalizationSign n •
    𝟙 ((F.rightDerived n).obj X)) ≫
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom) ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n = _
  rw [zsmul_comp, Category.id_comp, zsmul_comp, hs, smul_smul,
    ProjectiveResolution.acyclicResolutionNormalizationSign_mul_self, one_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive and preserving finite limits, and `J` an injective
resolution of `X` with all positive right-derived term values zero.
The forward normalized acyclic comparison on `J` is the forward
canonical injective-resolution comparison. -/
theorem rightDerivedNormalizedAcyclicComparison_injective_hom (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C} (J : InjectiveResolution X)
    (hJ : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (J.cocomplex.X q))) (n : ℕ) :
    (F.rightDerivedNormalizedAcyclicComparison J.cocomplex J.ι hJ n).hom =
      (J.isoRightDerivedObj F n).hom := by
  change (ProjectiveResolution.acyclicResolutionNormalizationSign n •
    𝟙 ((F.rightDerived n).obj X)) ≫
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution J.cocomplex J.ι hJ n).hom = _
  rw [InjectiveResolution.normalizationAcyclicInjective_hom, zsmul_comp, comp_zsmul,
    Category.id_comp, smul_smul,
    ProjectiveResolution.acyclicResolutionNormalizationSign_mul_self, one_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive and preserving finite limits, and `J` an injective
resolution of `X` with all positive right-derived term values zero.
Its normalized acyclic isomorphism equals its canonical
injective-resolution isomorphism in every degree. -/
theorem rightDerivedNormalizedAcyclicComparison_injective (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] {X : C} (J : InjectiveResolution X)
    (hJ : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (J.cocomplex.X q))) (n : ℕ) :
    F.rightDerivedNormalizedAcyclicComparison J.cocomplex J.ι hJ n =
      J.isoRightDerivedObj F n := by
  apply Iso.ext
  exact F.rightDerivedNormalizedAcyclicComparison_injective_hom J hJ n

end CategoryTheory.Functor
