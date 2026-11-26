/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits
public import MathlibExt.Algebra.Homology.FirstQuadrantEdge
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalMap
public import MathlibExt.Algebra.Homology.Functor

/-!
# Localization of first-quadrant totals and their homology

Let R be a commutative ring, S a multiplicative submonoid and
L(M)=S⁻¹M the module localization functor to S⁻¹R-modules.
For a nonnegative homological bicomplex K in ModuleCat^u(R),
localization commutes naturally with its finite-antidiagonal total:
L(Tot(K)) ≅ Tot(LK).

Since localization is exact, it also gives
L(H_n(Tot(K))) ≅ H_n(Tot(LK)) for every n≥0, naturally in K.
If the second page of the objectwise-localized bicomplex LK
vanishes in every positive horizontal degree, its zero-column
edge gives E²_(0,n)(LK) ≅ L(H_n(Tot(K))).
The concentration condition is imposed on that actual localized
bicomplex and its horizontal-filtration spectral sequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R] (S : Submonoid R)

local notation "L" => ModuleCat.localizedModuleFunctor S
local notation "c" => ComplexShape.down ℕ

/-- For a commutative ring R, a submonoid S and nonnegative
homological R-module bicomplexes, localization gives the natural
chain isomorphism S⁻¹Tot(K) ≅ Tot(S⁻¹K).
The total uses the finite antidiagonals p+q=n in each degree. -/
noncomputable abbrev localizedFirstQuadrantTotalNatIso :
    firstQuadrantMapAfterTotalFunctor L ≅
      firstQuadrantTotalAfterMapFunctor L :=
  firstQuadrantMapTotalNatIso L

/-- For a commutative ring R, a submonoid S and n≥0, the
total-homology localization functor sends a nonnegative
homological R-module bicomplex K to S⁻¹H_n(Tot(K)).
Its target category is ModuleCat^u(S⁻¹R). -/
noncomputable abbrev localizedFirstQuadrantTotalHomologyFunctor (n : ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      ModuleCat.{u} (Localization S) :=
  totalFunctor (ModuleCat.{u} R) c c c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n ⋙ L

/-- For a commutative ring R, a submonoid S and n≥0, the
objectwise-localized total-homology functor sends K to
H_n(Tot(S⁻¹K)), where K is a nonnegative homological bicomplex
in ModuleCat^u(R). -/
noncomputable abbrev localizedFirstQuadrantBicomplexTotalHomologyFunctor
    (n : ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      ModuleCat.{u} (Localization S) :=
  mapBicomplexFunctor L ⋙
    totalFunctor (ModuleCat.{u} (Localization S)) c c c ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (Localization S)) c n

/-- For a commutative ring R, a submonoid S, a nonnegative
homological R-module bicomplex K and n≥0, there is an isomorphism
S⁻¹H_n(Tot(K)) ≅ H_n(Tot(S⁻¹K)).
It combines exactness of module localization with the natural
finite-total comparison. -/
noncomputable def localizedFirstQuadrantTotalHomologyIso
    (K : HomologicalComplex₂ (ModuleCat.{u} R) c c) (n : ℕ) :
    (L).obj ((K.total c).homology n) ≅
      ((mapBicomplex L K).total c).homology n :=
  ((HomologicalComplex.mapHomologyFunctorIso n L).app
      (K.total c)).symm ≪≫
    (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (Localization S)) c n).mapIso
        (firstQuadrantMapTotalIso L K)

/-- For a commutative ring R, a submonoid S and n≥0, the
isomorphisms S⁻¹H_n(Tot(K)) ≅ H_n(Tot(S⁻¹K)) form a natural
isomorphism of functors on nonnegative homological R-module
bicomplexes. -/
noncomputable def localizedFirstQuadrantTotalHomologyNatIso (n : ℕ) :
    localizedFirstQuadrantTotalHomologyFunctor S n ≅
      localizedFirstQuadrantBicomplexTotalHomologyFunctor S n := by
  let _ : L.PreservesZeroMorphisms := inferInstance
  let _ : L.PreservesHomology := inferInstance
  let totalR : HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      ChainComplex (ModuleCat.{u} R) ℕ := totalFunctor (ModuleCat.{u} R) c c c
  let localizeComplex : ChainComplex (ModuleCat.{u} R) ℕ ⥤
      ChainComplex (ModuleCat.{u} (Localization S)) ℕ := L.mapHomologicalComplex c
  let homologyR : ChainComplex (ModuleCat.{u} R) ℕ ⥤ ModuleCat.{u} R :=
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n
  let homologyLoc : ChainComplex (ModuleCat.{u} (Localization S)) ℕ ⥤
      ModuleCat.{u} (Localization S) :=
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (Localization S)) c n
  let localizeBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      HomologicalComplex₂ (ModuleCat.{u} (Localization S)) c c := mapBicomplexFunctor L
  let totalLoc : HomologicalComplex₂ (ModuleCat.{u} (Localization S)) c c ⥤
      ChainComplex (ModuleCat.{u} (Localization S)) ℕ :=
    totalFunctor (ModuleCat.{u} (Localization S)) c c c
  let eHomology : totalR ⋙ (homologyR ⋙ L) ≅
      totalR ⋙ (localizeComplex ⋙ homologyLoc) :=
    Functor.isoWhiskerLeft totalR
      (HomologicalComplex.mapHomologyFunctorIso (c := c) n L).symm
  let eTotal : (totalR ⋙ localizeComplex) ⋙ homologyLoc ≅
      (localizeBicomplex ⋙ totalLoc) ⋙ homologyLoc :=
    Functor.isoWhiskerRight
      (show totalR ⋙ localizeComplex ≅ localizeBicomplex ⋙ totalLoc from
        firstQuadrantMapTotalNatIso L) homologyLoc
  exact eHomology ≪≫ (Functor.associator totalR localizeComplex homologyLoc).symm ≪≫
    eTotal ≪≫ Functor.associator localizeBicomplex totalLoc homologyLoc

@[simp]
theorem localizedFirstQuadrantTotalHomologyNatIso_app
    (K : HomologicalComplex₂ (ModuleCat.{u} R) c c) (n : ℕ) :
    (localizedFirstQuadrantTotalHomologyNatIso S n).app K =
      localizedFirstQuadrantTotalHomologyIso S K n :=
  rfl

/-- For a commutative ring R, a submonoid S and a nonnegative
homological R-module bicomplex K, suppose E²_(p,q)(S⁻¹K) is zero
for every p≥1 and q≥0. Then
E²_(0,n)(S⁻¹K) ≅ S⁻¹H_n(Tot(K)) for all n≥0.
The premise concerns the second page of the objectwise-localized
bicomplex, with its actual localized differentials. -/
noncomputable def localizedHorizontalSecondPageZeroColumnTotalHomologyIso
    (K : HomologicalComplex₂ (ModuleCat.{u} R) c c) (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence
        (mapBicomplex L K)).page 2).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence
        (mapBicomplex L K)).page 2).X (0, n) ≅
      (L).obj ((K.total c).homology n) :=
  horizontalSecondPageZeroColumnTotalHomologyIso
      (mapBicomplex L K) n hpos ≪≫
    (localizedFirstQuadrantTotalHomologyIso S K n).symm

end HomologicalComplex₂

end
