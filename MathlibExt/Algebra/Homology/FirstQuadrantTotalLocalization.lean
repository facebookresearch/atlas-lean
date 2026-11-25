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
# Localizing first-quadrant total complexes

Module localization commutes naturally with first-quadrant totalization.
Since localization is exact, it also commutes with the homology of those
total complexes.  The chain comparison is the generic finite-coproduct
comparison, and the homology comparison additionally uses the standard
exact-functor homology isomorphism.

This file is generic infrastructure.  In particular, it does not assert that
any particular Bousfield--Kan bicomplex carries a compatible module action.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R] (S : Submonoid R)

local notation "L" => ModuleCat.localizedModuleFunctor S
local notation "c" => ComplexShape.down ℕ

/-- Localization commutes naturally with the total complex of a
first-quadrant module-valued bicomplex. -/
noncomputable abbrev localizedFirstQuadrantTotalNatIso :
    firstQuadrantMapAfterTotalFunctor L ≅
      firstQuadrantTotalAfterMapFunctor L :=
  firstQuadrantMapTotalNatIso L

/-- Localization of total homology, as a functor of a first-quadrant
bicomplex. -/
noncomputable abbrev localizedFirstQuadrantTotalHomologyFunctor (n : ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      ModuleCat.{u} (Localization S) :=
  totalFunctor (ModuleCat.{u} R) c c c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n ⋙ L

/-- Homology of the totalized objectwise localization, as a functor of a
first-quadrant bicomplex. -/
noncomputable abbrev localizedFirstQuadrantBicomplexTotalHomologyFunctor
    (n : ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) c c ⥤
      ModuleCat.{u} (Localization S) :=
  mapBicomplexFunctor L ⋙
    totalFunctor (ModuleCat.{u} (Localization S)) c c c ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (Localization S)) c n

/-- Localization of total homology is the homology of the totalized
objectwise-localized bicomplex. -/
noncomputable def localizedFirstQuadrantTotalHomologyIso
    (K : HomologicalComplex₂ (ModuleCat.{u} R) c c) (n : ℕ) :
    (L).obj ((K.total c).homology n) ≅
      ((mapBicomplex L K).total c).homology n :=
  ((HomologicalComplex.mapHomologyFunctorIso n L).app
      (K.total c)).symm ≪≫
    (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (Localization S)) c n).mapIso
        (firstQuadrantMapTotalIso L K)

/-- Natural form of the localized total-homology comparison. -/
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

/-- If the second page of the objectwise-localized bicomplex is concentrated
in horizontal degree zero, its surviving edge is the localization of the
original total homology.

The concentration hypothesis concerns the actual mapped bicomplex, not only
an abstract localization of the original second-page objects. -/
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
