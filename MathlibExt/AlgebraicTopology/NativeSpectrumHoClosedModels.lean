/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeMotiveTensorModels

/-!
# Derived closed structure on the literal native spectrum homotopy category

The category is the formal localization of the actual Tau spectra at the
native stable weak maps. Tensor and internal Hom are normalized on the
actual cofibrant tensor and complete function spectrum. The original
native unit, braiding and closed counit fix their comparisons.

This is a source construction interface. It supplies no K spectrum,
motive corepresentability, or independently asserted RHom endpoint.
Sources: HSS Sections 2.2/3.1--3.4; BGT arXiv:1001.2282v4 Section 2.3.
Native license notices and revisions remain in the imported ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open NativeDerivedSpectrumModels StableSpectraInfinitySource NativeK0ComparisonModels
open NativeMotiveTensorModels
open scoped MonoidalClosed

/-- Every source object is still the original native spectrum localization object. -/
structure SpectrumHoClosedSource (S : SpectrumInfinitySource) (R : SpectrumReplacements S) where
  monoidal : MonoidalCategory (spectrumHo S)
  symmetric : letI := monoidal; SymmetricCategory (spectrumHo S)
  closed : letI := monoidal; MonoidalClosed (spectrumHo S)
  unit : letI := monoidal; (𝟙_ (spectrumHo S)) ≅ (spectrumQ S).obj sphereSpectrum
  tensor : letI := monoidal
    ∀ E F : SymmetricSpectrum, (spectrumQ S).obj E ⊗ (spectrumQ S).obj F ≅
      (spectrumQ S).obj (R.cofibrant.obj E ⊗ R.cofibrant.obj F)
  hom : letI := monoidal; letI := closed
    ∀ E F : SymmetricSpectrum,
    (ihom ((spectrumQ S).obj E)).obj ((spectrumQ S).obj F) ≅
      (spectrumQ S).obj (derivedFunctionSpectrum R E F)
  unit_normalization : letI := monoidal
    ∀ E : SymmetricSpectrum,
    unit.inv ▷ (spectrumQ S).obj E ≫ (λ_ ((spectrumQ S).obj E)).hom =
      (tensor sphereSpectrum E).hom ≫ (spectrumQ S).map ((spectrumUnitMap R).app E)
  braiding_normalization : letI := monoidal; letI := symmetric
    ∀ E F : SymmetricSpectrum,
    (β_ ((spectrumQ S).obj E) ((spectrumQ S).obj F)).hom ≫ (tensor F E).hom =
      (tensor E F).hom ≫ (spectrumQ S).map (β_ (R.cofibrant.obj E) (R.cofibrant.obj F)).hom
  evaluation_normalization : letI := monoidal; letI := closed
    ∀ E F : SymmetricSpectrum,
    (spectrumQ S).obj E ◁ (hom E F).inv ≫ (ihom.ev ((spectrumQ S).obj E)).app ((spectrumQ S).obj F) = by
      let d := derivedFunctionSpectrum R E F
      letI : IsIso ((spectrumQ S).map (R.fibrant_augmentation.app F)) :=
        (stableWeak S).Q_inverts _ (R.fibrant_weak F)
      exact (tensor E d).hom ≫ (spectrumQ S).map
        (R.cofibrant.obj E ◁ R.cofibrant_augmentation.app d ≫
          (ihom.ev (R.cofibrant.obj E)).app (R.fibrant.obj F)) ≫
        inv ((spectrumQ S).map (R.fibrant_augmentation.app F))

/-- The free-zero sphere is the original regular sphere unit, as an actual native spectrum isomorphism. -/
def sphereLevelZeroIso : level sphereSpectrum 0 ≅ (𝟙_ PointedSSet.{0}) :=
  (PointedSSet.smashPowUnitIso PointedSSet.circle (Fin 0)).symm

structure FreeZeroSphereSource where
  iso : sourceSphere ≅ sphereSpectrum
  generators : ∀ (n : SimplexCategoryᵒᵖ),
    ((SymmetricSpectrum.freeι 0 (𝟙_ PointedSSet.{0}) ≫
      (SymmetricSpectrum.evaluation 0).map iso.hom ≫ sphereLevelZeroIso.hom).right).app n
      (PointedSSet.tensorUnitSimplex n) = PointedSSet.tensorUnitSimplex n

end MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels
