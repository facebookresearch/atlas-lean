/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
public import MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe
public import MathlibExt.AlgebraicGeometry.AffineConeAtlas
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Normalized global POT cone-image and virtual-class contracts

The coefficient field is arbitrary, including positive characteristic. The
cotangent target is relative to `Spec k`, and the class lies in absolute
rational Chow homology of locally finite-type k-schemes. No Betti realization,
integral Chow refinement or bivariant theory over an arbitrary base is asserted.

The POT is an actual global two-term complex of finite locally free sheaves,
with a cochain morphism into the overlap-normalized full cotangent model.
The dual bundle represents actual linear forms on its negative term. On a
cover by affine charts, the global source and morphism agree with the actual
POT matrix through a pure-differential-normalized cotangent truncation. The
ambient algebra is actually smooth and finitely presented, including Laurent,
localized and étale presentations; it need not be a polynomial ring. The
bundle coordinates are fixed by its universal linear form and the source
frame. The actual closed cone pulls back to the literal quotient by the kernel
of the computed Rees-atlas map. These comparisons are required bridge data;
an arbitrary closed subscheme is not declared to be an intrinsic POT cone.

The virtual class is computed from the actual generic-length fundamental
cycle and the inverse of the fixed bundle-cycle pullback. No virtual-class
operator is supplied. This covers global, globally two-term locally free
presentations of constant ranks; general bundle stacks, intrinsic-stack Chow,
and descent from locally two-term presentations remain separate dependencies.

Source-complete ordinary global vector-bundle/virtual-normal constructions:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleOfModule.lean`,
`StacksFrontier/AlgebraicGeometry/Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean`
(Apache 2.0). Completed cotangent primitives include the canonical explicit
pure-face map and its H0/H−1 isomorphisms in
`StacksFrontier/Cotangent/NaiveComparisonChainMap.lean` and
`StacksFrontier/Cotangent/NaiveComparisonIsIso.lean`, together with arbitrary
resolution comparison in `StacksFrontier/Cotangent/ResolutionCotangentAny.lean`.
Their integration with the specified charts/presentations is explicit bridge
data here, not a new Wanted request for those canonical results. Reference: Behrend--Fantechi,
§§2 and 4--5, https://arxiv.org/abs/alg-geom/9601010.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow
open MathlibExt.AlgebraicGeometry.RelativeCurveClasses
open MathlibExt.AlgebraicGeometry.FieldChowOperators
attribute [local instance] HasDerivedCategory.standard
open scoped TensorProduct

variable {k : Type} [Field k]

structure TwoTermModel (X : Scheme.{0}) where
  negative : X.Modules
  degreeZero : X.Modules
  negativeRank : ℕ
  zeroRank : ℕ
  negative_bundle : IsBundle negative negativeRank
  zero_bundle : IsBundle degreeZero zeroRank
  differential : negative ⟶ degreeZero

def sourceComplex {X : Scheme.{0}} (E : TwoTermModel X) : Complex X :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor X.Modules 0).map E.differential)

/-- A globally two-term locally free POT with the normalized cotangent target.
Its actual cochain map is retained for the affine comparison equations. -/
structure TwoTermPOT (X : SchemeOver k) where
  model : TwoTermModel X.left
  cotangent : CotangentNormalization X.hom
  map : sourceComplex model ⟶ cotangent.complex
  amplitude : LocallyPerfectAmplitude (sourceComplex model)
  [h0 : IsIso ((DerivedCategory.homologyFunctor X.left.Modules 0).map
    (DerivedCategory.Q.map map))]
  [hMinus : Epi ((DerivedCategory.homologyFunctor X.left.Modules (-1)).map
    (DerivedCategory.Q.map map))]
attribute [instance] TwoTermPOT.h0 TwoTermPOT.hMinus

def TwoTermPOT.toGlobal {X : SchemeOver k} (P : TwoTermPOT X) :
    MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory.PerfectObstructionTheory X.hom :=
  ⟨P.cotangent, ⟨sourceComplex P.model, P.amplitude, DerivedCategory.Q.map P.map⟩⟩

/-- Pull an actual universal linear form along a specified over-base map. -/
def pulledForm {X T V : SchemeOver k} (E : X.left.Modules) (p : V ⟶ X)
    (q : (Scheme.Modules.pullback p.left).obj E ⟶ SheafOfModules.unit V.left.ringCatSheaf)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :=
  (Scheme.Modules.pullbackCongr
    (congrArg (fun v : T ⟶ X => v.left) h).symm).hom.app E ≫
    (Scheme.Modules.pullbackComp g.left p.left).inv.app E ≫
      (Scheme.Modules.pullback g.left).map q ≫ (pullbackUnit T.left V.left g.left).hom

/-- The actual negative-dual bundle, represented by linear forms on E. -/
structure DualBundleModel (X : SchemeOver k) (E : X.left.Modules) (r : ℕ) where
  locallyFree : IsBundle E r
  total : SchemeOver k
  projection : total ⟶ X
  universalForm : (Scheme.Modules.pullback projection.left).obj E ⟶
    SheafOfModules.unit total.left.ringCatSheaf
  universal : ∀ (T : SchemeOver k) (f : T ⟶ X)
    (s : (Scheme.Modules.pullback f.left).obj E ⟶ SheafOfModules.unit T.left.ringCatSheaf),
    ∃! g : T ⟶ total, ∃ h : g ≫ projection = f,
      s = pulledForm E projection universalForm f g h

def DualBundleModel.zeroSection {X : SchemeOver k} {E : X.left.Modules} {r : ℕ}
    (B : DualBundleModel X E r) : X ⟶ B.total :=
  Classical.choose (B.universal X (𝟙 X) 0)

theorem DualBundleModel.zeroSection_projection {X : SchemeOver k} {E : X.left.Modules} {r : ℕ}
    (B : DualBundleModel X E r) : B.zeroSection ≫ B.projection = 𝟙 X :=
  (Classical.choose_spec (B.universal X (𝟙 X) 0)).1.choose

section PresentationComparison

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (R : PolynomialResolution A B) (P : _root_.Algebra.Extension.{0} A B)

structure PolynomialLift where
  hom : R.algebra.obj (op ⦋0⦌) →ₐ[A] P.Ring
  over : (IsScalarTower.toAlgHom A P.Ring B).comp hom =
    (R.augmentation.app (op ⦋0⦌)).hom

theorem augmentation_face (i : Fin 2) (p : R.algebra.obj (op ⦋1⦌)) :
    (R.augmentation.app (op ⦋0⦌)).hom (R.algebra.δ i p) =
      (R.augmentation.app (op ⦋1⦌)).hom p := by
  have h := R.augmentation.naturality (SimplexCategory.δ i).op
  exact congrArg (fun f : R.algebra.obj (op ⦋1⦌) ⟶ CommAlgCat.of A B => f p) h

def liftError (L : PolynomialLift R P) (p : R.algebra.obj (op ⦋1⦌)) : P.Cotangent :=
  _root_.Algebra.Extension.Cotangent.mk ⟨L.hom (R.algebra.δ (0 : Fin 2) p) -
    L.hom (R.algebra.δ (1 : Fin 2) p), by
    change algebraMap P.Ring B _ = 0
    have hov (t : R.algebra.obj (op ⦋0⦌)) : algebraMap P.Ring B (L.hom t) =
        (R.augmentation.app (op ⦋0⦌)).hom t :=
      congrArg (fun f : R.algebra.obj (op ⦋0⦌) →ₐ[A] B => f t) L.over
    rw [map_sub, hov, hov, augmentation_face, augmentation_face, sub_self]⟩

abbrev presentationDifferential :=
  (CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom P.cotangentComplex)

/-- The full-to-naive comparison, fixed in both nonzero degrees by the actual
polynomial lift and its conormal face error. No naive/full equivalence is assumed. -/
structure PresentationTruncation where
  lift : PolynomialLift R P
  map : affineComplex R ⟶ MathlibExt.AlgebraicGeometry.AffineConeAtlas.cotangentComplex P
  degreeZero : ∀ x : R.algebra.obj (op ⦋0⦌),
    map.f 0 ((affineDegreeIso R 0).inv
      (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A B)
        R.algebra R.augmentation (op ⦋0⦌) x)) =
    (CochainComplex.mappingCone.inr (presentationDifferential P)).f 0
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B P.CotangentSpace)).inv
          ((1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (lift.hom x)))
  degreeMinus : ∀ x : R.algebra.obj (op ⦋1⦌),
    map.f (-1) ((affineDegreeIso R 1).inv
      (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A B)
        R.algebra R.augmentation (op ⦋1⦌) x)) =
    (CochainComplex.mappingCone.inl (presentationDifferential P)).v 0 (-1) (by decide)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of B P.Cotangent)).inv (liftError R P lift x))
  [h0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{0} B) 0).map
    (DerivedCategory.Q.map map))]
  [hMinus : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{0} B) (-1)).map
    (DerivedCategory.Q.map map))]
attribute [instance] PresentationTruncation.h0 PresentationTruncation.hMinus

end PresentationComparison

/-- A chart matching the genuine global map and source to the Rees/POT matrix. -/
structure POTChart {X : SchemeOver k} (P : TwoTermPOT X) where
  chart : AffineChart X.hom
  target_top : chart.target = ⊤
  [noetherian : IsNoetherianRing chart.ring]
  presentation : _root_.Algebra.Extension.{0} chart.base chart.ring
  [smooth : _root_.Algebra.Smooth chart.base presentation.Ring]
  matrix : MathlibExt.AlgebraicGeometry.AffineConeAtlas.ConePresentation presentation
  negativeRank : matrix.negativeRank = P.model.negativeRank
  zeroRank : matrix.zeroRank = P.model.zeroRank
  negativeFrame : ModuleCat.of chart.ring (Fin matrix.negativeRank → chart.ring) ≅
    (moduleSections chart.source).obj P.model.negative
  zeroFrame : ModuleCat.of chart.ring (Fin matrix.zeroRank → chart.ring) ≅
    (moduleSections chart.source).obj P.model.degreeZero
  sourceIso : MathlibExt.AlgebraicGeometry.AffineConeAtlas.modelComplex matrix ≅
    sectionsComplex (sourceComplex P.model) chart.source
  negative_frame :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of chart.ring (Fin matrix.negativeRank → chart.ring))).inv ≫
      (CochainComplex.mappingCone.inl
        ((CochainComplex.singleFunctor (ModuleCat.{0} chart.ring) 0).map
          (ModuleCat.ofHom matrix.differential))).v 0 (-1) (by decide) ≫
      sourceIso.hom.f (-1) =
    negativeFrame.hom ≫ (moduleSections chart.source).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P.model.negative).inv ≫
      (moduleSections chart.source).map ((CochainComplex.mappingCone.inl
        ((CochainComplex.singleFunctor X.left.Modules 0).map P.model.differential)).v
          0 (-1) (by decide))
  zero_frame :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of chart.ring (Fin matrix.zeroRank → chart.ring))).inv ≫
      (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (ModuleCat.{0} chart.ring) 0).map
          (ModuleCat.ofHom matrix.differential))).f 0 ≫ sourceIso.hom.f 0 =
    zeroFrame.hom ≫ (moduleSections chart.source).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P.model.degreeZero).inv ≫
      (moduleSections chart.source).map ((CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor X.left.Modules 0).map P.model.differential)).f 0)
  truncation : PresentationTruncation (P.cotangent.resolution chart) presentation
  map_eq : DerivedCategory.Q.map
      (MathlibExt.AlgebraicGeometry.AffineConeAtlas.comparisonCochain matrix) =
    DerivedCategory.Q.map sourceIso.hom ≫
      DerivedCategory.Q.map (((moduleSections chart.source).mapHomologicalComplex
        (ComplexShape.up ℤ)).map P.map) ≫
      inv (DerivedCategory.Q.map (P.cotangent.comparison chart)) ≫
      DerivedCategory.Q.map truncation.map
  pot : MathlibExt.AlgebraicGeometry.AffineConeAtlas.IsObstructionTheory matrix
attribute [instance] POTChart.noetherian POTChart.smooth

namespace POTChart
variable {X : SchemeOver k} {P : TwoTermPOT X} (a : POTChart P)

abbrev ring := SymmetricAlgebra a.chart.ring (Fin a.matrix.negativeRank → a.chart.ring)
abbrev bundle := Spec (CommRingCat.of a.ring)
def bundleProjection : a.bundle ⟶ Spec (.of a.chart.ring) :=
  Spec.map (CommRingCat.ofHom (algebraMap a.chart.ring a.ring))
abbrev coneIdeal := RingHom.ker
  (MathlibExt.AlgebraicGeometry.AffineConeAtlas.atlasHom a.matrix).toRingHom
abbrev cone := Spec (CommRingCat.of (a.ring ⧸ a.coneIdeal))
def coneInclusion : a.cone ⟶ a.bundle :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a.coneIdeal))
def baseMap : Spec (.of a.chart.ring) ⟶ X.left := a.chart.source_affine.fromSpec

end POTChart

/-- The actual pullback of a universal linear form, on scheme morphisms. -/
def pulledSchemeForm {X T V : Scheme.{0}} (E : X.Modules) (p : V ⟶ X)
    (q : (Scheme.Modules.pullback p).obj E ⟶ SheafOfModules.unit V.ringCatSheaf)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :
    (Scheme.Modules.pullback f).obj E ⟶ SheafOfModules.unit T.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr h.symm).hom.app E ≫
    (Scheme.Modules.pullbackComp g p).inv.app E ≫
      (Scheme.Modules.pullback g).map q ≫ (pullbackUnit T V g).hom

/-- Actual cone and bundle chart comparisons, with bundle coordinates fixed
by the source frame and the universal linear form. -/
structure ConeChartComparison {X : SchemeOver k} (P : TwoTermPOT X)
    (B : DualBundleModel X P.model.negative P.model.negativeRank)
    (C : SchemeOver k) (i : C ⟶ B.total) (a : POTChart P) where
  bundleMap : a.bundle ⟶ B.total.left
  bundle_over : bundleMap ≫ B.projection.left = a.bundleProjection ≫ a.baseMap
  bundle_square : IsPullback bundleMap a.bundleProjection B.projection.left a.baseMap
  coneMap : a.cone ⟶ C.left
  cone_square : IsPullback coneMap a.coneInclusion i.left bundleMap
  preimage_top : a.baseMap ⁻¹ᵁ a.chart.source = ⊤
  basis : ∀ _ : Fin a.matrix.negativeRank,
    SheafOfModules.unit (Spec (.of a.chart.ring)).ringCatSheaf ⟶
      (Scheme.Modules.pullback a.baseMap).obj P.model.negative
  basis_value : ∀ j,
    Scheme.Modules.Hom.app (X := X.left)
      ((Scheme.Modules.pullbackPushforwardAdjunction a.baseMap).unit.app P.model.negative)
      a.chart.source (a.negativeFrame.hom (Pi.single j 1)) =
    ((Scheme.Modules.pullback a.baseMap).obj P.model.negative).presheaf.map
      (eqToHom preimage_top).op
        ((((Scheme.Modules.pullback a.baseMap).obj P.model.negative).unitHomEquiv
          (basis j)).val (op ⊤))
  coordinates : ∀ j,
    ((SheafOfModules.unit a.bundle.ringCatSheaf).unitHomEquiv
      (pullbackSection a.bundleProjection ((Scheme.Modules.pullback a.baseMap).obj P.model.negative)
      (basis j) ≫ (Scheme.Modules.pullbackComp a.bundleProjection a.baseMap).hom.app
        P.model.negative ≫
      pulledSchemeForm P.model.negative B.projection.left B.universalForm
        (a.bundleProjection ≫ a.baseMap) bundleMap bundle_over)).val (op ⊤) =
    (Scheme.ΓSpecIso (.of a.ring)).inv.hom
      (SymmetricAlgebra.ι a.chart.ring (Fin a.matrix.negativeRank → a.chart.ring) (Pi.single j 1))
  atlas_closed : Function.Surjective
    (MathlibExt.AlgebraicGeometry.AffineConeAtlas.atlasHom a.matrix)
  translation_stability : ∀ (D : Type) [CommRing D] [Algebra a.chart.ring D]
    (x : MathlibExt.AlgebraicGeometry.AffineConeAtlas.AtlasPoint a.matrix D)
    (t : (Fin a.matrix.zeroRank → a.chart.ring) →ₗ[a.chart.ring] D),
    ∃ y : MathlibExt.AlgebraicGeometry.AffineConeAtlas.AtlasPoint a.matrix D,
      MathlibExt.AlgebraicGeometry.AffineConeAtlas.coordinates a.matrix D y =
        MathlibExt.AlgebraicGeometry.AffineConeAtlas.coordinates a.matrix D x +
          t ∘ₗ a.matrix.differential

/-- A genuine global cone image: actual local pullback identifications with
the computed Rees/POT images on a covering family, including normalized maps.
Existence and these comparison proofs are explicit construction dependencies. -/
structure IntrinsicConeModel {X : SchemeOver k} (P : TwoTermPOT X)
    (B : DualBundleModel X P.model.negative P.model.negativeRank) where
  cone : SchemeOver k
  inclusion : cone ⟶ B.total
  [closed : IsClosedImmersion inclusion.left]
  [noetherian : IsNoetherian cone.left]
  Index : Type
  chart : Index → POTChart P
  covers : ∀ x : X.left, ∃ j : Index, x ∈ (chart j).chart.source
  comparison : ∀ j, ConeChartComparison P B cone inclusion (chart j)
attribute [instance] IntrinsicConeModel.closed IntrinsicConeModel.noetherian

instance IntrinsicConeModel.locallyOfFiniteType {X : SchemeOver k} {P : TwoTermPOT X}
    {B : DualBundleModel X P.model.negative P.model.negativeRank}
    (C : IntrinsicConeModel P B) [LocallyOfFiniteType B.total.hom] :
    LocallyOfFiniteType C.cone.hom := by
  rw [← C.inclusion.w]
  infer_instance

variable {X : SchemeOver k} (P : TwoTermPOT X)
  (B : DualBundleModel X P.model.negative P.model.negativeRank)
  (C : IntrinsicConeModel P B) [LocallyOfFiniteType X.hom]
  [LocallyOfFiniteType B.total.hom] [IsNoetherian X.left] [IsNoetherian B.total.left]
  (D : ChowPullbackEquivalence X B.total B.projection P.model.negativeRank)
  (J : ClosedCycleDescent B.total C.inclusion)

/-- The computed global zero-section operator on the normalized intrinsic
cone carrier. Its only proof inputs concern the displayed actual cycle maps. -/
def zeroSectionPullback (d : ℤ) :
    gradedChow C.cone d →ₗ[ℚ] gradedChow X (d - P.model.negativeRank) :=
  (pullbackEquiv X B.total B.projection P.model.negativeRank D
    (d - P.model.negativeRank)).symm.toLinearMap ∘ₗ
      gradedChowCast B.total (by omega) ∘ₗ gradedClosedPush B.total C.inclusion J d

/-- The normalized global virtual class has degree rank(E0)-rank(E−1),
and is computed from the actual generic-length fundamental cone cycle. -/
def virtualClass : gradedChow X ((P.model.zeroRank : ℤ) - P.model.negativeRank) :=
  zeroSectionPullback P B C D J P.model.zeroRank
    ((positiveChowIso C.cone P.model.zeroRank (by omega)).toLinearEquiv.symm
      ((relations C.cone P.model.zeroRank).mkQ
        (fundamentalCycleOfDimension C.cone.left P.model.zeroRank)))

end MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass
