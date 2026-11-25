/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGlobalDualSourceModels
public import MathlibExt.AlgebraicGeometry.LiGlobalCoefficientModels
public import MathlibExt.AlgebraicGeometry.POTActualConeCoordinates
public import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks
public import MathlibExt.AlgebraicGeometry.RubberVirtualClassModels
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Source-qualified global Li POT, cone and virtual outputs

The input source is the completed whole coefficient/cochain diagram
constructed from the actual Li family. All final bundle, perfect
obstruction, cone and Chow recipe data below are outputs. The final
Wanted factories use the actual relative or central source constructor,
not an arbitrary complex or supplied virtual class.

A global module-presheaf differential presents the same source. Its
terms need not be globally free, locally free or constant-rank modules.
ONE linear strong transformation identifies its actual quotient
pseudofunctor with the full bundle-stack diagram, including all overlap
two-cells. ONE whole cochain roof binds that presentation
to the supplied Li source. The POT source is its global derived dual,
with actual evaluation/coevaluation triangle homotopies.

The map P -> L is one global cochain map into the source-normalized,
full coherent cotangent. Its H0/H-1 conditions and local perfect
amplitude are genuine native properties. The constructed affine POT atlas
is fixed by the same map, using the actual degree-0 polynomial lift and
degree-1 face differences before the canonical two-term truncation.
The resulting global conical embedding and virtual class use the native
full-Kresch specialization/push/zero-section-inverse recipe.

Sources: Jun Li math/0110113v1 Sections 1--2; Behrend--Fantechi
alg-geom/9601010 Section 4; Manolache0805.2065v2 Construction 3.6;
native coefficient source PR4048 e6e3c8d7c02b1baedace4e3044e622070b5217d0;
implemented AxiomMath/Stacks cotangent source
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiSourceQualifiedVirtualModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open StackVectorBundles StackBundleCones StackChowGroups StackCycleRelations StackVirtualPullbacks
open AffineConeAtlas LiGlobalDualSourceModels
open _root_.AlgebraicTopology _root_.Simplicial
open scoped Simplicial TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))

/-- Ordinary module-presheaf terms, without a global resolution-property requirement. -/
structure SourcePresentation where
  zero : ModulePresheaf X
  one : ModulePresheaf X
  differential : zero ⟶ one

variable {X}

def SourcePresentation.complex (B : SourcePresentation X) : SmallComplex X :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModulePresheaf X) 2).map B.differential)

/-- The literal restriction of the actual global differential and its quotient groupoid. -/
def quotientRestriction (B : SourcePresentation X) {p q : (AffinePoint X)ᵒᵖ} (f : p ⟶ q) :
    AdditiveQuotient (R := (rings X).obj p) (B.differential.app p).hom ⥤
      AdditiveQuotient (R := (rings X).obj q) (B.differential.app q).hom where
  obj x := ⟨B.one.restrictₛₗ f x.value⟩
  map e :=
    { translation := B.zero.restrictₛₗ f e.translation
      relation := by
        change B.one.restrictₛₗ f _ = B.one.restrictₛₗ f _ +
          B.differential.app q (B.zero.restrictₛₗ f e.translation)
        rw [e.relation, map_add]
        congr 1
        exact (PresheafOfModules.naturality_apply B.differential f e.translation).symm }
  map_id x := by apply AdditiveQuotient.hom_ext; exact map_zero _
  map_comp e h := by
    apply AdditiveQuotient.hom_ext
    exact map_add _ _ _

/-- A construction output with all values and all source restrictions fixed. -/
structure SourceQuotientDiagram (B : SourcePresentation X) where
  functor : (AffinePoint X)ᵒᵖ ⥤ Cat.{0, 0}
  objects : ∀ p, functor.obj p =
    Cat.of (AdditiveQuotient (R := (rings X).obj p) (B.differential.app p).hom)
  maps : ∀ {p q : (AffinePoint X)ᵒᵖ} (f : p ⟶ q),
    eqToHom (objects p).symm ≫ functor.map f ≫ eqToHom (objects q) =
      (quotientRestriction B f).toCatHom

def SourceQuotientDiagram.pseudofunctor {B : SourcePresentation X} (Q : SourceQuotientDiagram B) :
    Pseudofunctor (LocallyDiscrete (AffinePoint X)ᵒᵖ) Cat.{0, 0} := Q.functor.toPseudofunctor'

variable (E : VectorBundleStack X) (L : LargeComplex X)

/-- ONE linear comparison of full pseudofunctors fixes the actual overlap two-cells. -/
structure BundleBinding where
  presentation : SourcePresentation X
  diagram : SourceQuotientDiagram presentation
  comparison : Pseudofunctor.StrongTrans E.linear.diagram.pseudofunctor diagram.pseudofunctor
  equivalence : ∀ p : AffinePoint X, (comparison.app (.mk (op p))).toFunctor.IsEquivalence
  linear : ∀ p : AffinePoint X,
    SemilinearQuotientMap (E.linear.diagram.modules p).differential.hom
      (presentation.differential.app (op p)).hom (RingHom.id ((rings X).obj (op p)))
  component : ∀ p : AffinePoint X,
    eqToHom (E.linear.diagram.objects p).symm ≫ comparison.app (.mk (op p)) ≫
      eqToHom (diagram.objects (op p)) = (linear p).functor.toCatHom
  naturality_linear : ∀ {p q : AffinePoint X} (f : p ⟶ q),
    ∃ h : (E.linear.diagram.modules q).degreeOne →ₛₗ[((rings X).map f.op).hom]
      presentation.zero.obj (op p),
      ∀ x : (E.linear.diagram.modules q).Point,
        ((eqToHom (diagram.objects (op p))).toFunctor.map
          ((Cat.Hom.toNatIso (comparison.naturality f.op.toLoc)).hom.app
            ((eqToHom (E.linear.diagram.objects q).symm).toFunctor.obj x))).translation = h x.value
  sourceModel : LargeComplex X
  presentationMap : sourceModel ⟶ raised X presentation.complex
  [presentationQuasi : QuasiIso presentationMap]
  sourceMap : sourceModel ⟶ L
  [sourceQuasi : QuasiIso sourceMap]
attribute [instance] BundleBinding.presentationQuasi BundleBinding.sourceQuasi

/-- Perfect amplitude [-1,0] on every actual principal affine neighborhood. -/
def LocallyPerfectAmplitude (P : SmallComplex X) : Prop :=
  ∀ (p : AffinePoint X) (x : PrimeSpectrum ((rings X).obj (op p))),
    ∃ s : (rings X).obj (op p), s ∉ x.asIdeal ∧
    ∃ negativeRank zeroRank : ℕ,
    ∃ d : (Fin negativeRank → Localization.Away s) →ₗ[Localization.Away s]
      (Fin zeroRank → Localization.Away s),
    Nonempty
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap ((rings X).obj (op p))
          (Localization.Away s))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (GlobalStackCotangentModels.evaluate P p)) ≅
        DerivedCategory.Q.obj
          (AffineObstructionComplexes.complex (Localization.Away s) ⟨negativeRank, zeroRank, d⟩))

section Truncation

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  (R : GeometricCotangentComplex.PolynomialResolution A B) (P : _root_.Algebra.Extension.{0} A B)

def presentationArrow :=
  (CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom P.cotangentComplex)

def negativeProjection : (AffineConeAtlas.cotangentComplex P).X (-1) ⟶ ModuleCat.of B P.Cotangent :=
  (CochainComplex.mappingCone.fst (presentationArrow P)).val.v (-1) 0 (by simp) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B P.Cotangent)).hom

def zeroProjection : (AffineConeAtlas.cotangentComplex P).X 0 ⟶ ModuleCat.of B P.CotangentSpace :=
  (CochainComplex.mappingCone.snd (presentationArrow P)).v 0 0 (by simp) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B P.CotangentSpace)).hom

/-- The actual degree-zero lift and degree-one face relation determine the
canonical two-term truncation of this full polynomial-resolution target. -/
structure CotangentTruncation where
  lift : R.algebra.obj (op ⦋0⦌) →ₐ[A] P.Ring
  augmentation : ∀ x, algebraMap P.Ring B (lift x) = R.augmentation.app (op ⦋0⦌) x
  relation : R.algebra.obj (op ⦋1⦌) → P.ker
  relation_value : ∀ x, (relation x).val =
    lift (R.algebra.map (SimplexCategory.δ (0 : Fin 2)).op x) -
      lift (R.algebra.map (SimplexCategory.δ (1 : Fin 2)).op x)
  map : GeometricCotangentComplex.affineComplex R ⟶ AffineConeAtlas.cotangentComplex P
  pure_zero : ∀ x : R.algebra.obj (op ⦋0⦌),
    zeroProjection P (map.f 0 ((GeometricCotangentComplex.affineDegreeIso R 0).inv
      (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A B)
        R.algebra R.augmentation (op ⦋0⦌) x))) =
      (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (lift x)
  pure_negative : ∀ x : R.algebra.obj (op ⦋1⦌),
    negativeProjection P (map.f (-1) ((GeometricCotangentComplex.affineDegreeIso R 1).inv
      (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A B)
        R.algebra R.augmentation (op ⦋1⦌) x))) = _root_.Algebra.Extension.Cotangent.mk (relation x)
  [zeroIso : IsIso (HomologicalComplex.homologyMap map 0)]
  [negativeIso : IsIso (HomologicalComplex.homologyMap map (-1))]
attribute [instance] CotangentTruncation.zeroIso CotangentTruncation.negativeIso

end Truncation

variable {Y : Stack (Spec (.of k))} {f : StackHom X Y}
  (C : LiGlobalCoefficientModels.Context X)
  (T : LiGlobalCoefficientModels.CotangentBinding f C)
  (P : LiGlobalCoefficientModels.SourceBinding f C T)

def evaluateMorphism (h : P.complex ⟶ T.native.complex) (p : AffinePoint X) :=
  ((PresheafOfModules.evaluation (rings X ⋙ forget₂ CommRingCat RingCat)
    (op p)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map h

def chartEvaluation (Q : SmallComplex X) (c : IntrinsicConeChart f) :
    CochainComplex (ModuleCat.{0} Γ(c.geometry.source.U.left, ⊤)) ℤ :=
  GlobalStackCotangentModels.evaluate Q (GlobalStackCotangentModels.chartPoint c)

/-- Every cone chart uses the SAME global POT morphism and actual target truncation. -/
structure AffinePOTBinding (c : IntrinsicConeChart f)
    (F : letI := c.geometry.algebra; ConePresentation c.presentation) where
  truncation : letI := c.geometry.algebra;
    CotangentTruncation (T.native.resolution c) c.presentation
  targetMap : letI := c.geometry.algebra;
    chartEvaluation T.native.complex c ⟶
      AffineConeAtlas.cotangentComplex c.presentation
  target_square : letI := c.geometry.algebra; T.native.comparison c ≫ targetMap = truncation.map
  sourceModel : CochainComplex (ModuleCat.{0} Γ(c.geometry.source.U.left, ⊤)) ℤ
  toPot : letI := c.geometry.algebra; sourceModel ⟶
    chartEvaluation P.complex c
  [potQuasi : letI := c.geometry.algebra; QuasiIso toPot]
  toPresentation : letI := c.geometry.algebra; sourceModel ⟶ AffineConeAtlas.modelComplex F
  [presentationQuasi : letI := c.geometry.algebra; QuasiIso toPresentation]
  map_square : letI := c.geometry.algebra;
    toPot ≫ evaluateMorphism C T P P.map (GlobalStackCotangentModels.chartPoint c) ≫ targetMap =
      toPresentation ≫ AffineConeAtlas.comparisonCochain F
attribute [instance] AffinePOTBinding.potQuasi AffinePOTBinding.presentationQuasi

variable (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
  (hX : FiniteTypeArtin k X) (Z : RubberVirtualClassModels.Point D K)

/-- All source-qualified POT/bundle/cone/Chow objects are constructed outputs. -/
structure VirtualData where
  structural : StackHom X Z.model.stack
  coefficients : LiGlobalCoefficientModels.Context X
  cotangent : LiGlobalCoefficientModels.CotangentBinding structural coefficients
  pot : LiGlobalCoefficientModels.SourceBinding structural coefficients cotangent
  perfect : LocallyPerfectAmplitude pot.complex
  [zeroIso : IsIso (HomologicalComplex.homologyMap pot.map 0)]
  [negativeEpi : Epi (HomologicalComplex.homologyMap pot.map (-1))]
  dual : Duality X pot.complex L
  bundle : VectorBundleStack X
  sourceBundle : BundleBinding bundle L
  star : ConditionStar structural bundle
  bundleScope : FiniteTypeArtin k bundle.total
  coneScope : FiniteTypeArtin k star.cone.total
  presentation : letI := star.cone.chart.geometry.algebra;
    ConePresentation star.cone.chart.presentation
  affinePot : AffinePOTBinding coefficients cotangent pot star.cone.chart presentation
  obstruction : letI := star.cone.chart.geometry.algebra; IsObstructionTheory presentation
  coneCoefficients : POTAffineModuleFrames.Coefficients
    star.cone.chart.geometry.source.U star.cone.chart.geometry.sourcePoint
  frame : letI := star.cone.chart.geometry.algebra;
    POTAffineModuleFrames.Frame bundle star.cone.chart.geometry.source.U
      star.cone.chart.geometry.sourcePoint
      star.cone.chart.presentation presentation coneCoefficients
  normalizedCone : letI := star.cone.chart.geometry.algebra;
    POTActualConeCoordinates.Model star.cone bundle star.embedding star.cone.chart
      presentation coneCoefficients frame
  recipe : VirtualPullbackRecipe D K hX Z.scope bundle bundleScope
    star.cone coneScope star.embedding
attribute [instance] VirtualData.zeroIso VirtualData.negativeEpi

def virtualClass (V : VirtualData L D K hX Z) :
    RationalChowGroup D K X hX (0 - V.bundle.virtualRank) :=
  StackVirtualPullbacks.virtualClass V.recipe 0 Z.fundamental Z.classes

end MathlibExt.AlgebraicGeometry.LiSourceQualifiedVirtualModels
