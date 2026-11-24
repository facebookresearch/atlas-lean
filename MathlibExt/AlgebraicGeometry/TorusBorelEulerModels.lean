/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoefficientProperDualityModels
public import MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe
public import MathlibExt.AlgebraicGeometry.FiniteTorusBorelApproximationModels

/-!
# Zero-section Euler classes in finite Borel approximations, relative to an orientation

The Euler class is the actual proper zero-section push of the smooth
fundamental class, followed by the inverse of the actual bundle-projection
cohomology map. Fundamental classes and Poincaré duality are taken from one
shared `OrientationData`: a dualizing representation with smooth purity for
every smooth separated complex variety of finite type, compatible with
isomorphisms. Two orientation
data differ on each space by a locally constant unit, so the Euler classes are
determined up to such units; they are the usual complex Euler classes when
the datum is the complex orientation, which is not encoded here. The
rank-zero Euler class is `1` for every datum
(`ZeroEulerGeometry.euler_eq_unitClass`). The equivariant class uses the native
finite-approximation comparison. The associated module is identified with the
original pulled equivariant module; its descent equation fixes the torus
action, including character twists. No independent Euler class or
cohomological push operator is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusBorelEulerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ConstructibleComplexes IntegralChowChernModels ComplexAnalytification
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels LinearizedLineBundles
open SymplecticTorusSourceModels FiniteTorusBorelApproximationModels
open CoefficientBettiModels CoefficientCompactSupportModels CoefficientProperDualityModels
attribute [local instance] HasDerivedCategory.standard

/-- Only the actual integer cohomological degree is changed. -/
def cohomologyCast {Z : TopCat.{0}} {i j : ℤ} (h : i = j) :
    CoefficientBettiModels.Cohomology ℂ Z i →ₗ[ℂ] CoefficientBettiModels.Cohomology ℂ Z j := by
  cases h
  exact LinearMap.id

/-- The degree cast is composition with the identity identification of the shifted units. -/
theorem cohomologyCast_eq {Z : TopCat.{0}} {i j : ℤ} (h : i = j) (x : Cohomology ℂ Z i) :
    cohomologyCast h x = x ≫ eqToHom (by rw [h]) := by
  subst h
  simp [cohomologyCast]

/-- The purity identification sends the fundamental class to the unit class (in degree
`2d - 2d`). -/
theorem purityHomologyEquiv_fundamentalClass (Z : TopCat.{0}) (D : DualizingComplex ℂ Z)
    (d : ℕ) (e : D.obj ≅ (coefficientUnit ℂ Z)⟦(2 * d : ℤ)⟧) :
    purityHomologyEquiv ℂ Z D d e (2 * d) (fundamentalClass ℂ Z D d e) =
      cohomologyCast (by omega) (unitClass ℂ Z) := by
  rw [cohomologyCast_eq]
  simp only [purityHomologyEquiv, fundamentalClass, unitClass, LinearEquiv.coe_mk,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  simp [shiftFunctorAdd', eqToHom_app]

/-- Orientation data: a dualizing representation with smooth purity for every smooth separated
complex variety of finite type (so that its analytic space is a Hausdorff manifold), compatible
with isomorphisms (the actual compact pullback along an isomorphism carries one top trace to the
other). Fundamental classes and Poincaré duality, hence the Euler classes below, are relative to
it. The complex orientation is one such datum; it is not encoded here. -/
structure OrientationData where
  /-- The dualizing representation of a smooth separated variety of dimension `d`. -/
  duality : ∀ (Y : Over base) (d : ℕ) [SmoothOfRelativeDimension d Y.hom] [IsSeparated Y.hom]
    [QuasiCompact Y.hom], DualizingComplex ℂ (space Y)
  /-- Its smooth purity. -/
  purity : ∀ (Y : Over base) (d : ℕ) [SmoothOfRelativeDimension d Y.hom] [IsSeparated Y.hom]
    [QuasiCompact Y.hom], (duality Y d).obj ≅ (coefficientUnit ℂ (space Y))⟦(2*d : ℤ)⟧
  /-- Isomorphisms preserve the induced top compact-support traces. -/
  isomorphism : ∀ {Y Y' : Over base} (f : Y ⟶ Y') [IsIso f] (d : ℕ)
    [SmoothOfRelativeDimension d Y.hom] [IsSeparated Y.hom] [QuasiCompact Y.hom]
    [SmoothOfRelativeDimension d Y'.hom] [IsSeparated Y'.hom] [QuasiCompact Y'.hom]
    (P : ProperPullback ℂ (spaceMap f)),
    compactPullback ℂ P (2*d) ≫ topTrace ℂ (space Y) (duality Y d) d (purity Y d) =
      topTrace ℂ (space Y') (duality Y' d) d (purity Y' d)

/-- Native zero-section geometry. Its compact-support duality and purity on the base and on the
total space are those of the given orientation datum, not independent choices. -/
structure ZeroEulerGeometry (O : OrientationData) (X : SchemeData) (E : X.scheme.left.Modules)
    (r : ℕ) where
  bundle : GlobalZeroSectionRecipe.VectorBundleModel X.scheme E r
  dimension : ℕ
  [baseSmooth : SmoothOfRelativeDimension dimension X.scheme.hom]
  [baseSeparated : IsSeparated X.scheme.hom]
  [baseQuasiCompact : QuasiCompact X.scheme.hom]
  [totalSmooth : SmoothOfRelativeDimension (dimension+r) bundle.total.hom]
  [totalSeparated : IsSeparated bundle.total.hom]
  [totalQuasiCompact : QuasiCompact bundle.total.hom]
  [closed : IsClosedImmersion (GlobalZeroSectionRecipe.zeroSection bundle).left]
  zeroPullback : ProperPullback ℂ (spaceMap (GlobalZeroSectionRecipe.zeroSection bundle))
  homotopy : ∀ n : ℤ, Function.Bijective
    (cohomologyPullback ℂ (spaceMap bundle.projection) n)

attribute [instance] ZeroEulerGeometry.baseSmooth ZeroEulerGeometry.totalSmooth
  ZeroEulerGeometry.totalSeparated ZeroEulerGeometry.totalQuasiCompact ZeroEulerGeometry.closed

section ZeroEuler

variable {O : OrientationData} {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}

/-- The base duality is the orientation datum's. -/
abbrev ZeroEulerGeometry.baseDuality (G : ZeroEulerGeometry O X E r) :
    DualizingComplex ℂ (space X.scheme) :=
  haveI := G.baseSeparated
  haveI := G.baseQuasiCompact
  O.duality X.scheme G.dimension

/-- The total-space duality is the orientation datum's. -/
abbrev ZeroEulerGeometry.totalDuality (G : ZeroEulerGeometry O X E r) :
    DualizingComplex ℂ (space G.bundle.total) :=
  O.duality G.bundle.total (G.dimension+r)

/-- The base purity is the orientation datum's. -/
abbrev ZeroEulerGeometry.basePurity (G : ZeroEulerGeometry O X E r) :
    G.baseDuality.obj ≅ (coefficientUnit ℂ (space X.scheme))⟦(2*G.dimension : ℤ)⟧ :=
  haveI := G.baseSeparated
  haveI := G.baseQuasiCompact
  O.purity X.scheme G.dimension

/-- The total-space purity is the orientation datum's. -/
abbrev ZeroEulerGeometry.totalPurity (G : ZeroEulerGeometry O X E r) :
    G.totalDuality.obj ≅ (coefficientUnit ℂ (space G.bundle.total))⟦(2*(G.dimension+r : ℕ) : ℤ)⟧ :=
  O.purity G.bundle.total (G.dimension+r)

/-- The zero-section class is computed from native proper push and the datum's smooth purity. -/
def ZeroEulerGeometry.zeroClass (G : ZeroEulerGeometry O X E r) :
    CoefficientBettiModels.Cohomology ℂ (space G.bundle.total) (2*r) :=
  cohomologyCast (show (2*(G.dimension+r) : ℤ)-(2*G.dimension : ℤ) = (2*r : ℤ) by omega)
    ((purityHomologyEquiv ℂ (space G.bundle.total) G.totalDuality (G.dimension+r)
      G.totalPurity (2*G.dimension)).toLinearMap
      (borelMoorePushforward ℂ G.zeroPullback G.baseDuality G.totalDuality (2*G.dimension)
        (fundamentalClass ℂ (space X.scheme) G.baseDuality G.dimension G.basePurity)))

/-- The Euler class, relative to the orientation datum, is the inverse actual bundle pullback of
that zero-section class. -/
def ZeroEulerGeometry.euler (G : ZeroEulerGeometry O X E r) :
    CoefficientBettiModels.Cohomology ℂ (space X.scheme) (2*r) :=
  (LinearEquiv.ofBijective (cohomologyPullback ℂ (spaceMap G.bundle.projection) (2*r))
    (G.homotopy (2*r))).symm G.zeroClass

/-- The zero section of a bundle of rank zero is an isomorphism: the module is zero, so its
total space represents the morphisms to the base, with the projection as inverse. -/
instance zeroSection_isIso_of_rank_zero {k : Type} [Field k] {Y : Over (Spec (.of k))}
    {F : Y.left.Modules} (B : GlobalZeroSectionRecipe.VectorBundleModel Y F 0) :
    IsIso (GlobalZeroSectionRecipe.zeroSection B) := by
  have hF : IsZero F := CurveVectorBundles.isZero_of_isVectorBundle_zero B.locallyFree
  have hz : IsZero ((Scheme.Modules.pullback B.projection.left).obj F) :=
    Functor.map_isZero _ hF
  have key : B.projection ≫ GlobalZeroSectionRecipe.zeroSection B = 𝟙 B.total :=
    (B.universal B.total B.projection 0).unique
      ⟨by rw [Category.assoc, GlobalZeroSectionRecipe.zeroSection_projection, Category.comp_id],
        hz.eq_of_tgt _ _⟩
      ⟨Category.id_comp _, hz.eq_of_tgt _ _⟩
  exact ⟨B.projection, GlobalZeroSectionRecipe.zeroSection_projection B, key⟩

/-- In rank zero the Euler class is the unit class for every orientation datum: the module is
zero, so the zero section is an isomorphism (`zeroSection_isIso_of_rank_zero`). -/
theorem ZeroEulerGeometry.euler_eq_unitClass {O : OrientationData} {X : SchemeData}
    {E : X.scheme.left.Modules} (G : ZeroEulerGeometry O X E 0) :
    G.euler = unitClass ℂ (space X.scheme) := by
  have : SmoothOfRelativeDimension G.dimension G.bundle.total.hom := G.totalSmooth
  have := G.baseSeparated
  have := G.baseQuasiCompact
  have hpush := borelMoorePushforward_fundamentalClass ℂ G.zeroPullback
    (O.duality X.scheme G.dimension) (O.duality G.bundle.total G.dimension) G.dimension
    (O.purity X.scheme G.dimension) (O.purity G.bundle.total G.dimension)
    (O.isomorphism (GlobalZeroSectionRecipe.zeroSection G.bundle) G.dimension G.zeroPullback)
  have hzero : G.zeroClass = cohomologyPullback ℂ (spaceMap G.bundle.projection) (2*0)
      (unitClass ℂ (space X.scheme)) := by
    simp only [ZeroEulerGeometry.zeroClass]
    erw [hpush, purityHomologyEquiv_fundamentalClass]
    rw [cohomologyCast_eq, cohomologyCast_eq, Category.assoc, eqToHom_trans]
    erw [cohomologyPullback_unitClass]
    simp
  simp only [ZeroEulerGeometry.euler, hzero]
  exact (LinearEquiv.ofBijective _ _).symm_apply_apply _

end ZeroEuler

/-- The pulled bundle comparison is the actual action/projection square of its original map. -/
def pulledLinearComparison {T Y Z : Over base} [GrpObj T] [ModObj T Y] [ModObj T Z]
    (f : Y ⟶ Z) (hf : γ[T,Y] ≫ f = (T ◁ f) ≫ γ[T,Z])
    {E : Z.left.Modules} (L : Linearization T Z E) :
    (Scheme.Modules.pullback γ[T,Y].left).obj ((Scheme.Modules.pullback f.left).obj E) ⟶
      (Scheme.Modules.pullback (snd T Y).left).obj ((Scheme.Modules.pullback f.left).obj E) :=
  (Scheme.Modules.pullbackComp γ[T,Y].left f.left).hom.app E ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).hom.app E ≫
    reindexHom (T ◁ f).left L.comparison.hom ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (whiskerLeft_snd T f))).hom.app E ≫
    (Scheme.Modules.pullbackComp (snd T Y).left f.left).inv.app E

/-- A module from the actual invariant quotient has its literal trivial relative transport. -/
def invariantPullbackComparison {T Y Z : Over base} [GrpObj T] [ModObj T Y]
    (f : Y ⟶ Z) (hf : γ[T,Y] ≫ f = snd T Y ≫ f) (E : Z.left.Modules) :
    (Scheme.Modules.pullback γ[T,Y].left).obj ((Scheme.Modules.pullback f.left).obj E) ⟶
      (Scheme.Modules.pullback (snd T Y).left).obj ((Scheme.Modules.pullback f.left).obj E) :=
  (Scheme.Modules.pullbackComp γ[T,Y].left f.left).hom.app E ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).hom.app E ≫
    (Scheme.Modules.pullbackComp (snd T Y).left f.left).inv.app E

variable {T : Over base} [GrpObj T] (M : TorusModel T) (X : SchemeData) [ModObj T X.scheme]
  (AX : AnalyticTorusAction M X.scheme) (m : ℕ)
  [ModObj T (MixedTotal M X m)] (A : AnalyticTorusAction M (MixedTotal M X m))
  (P : MixedStage M X AX m A) {E : X.scheme.left.Modules} (L : Linearization T X.scheme E)

/-- Descent retains the original module and its complete actual torus transport. -/
structure AssociatedModule where
  module : P.quotient.quotient.scheme.left.Modules
  comparison : (Scheme.Modules.pullback P.quotient.projection.left).obj module ≅
    (Scheme.Modules.pullback (snd (freeApproximation M.rank m) X.scheme).left).obj E
  equivariant :
    (Scheme.Modules.pullback γ[T,MixedTotal M X m].left).map comparison.hom ≫
      pulledLinearComparison (snd (freeApproximation M.rank m) X.scheme) P.projection L =
    invariantPullbackComparison P.quotient.projection P.quotient.invariant module ≫
      (Scheme.Modules.pullback (snd T (MixedTotal M X m)).left).map comparison.hom

/-- The finite-stage Euler geometry is for that exact descended original module, oriented by
the given datum. -/
structure EquivariantEulerGeometry (O : OrientationData) (r : ℕ) where
  associated : AssociatedModule M X AX m A P L
  zero : ZeroEulerGeometry O P.quotient.quotient associated.module r
  stableRange : (2*r : ℤ) < 2*m+1

/-- The class is transported by the actual finite Borel comparison, with no Borel properness
  assumption. It is relative to the orientation datum. -/
def EquivariantEulerGeometry.euler {O : OrientationData} {r : ℕ}
    (G : EquivariantEulerGeometry M X AX m A P L O r) :
    letI := AX.action
    letI := AX.continuous
    BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X.scheme) (2*r) := by
  letI := AX.action
  letI := AX.continuous
  exact (MixedStage.comparison M X AX m A P (2*r) G.stableRange).symm G.zero.euler

end MathlibExt.AlgebraicGeometry.TorusBorelEulerModels
