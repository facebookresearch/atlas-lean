/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineDeterminantTransitions
public import MathlibExt.AlgebraicGeometry.ScalarDeterminantComplexes
public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Source-normalized determinants of curve cohomology

The usual [0,1] determinant is the actual module dual of the determinant
of its [1]-shifted [-1,0] presentation. Global lines are compared with
every affine presentation, every native derived isomorphism, and every
nonflat affine ring map. The scalar dual comparison is fixed by the
actual two-term determinant map and its evaluation equation.

This specializes the completed two-term source from AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0),
DeterminantTwoTermGlobal and Homology/TwoTermComplex. The original
source adaptation notices are retained in the imported modules. Global
native descent/assembly is a separate constructor; no general bounded
amplitude theorem is claimed by this curve scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PositiveCurveDeterminants

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai SchemeDeterminantPresentations TwoTermDeterminantModels
open ScalarDeterminantComplexes AffineDerivedCoefficientModules AffineCoefficientModules
open AffineDeterminantTransitions DeterminantPullbackCoherence
open ProjectiveDeterminantModules CoherentCurveLinearSeries

attribute [local instance] HasDerivedCategory.standard

abbrev positiveModule {R : CommRingCat.{0}} (P : LocalComplex R) : ModuleCat.{0} R :=
  ModuleCat.of R (Module.Dual R P.determinant)

def positiveTransport {R : CommRingCat.{0}} (S : TransportSystem R)
    (P Q : LocalComplex R) (e : P.derivedObject ≅ Q.derivedObject) :
    positiveModule P ≅ positiveModule Q :=
  (S.transport P.presentation Q.presentation e).symm.dualMap.toModuleIso

variable [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

/-- Data on affine schemes, assuming that derived pullbacks and derived extensions of scalars exist
and that $M \mapsto \tilde M$ preserves finite limits: for every commutative ring $R$, a system of
determinant transports along isomorphisms between two-term presentations in the derived category
of $R$-modules (`TransportSystem`); coherence data for derived pullback under identities and
composition (`Coherence`); for every ring map $g : R \to S$, a comparison of derived pullback along
$\operatorname{Spec} g$ with derived extension of scalars along $g$ through the derived tilde
functors, normalized on complexes (`DerivedComparison`); and full faithfulness data for the derived
tilde functor $D(R) \to D(\operatorname{Spec} R)$ of every $R$. -/
structure AffineSources where
  transport : ∀ R : CommRingCat.{0}, TransportSystem R
  coherence : Coherence.{0}
  coefficient : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S), DerivedComparison g
  faithful : ∀ R : CommRingCat.{0}, (derivedTilde R).FullyFaithful

/-- The inverse determinant scalar map is fixed by the evaluation pairing
against the already computed ordinary determinant scalar map. -/
structure PositiveScalarComparison {R S : CommRingCat.{0}} (g : R ⟶ S)
    (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) where
  iso : (ModuleCat.extendScalars g.hom).obj (positiveModule P) ≅
    positiveModule (baseComplex g P C)
  normalization : ∀ (f : Module.Dual R P.determinant) (x : P.determinant),
    (iso.hom.hom (scalarUnit g (positiveModule P) f)) (determinantMap g P C U T x) = g.hom (f x)

def affinePositiveIso (S : AffineSources) {X : Scheme.{0}}
    {K L : FourierMukai.D X} (e : K⟦(1 : ℤ)⟧ ≅ L⟦(1 : ℤ)⟧)
    {R : CommRingCat.{0}} (a : Spec R ⟶ X)
    (P : AffinePresentation (K⟦(1 : ℤ)⟧) a) (Q : AffinePresentation (L⟦(1 : ℤ)⟧) a) :
    positiveModule P.localComplex ≅ positiveModule Q.localComplex :=
  positiveTransport (S.transport R) P.localComplex Q.localComplex
    (affineDerivedIso e a P Q (S.faithful R))

def basePositiveIso (S : AffineSources) {X : Scheme.{0}} (K : FourierMukai.D X)
    {R T : CommRingCat.{0}} (g : R ⟶ T) (a : Spec R ⟶ X) (a' : Spec T ⟶ X)
    (h : Spec.map g ≫ a = a')
    (P : AffinePresentation (K⟦(1 : ℤ)⟧) a) (Q : AffinePresentation (K⟦(1 : ℤ)⟧) a')
    (C : ScalarComplexData g P.localComplex) :
    positiveModule (baseComplex g P.localComplex C) ≅ positiveModule Q.localComplex :=
  positiveTransport (S.transport T) (baseComplex g P.localComplex C) Q.localComplex
    ((baseComplexIso g P.localComplex C).symm ≪≫
      transitionIso (K⟦(1 : ℤ)⟧) g a a' h P Q S.coherence (S.coefficient g) (S.faithful T))

/-- A line on the actual parameter scheme with all affine transition maps
fixed, including every presentation and every scalar-extension choice. -/
structure CurveDeterminantData (S : AffineSources) {X : Scheme.{0}} (K : FourierMukai.D X) where
  line : X.Modules
  lineBundle : IsLineBundle line
  perfect : IsPerfectTwoTermOn (K⟦(1 : ℤ)⟧)
  affine : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ X)
    (P : AffinePresentation (K⟦(1 : ℤ)⟧) a),
    (Scheme.Modules.pullback a).obj line ≅ (tilde.functor R).obj (positiveModule P.localComplex)
  presentation : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ X)
    (P Q : AffinePresentation (K⟦(1 : ℤ)⟧) a),
    (affine R a Q).hom = (affine R a P).hom ≫
      (tilde.functor R).map (affinePositiveIso S (Iso.refl (K⟦(1 : ℤ)⟧)) a P Q).hom
  baseChange : ∀ {R T : CommRingCat.{0}} (g : R ⟶ T)
    (a : Spec R ⟶ X) (a' : Spec T ⟶ X) (h : Spec.map g ≫ a = a')
    (P : AffinePresentation (K⟦(1 : ℤ)⟧) a) (Q : AffinePresentation (K⟦(1 : ℤ)⟧) a')
    (C : ScalarComplexData g P.localComplex)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.localComplex.complex.X i)))
    (T' : TermDeterminantData g P.localComplex C U)
    (V : PositiveScalarComparison g P.localComplex C U T'),
    (Scheme.Modules.pullback (Spec.map g)).map (affine R a P).hom ≫
      (pullbackTildeIso g).hom.app (positiveModule P.localComplex) ≫
        (tilde.functor T).map V.iso.hom ≫
          (tilde.functor T).map (basePositiveIso S K g a a' h P Q C).hom =
    (Scheme.Modules.pullbackComp (Spec.map g) a).hom.app line ≫
      (Scheme.Modules.pullbackCongr h).hom.app line ≫ (affine T a' Q).hom

/-- A global isomorphism is normalized on every actual affine avatar. -/
structure LineComparison (S : AffineSources) {X : Scheme.{0}} {K L : FourierMukai.D X}
    (e : K⟦(1 : ℤ)⟧ ≅ L⟦(1 : ℤ)⟧)
    (P : CurveDeterminantData S K) (Q : CurveDeterminantData S L) where
  iso : P.line ≅ Q.line
  normalized : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ X)
    (A : AffinePresentation (K⟦(1 : ℤ)⟧) a) (B : AffinePresentation (L⟦(1 : ℤ)⟧) a),
    (Scheme.Modules.pullback a).map iso.hom ≫ (Q.affine R a B).hom =
      (P.affine R a A).hom ≫ (tilde.functor R).map (affinePositiveIso S e a A B).hom

def affinePullbackIso (S : AffineSources) {X Y : Scheme.{0}} (f : Y ⟶ X)
    {K : FourierMukai.D X} {L : FourierMukai.D Y}
    (e : (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧)
    {R : CommRingCat.{0}} (a : Spec R ⟶ Y)
    (P : AffinePresentation (K⟦(1 : ℤ)⟧) (a ≫ f))
    (Q : AffinePresentation (L⟦(1 : ℤ)⟧) a) :
    positiveModule P.localComplex ≅ positiveModule Q.localComplex :=
  positiveTransport (S.transport R) P.localComplex Q.localComplex
    ((S.faithful R).preimageIso (P.comparison ≪≫
      ((S.coherence.composition a f).comparison.app (K⟦(1 : ℤ)⟧)).symm ≪≫
        (derivedPullback a).mapIso e ≪≫ Q.comparison.symm))

/-- Native pullback of the global line, fixed by actual derived composition
and the specified cohomology/shift comparison, on every affine test. -/
structure PullbackLineComparison (S : AffineSources) {X Y : Scheme.{0}} (f : Y ⟶ X)
    {K : FourierMukai.D X} {L : FourierMukai.D Y}
    (e : (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧)
    (P : CurveDeterminantData S K) (Q : CurveDeterminantData S L) where
  iso : (Scheme.Modules.pullback f).obj P.line ≅ Q.line
  normalized : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y)
    (A : AffinePresentation (K⟦(1 : ℤ)⟧) (a ≫ f))
    (B : AffinePresentation (L⟦(1 : ℤ)⟧) a),
    (Scheme.Modules.pullback a).map iso.hom ≫ (Q.affine R a B).hom =
      (Scheme.Modules.pullbackComp a f).hom.app P.line ≫ (P.affine R (a ≫ f) A).hom ≫
        (tilde.functor R).map (affinePullbackIso S f e a A B).hom

end MathlibExt.AlgebraicGeometry.PositiveCurveDeterminants
