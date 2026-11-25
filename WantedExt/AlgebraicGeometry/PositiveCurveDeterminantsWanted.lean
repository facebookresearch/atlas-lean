/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PositiveCurveDeterminants
public import MathlibExt.AlgebraicGeometry.NativeLineDuals

/-!
# Native curve determinant descent and comparison requests

All affine determinants are the actual inverse of the [1]-shifted native
two-term presentation determinant. Every object, scalar map, derived
isomorphism and global pullback comparison has its full native affine
normalization in MathlibExt. These constructors assemble that data into
global lines; they do not duplicate a general arbitrary-amplitude theory.
Source: Knudsen--Mumford Sections 1--2; MRV arXiv:1207.7233v5,
Section 5, Equation (5.2). Pinned source attribution is in the imports.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PositiveCurveDeterminantsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open FourierMukai SchemeDeterminantPresentations ScalarDeterminantComplexes
open AffineDerivedCoefficientModules ProjectiveDeterminantModules PositiveCurveDeterminants
open NativeLineDuals CoherentCurveLinearSeries

def_wanted nativeLineDuality (X : Scheme.{0}) (L : X.Modules) (line : IsLineBundle L) :
    LineDuality X L

/-- **Affine determinant transports and derived base change.** Assume that derived pullbacks of
complexes of sheaves of modules along morphisms of schemes and derived extensions of scalars along
ring maps exist (as left derived functors), and that $M \mapsto \tilde M$ preserves finite limits
for every commutative ring. Then: for every commutative ring $R$, a system of Knudsen–Mumford
determinant transports along isomorphisms between two-term presentations in the derived category
of $R$-modules (`TransportSystem`); the coherence of derived pullback under composition and
identities; for every ring map $g : R \to S$, the comparison of derived pullback along
$\operatorname{Spec} g$ with derived scalar extension along $g$, through the derived tilde
functors, normalized on complexes; and full faithfulness of the derived tilde functor of every
commutative ring (`AffineSources`). -/
def_wanted affineSources [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)] : AffineSources

def_wanted positiveDeterminantScalarComparison [HasDerivedPullbacks.{0}]
    [HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    {R S : CommRingCat.{0}} (g : R ⟶ S) (P : LocalComplex R) (C : ScalarComplexData g P)
    (U : ∀ i : ℤ, IsScalarExtension g.hom (scalarUnit g (P.complex.X i)))
    (T : TermDeterminantData g P C U) : PositiveScalarComparison g P C U T

def_wanted curveDeterminantLine [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (S : AffineSources) (X : Scheme.{0}) (K : FourierMukai.D X)
    (perfect : IsPerfectTwoTermOn (K⟦(1 : ℤ)⟧)) : CurveDeterminantData S K

def_wanted curveDeterminantIso [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (S : AffineSources) {X : Scheme.{0}} {K L : FourierMukai.D X}
    (e : K⟦(1 : ℤ)⟧ ≅ L⟦(1 : ℤ)⟧)
    (P : CurveDeterminantData S K) (Q : CurveDeterminantData S L) : LineComparison S e P Q

def_wanted curveDeterminantPullback [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    (S : AffineSources) {X Y : Scheme.{0}} (f : Y ⟶ X)
    {K : FourierMukai.D X} {L : FourierMukai.D Y}
    (e : (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ L⟦(1 : ℤ)⟧)
    (P : CurveDeterminantData S K) (Q : CurveDeterminantData S L) :
    PullbackLineComparison S f e P Q

end WantedExt.AlgebraicGeometry.PositiveCurveDeterminantsWanted
