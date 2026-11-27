/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/AlgebraicGeometry/DeterminantTwoTermGlobal/Local.lean`

Modifications: native affine cochain avatars, native derived tilde, scalar extension and
pullback, and the whole native coefficient/composition square are used; the transition is
computed by the fully faithful native tilde preimage.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeDeterminantPresentations
public import MathlibExt.AlgebraicGeometry.DeterminantPullbackCoherence

/-!
# Actual affine derived transitions for global determinants

The transition between two affine avatars is the preimage of the native
Spec pullback/coefficient/composition square. Source and target objects
are the actual finite-projective cochain quotients. Every map is pinned
to the full sheaf-derived comparison; no affine line/frame map is assigned.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineDeterminantTransitions

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai AffineDerivedCoefficientModules SchemeDeterminantPresentations
open DeterminantPullbackCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{u}] [HasDerivedScalarExtensions.{u}]
  [∀ R : CommRingCat.{u}, PreservesFiniteLimits (tilde.functor R)]

/-- The exact native coefficient/pullback square of the affine parameter map. -/
def transitionSheafIso {X : Scheme.{u}} (K : FourierMukai.D X)
    {R S : CommRingCat.{u}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K a) (Q : AffinePresentation K a')
    (C : Coherence.{u}) (B : DerivedComparison g) :
    (derivedTilde S).obj ((derivedScalarExtension g).obj P.localComplex.derivedObject) ≅
      (derivedTilde S).obj Q.localComplex.derivedObject :=
  B.comparison.symm.app P.localComplex.derivedObject ≪≫
    (derivedPullback (Spec.map g)).mapIso P.comparison ≪≫
    (C.composition (Spec.map g) a).comparison.app K ≪≫
    eqToIso (congrArg (fun f : Spec S ⟶ X => (derivedPullback f).obj K) h) ≪≫
    Q.comparison.symm

/-- The actual affine derived transition, uniquely lifted through native tilde. -/
def transitionIso {X : Scheme.{u}} (K : FourierMukai.D X)
    {R S : CommRingCat.{u}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K a) (Q : AffinePresentation K a')
    (C : Coherence.{u}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful) :
    (derivedScalarExtension g).obj P.localComplex.derivedObject ≅ Q.localComplex.derivedObject :=
  F.preimageIso (transitionSheafIso K g a a' h P Q C B)

/-- Every transition is fixed by the full native sheaf-derived commuting square. -/
theorem transitionIso_normalization {X : Scheme.{u}} (K : FourierMukai.D X)
    {R S : CommRingCat.{u}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K a) (Q : AffinePresentation K a')
    (C : Coherence.{u}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful) :
    (derivedTilde S).map (transitionIso K g a a' h P Q C B F).hom =
      (transitionSheafIso K g a a' h P Q C B).hom := by
  exact F.map_preimage _

omit [HasDerivedScalarExtensions] in
/-- The actual affine map induced by a specified global derived isomorphism. -/
def affineDerivedIso {X : Scheme.{u}} {K L : FourierMukai.D X} (f : K ≅ L)
    {R : CommRingCat.{u}} (a : Spec R ⟶ X)
    (P : AffinePresentation K a) (Q : AffinePresentation L a)
    (F : (derivedTilde R).FullyFaithful) :
    P.localComplex.derivedObject ≅ Q.localComplex.derivedObject :=
  F.preimageIso (P.comparison ≪≫ (derivedPullback a).mapIso f ≪≫ Q.comparison.symm)

omit [HasDerivedScalarExtensions] in
/-- Its full global/affine map normalization is native tilde naturality. -/
theorem affineDerivedIso_normalization {X : Scheme.{u}} {K L : FourierMukai.D X} (f : K ≅ L)
    {R : CommRingCat.{u}} (a : Spec R ⟶ X)
    (P : AffinePresentation K a) (Q : AffinePresentation L a)
    (F : (derivedTilde R).FullyFaithful) :
    (derivedTilde R).map (affineDerivedIso f a P Q F).hom =
      P.comparison.hom ≫ (derivedPullback a).map f.hom ≫ Q.comparison.inv := by
  exact F.map_preimage _

end MathlibExt.AlgebraicGeometry.AffineDeterminantTransitions
