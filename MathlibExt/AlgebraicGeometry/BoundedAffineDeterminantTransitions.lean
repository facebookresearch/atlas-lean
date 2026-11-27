/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
public import MathlibExt.AlgebraicGeometry.DeterminantPullbackCoherence

/-!
# Full native affine transitions of arbitrary bounded perfect presentations

The transition is the native fully faithful tilde preimage of the
actual derived scalar-extension/pullback/composition square. Every
cochain degree of each bounded projective presentation is retained.
This extends the native two-term adapter without restricting amplitude.

Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Topology/Sheaves/Cohomology/DerivedPullback/CompositionCoherence.lean,
Apache 2.0; Stacks Project, Tags 0FJW and 0FJX. Generic affine derived
comparison and pullback coherence are existing source integration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedAffineDeterminantTransitions

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai AffineDerivedCoefficientModules RelativeDeterminantPairings
open DeterminantPullbackCoherence

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

def transitionSheafIso {X : Scheme.{0}} (K : FourierMukai.D X)
    {R S : CommRingCat.{0}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K R a) (Q : AffinePresentation K S a')
    (C : Coherence.{0}) (B : DerivedComparison g) :
    (derivedTilde S).obj ((derivedScalarExtension g).obj
      (DerivedCategory.Q.obj P.complex.cochain)) ≅
      (derivedTilde S).obj (DerivedCategory.Q.obj Q.complex.cochain) :=
  B.comparison.symm.app (DerivedCategory.Q.obj P.complex.cochain) ≪≫
    (derivedPullback (Spec.map g)).mapIso P.comparison ≪≫
      (C.composition (Spec.map g) a).comparison.app K ≪≫
        eqToIso (congrArg (fun f : Spec S ⟶ X => (derivedPullback f).obj K) h) ≪≫
          Q.comparison.symm

def transitionIso {X : Scheme.{0}} (K : FourierMukai.D X)
    {R S : CommRingCat.{0}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K R a) (Q : AffinePresentation K S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful) :
    (derivedScalarExtension g).obj (DerivedCategory.Q.obj P.complex.cochain) ≅
      DerivedCategory.Q.obj Q.complex.cochain :=
  F.preimageIso (transitionSheafIso K g a a' h P Q C B)

theorem transitionIso_normalization {X : Scheme.{0}} (K : FourierMukai.D X)
    {R S : CommRingCat.{0}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K R a) (Q : AffinePresentation K S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful) :
    (derivedTilde S).map (transitionIso K g a a' h P Q C B F).hom =
      (transitionSheafIso K g a a' h P Q C B).hom := F.map_preimage _

omit [HasDerivedScalarExtensions] in
def affineDerivedIso {X : Scheme.{0}} {K L : FourierMukai.D X} (f : K ≅ L)
    {R : CommRingCat.{0}} (a : Spec R ⟶ X) (P : AffinePresentation K R a)
    (Q : AffinePresentation L R a) (F : (derivedTilde R).FullyFaithful) :
    DerivedCategory.Q.obj P.complex.cochain ≅ DerivedCategory.Q.obj Q.complex.cochain :=
  F.preimageIso (P.comparison ≪≫ (derivedPullback a).mapIso f ≪≫ Q.comparison.symm)

end MathlibExt.AlgebraicGeometry.BoundedAffineDeterminantTransitions
