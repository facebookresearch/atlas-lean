/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeterminantScalarTensorModels
public import MathlibExt.AlgebraicGeometry.BoundedAffineDeterminantTransitions

/-!
# Actual bounded determinant affine transport and global algebraic lines

Every determinant factor uses the exact bounded presentation of the
given derived object. Scalar comparison uses its native cochain source
counit, and transition transport is the fully faithful preimage of the
original derived pullback square. The determinant transition is the
computed scalar comparison followed by that actual derived-isomorphism
transport.

A global determinant line is normalized on all actual affine pullbacks
and those computed transitions. The global Deligne line is pinned to
the literal subset direct-image determinant expression on every affine.
Construction and coherence remain direct Wanted requests.

Sources: Knudsen--Mumford, Sections 1--2; Yuan--Zhang,
arXiv:2105.13587v9, Section 4.2.1 and Theorem 4.1.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open FourierMukai AffineDerivedCoefficientModules
open BoundedProjectiveDeterminants BoundedScalarDeterminants
open BoundedDeterminantTransportModels RelativeDeterminantPairings
open DeterminantPullbackCoherence BoundedAffineDeterminantTransitions

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

/-- The actual bounded scalar and derived-isomorphism determinant data. -/
structure DeterminantSources where
  transport : ∀ R : CommRingCat.{0}, TransportSystem R
  scalar : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (C : BoundedProjectiveDeterminants.Complex R),
    ScalarPresentation g C
  terms : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (C : BoundedProjectiveDeterminants.Complex R),
    TermSources g C (scalar g C)
  comparison : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : BoundedProjectiveDeterminants.Complex R), ScalarComparison g C (scalar g C) (terms g C)
  scalar_source : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : BoundedProjectiveDeterminants.Complex R),
    IsIso ((derivedScalarExtensionCounit g).app C.cochain)

variable (I : DeterminantSources)

/-- The native scalar source comparison of the actual bounded target. -/
def scalarDerivedIso {R S : CommRingCat.{0}} (g : R ⟶ S)
    (C : BoundedProjectiveDeterminants.Complex R) :
    DerivedCategory.Q.obj (I.scalar g C).target.cochain ≅
      (derivedScalarExtension g).obj (DerivedCategory.Q.obj C.cochain) := by
  haveI := I.scalar_source g C
  exact DerivedCategory.Q.mapIso (I.scalar g C).cochain ≪≫
    (asIso ((derivedScalarExtensionCounit g).app C.cochain)).symm

/-- The actual bounded affine transition, with every derived coefficient map retained. -/
def determinantTransition {X : Scheme.{0}} (K : FourierMukai.D X)
    {R S : CommRingCat.{0}} (g : R ⟶ S) (a : Spec R ⟶ X) (a' : Spec S ⟶ X)
    (h : Spec.map g ≫ a = a') (P : AffinePresentation K R a) (Q : AffinePresentation K S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful) :
    (ModuleCat.extendScalars g.hom).obj (determinantObject R P.complex) ≅
      determinantObject S Q.complex :=
  (I.comparison g P.complex).comparison ≪≫
    (I.transport S).map
      ⟨(I.scalar g P.complex).target⟩ ⟨Q.complex⟩
      (scalarDerivedIso I g P.complex ≪≫ transitionIso K g a a' h P Q C B F)

variable {X : Scheme.{0}} (K : FourierMukai.D X)

/-- All actual affine bounded presentations of this same derived object. -/
abbrev AffineFamily :=
  ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ X), AffinePresentation K R a

/-- An algebraic determinant line is identified with its exact affine determinant modules. -/
structure DeterminantLine (P : AffineFamily K) where
  line : X.Modules
  isLine : CoherentCurveLinearSeries.IsLineBundle line
  affine : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ X),
    (Scheme.Modules.pullback a).obj line ≅
      (tilde.functor R).obj (determinantObject R (P R a).complex)
  transition_normalized : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ X) (a' : Spec S ⟶ X) (h : Spec.map g ≫ a = a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful),
    (Scheme.Modules.pullback (Spec.map g)).map (affine R a).hom ≫
      (AffineCoefficientModules.pullbackTildeIso g).hom.app (determinantObject R (P R a).complex) ≫
      (tilde.functor S).map (determinantTransition I K g a a' h (P R a) (P S a') C B F).hom =
    (Scheme.Modules.pullbackComp (Spec.map g) a).hom.app line ≫
      (eqToIso (congrArg (fun q : Spec S ⟶ X => (Scheme.Modules.pullback q).obj line) h)).hom ≫
        (affine S a').hom

variable [HasDerivedPushforwards.{0}]

variable [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Every signed local factor uses the computed scalar determinant
transition or its inverse dual. -/
def pairingFactorComparison {Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (P : Presentations f L R a) (Q : Presentations f L S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g) (s : Finset (Fin m)) :
    (ModuleCat.extendScalars g.hom).obj (factor P s) ≅ factor Q s := by
  classical
  let e := determinantTransition I (directImage f (subsetTensor L s)) g a a' h (P s) (Q s) C B F
  by_cases hs : IsPositive s
  · simpa only [factor, hs, ite_true] using e
  · haveI := determinantObject_invertible R (P s).complex
    let M := determinantObject R (P s).complex
    let d := T.dual M (by infer_instance) (by infer_instance)
    simpa only [factor, hs, ite_false] using d ≪≫ e.symm.toLinearEquiv.dualMap.toModuleIso

/-- The actual ordered subset-factor fold, with empty tensor its native scalar unit. -/
def pairingFold {Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ} {L : Fin m → X.Modules}
    {R : CommRingCat.{0}} {a : Spec R ⟶ Y} (P : Presentations f L R a)
    (ss : List (Finset (Fin m))) : ModuleCat.{0} R :=
  ss.foldr (fun s M ↦ factor P s ⊗ M) (𝟙_ (ModuleCat.{0} R))

/-- The whole local pairing comparison is computed by native scalar
tensor maps and actual factors. -/
def pairingFoldComparison {Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (P : Presentations f L R a) (Q : Presentations f L S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g) :
    (ss : List (Finset (Fin m))) →
      (ModuleCat.extendScalars g.hom).obj (pairingFold P ss) ≅ pairingFold Q ss
  | [] => T.unit
  | s :: ss => T.tensor (factor P s) (pairingFold P ss) ≪≫
    tensorIso (pairingFactorComparison I f L g a a' h P Q C B F T s)
      (pairingFoldComparison f L g a a' h P Q C B F T ss)

/-- The exact scalar pairing transition retains every subset in the original expression. -/
def pairingTransition {Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (P : Presentations f L R a) (Q : Presentations f L S a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g) :
    (ModuleCat.extendScalars g.hom).obj (localPairing P) ≅ localPairing Q :=
  pairingFoldComparison I f L g a a' h P Q C B F T
    (Finset.univ : Finset (Finset (Fin m))).toList

/-- The actual global Deligne algebraic line retains the entire subset determinant expression. -/
structure DeligneLine {Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) (L : Fin (n + 1) → X.Modules)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a) where
  line : Y.Modules
  isLine : CoherentCurveLinearSeries.IsLineBundle line
  affine : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y),
    (Scheme.Modules.pullback a).obj line ≅ (tilde.functor R).obj (localPairing (P R a))
  transition_normalized : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (C : Coherence.{0}) (B : DerivedComparison g) (F : (derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g),
    (Scheme.Modules.pullback (Spec.map g)).map (affine R a).hom ≫
      (AffineCoefficientModules.pullbackTildeIso g).hom.app (localPairing (P R a)) ≫
      (tilde.functor S).map (pairingTransition I f L g a a' h (P R a) (P S a') C B F T).hom =
    (Scheme.Modules.pullbackComp (Spec.map g) a).hom.app line ≫
      (eqToIso (congrArg (fun q : Spec S ⟶ Y => (Scheme.Modules.pullback q).obj line) h)).hom ≫
        (affine S a').hom

end MathlibExt.AlgebraicGeometry.GlobalBoundedDeterminantModels
