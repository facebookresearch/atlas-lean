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
* `StacksFrontier/Homology/TwoTermComplex/DeterminantFunctor.lean`

Modifications: native finite-projective cochain complexes on every affine test scheme, the
native derived tilde and scheme pullback, and the source's local presentation criterion for
perfect Tor amplitude [-1,0] are used.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules
public import MathlibExt.AlgebraicGeometry.TwoTermDeterminantFunctors

/-!
# Actual affine presentations for the global scheme determinant

Every affine test `u : Spec R -> X` has a genuine finite-projective complex
whose native derived tilde is the actual `Lu^*K`. The local derived object
is constructed from that complex by the native quotient. Its determinant
is the actual presentation determinant, with comparison to every other
presentation supplied by the completed source-normalized functor.

This is the affine criterion for perfect Tor amplitude [-1,0]. It records
all affine test schemes, including nonreduced ones and nonflat base maps.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeDeterminantPresentations

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FourierMukai TwoTermDeterminantModels TwoTermDeterminantFunctors
open AffineDerivedCoefficientModules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- An actual finite-projective complex supported in degrees -1 and 0. -/
structure LocalComplex (R : CommRingCat.{u}) where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  finite : ∀ i : ℤ, Module.Finite R (complex.X i)
  projective : ∀ i : ℤ, Module.Projective R (complex.X i)
  strictlyGE : complex.IsStrictlyGE (-1)
  strictlyLE : complex.IsStrictlyLE 0

/-- The actual local derived object, computed by the native quotient. -/
def LocalComplex.derivedObject {R : CommRingCat.{u}} (P : LocalComplex R) :
    DerivedCategory (ModuleCat.{u} R) := DerivedCategory.Q.obj P.complex

/-- Its actual presenting complex and identity comparison. -/
def LocalComplex.presentation {R : CommRingCat.{u}} (P : LocalComplex R) :
    Presentation P.derivedObject :=
  ⟨P.complex, P.finite, P.projective, P.strictlyGE, P.strictlyLE, Iso.refl _⟩

/-- The actual full-category object has the finite-projective criterion just proved. -/
def LocalComplex.perfectObject {R : CommRingCat.{u}} (P : LocalComplex R) :
    PerfectTwoTerm R := ⟨P.derivedObject, ⟨P.presentation⟩⟩

/-- The local determinant module is the literal determinant of these terms. -/
abbrev LocalComplex.determinant {R : CommRingCat.{u}} (P : LocalComplex R) :=
  presentationDeterminant P.presentation

variable [HasDerivedPullbacks.{u}]
  [∀ R : CommRingCat.{u}, PreservesFiniteLimits (tilde.functor R)]

/-- A genuine affine avatar of the specified global derived object. -/
structure AffinePresentation {X : Scheme.{u}} (K : FourierMukai.D X)
    {R : CommRingCat.{u}} (a : Spec R ⟶ X) where
  localComplex : LocalComplex R
  comparison : (derivedTilde R).obj localComplex.derivedObject ≅ (derivedPullback a).obj K

/-- The complete affine criterion for the global perfect two-term scope. -/
def IsPerfectTwoTermOn {X : Scheme.{u}} (K : FourierMukai.D X) : Prop :=
  ∀ (R : CommRingCat.{u}) (a : Spec R ⟶ X), Nonempty (AffinePresentation K a)

/-- The actual full subcategory on the scheme, with every affine test retained. -/
abbrev SchemePerfectTwoTerm (X : Scheme.{u}) :=
  (show ObjectProperty (FourierMukai.D X) from IsPerfectTwoTermOn).FullSubcategory

/-- Actual native determinant value of an affine presentation. -/
def affineDeterminant {X : Scheme.{u}} {K : FourierMukai.D X}
    {R : CommRingCat.{u}} {a : Spec R ⟶ X} (P : AffinePresentation K a)
    (S : TransportSystem R) : ModuleCat.{u} R :=
  (determinantFunctor S).obj ⟨P.localComplex.perfectObject⟩

/-- Its canonical source-normalized comparison to the literal term determinant. -/
def affineDeterminantIso {X : Scheme.{u}} {K : FourierMukai.D X}
    {R : CommRingCat.{u}} {a : Spec R ⟶ X} (P : AffinePresentation K a)
    (S : TransportSystem R) : affineDeterminant P S ≅ ModuleCat.of R P.localComplex.determinant :=
  presentationIso S ⟨P.localComplex.perfectObject⟩ P.localComplex.presentation

end MathlibExt.AlgebraicGeometry.SchemeDeterminantPresentations
