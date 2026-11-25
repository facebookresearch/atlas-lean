/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleConstantDerivedModels
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Field Galois operators on actual geometric stalk cohomology

The geometric field is the actual algebraic closure. Every operator uses
the actual spectrum map of its Galois automorphism, the native derived
restriction and the normalized pullback composition comparison. Thus the
coefficient module and each Galois operator are fixed by the original
generic-field sheaf complex.

Group-law adapters are construction requests on these exact operators.
Finite Galois descent and ramification data can be supplied separately;
no representation space or Swan value is given as arbitrary data.

Sources: Saito, arXiv:1510.03018v4, Sections 1.1 and 1.3;
the field étale/Galois comparison of AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleGaloisStalkActions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AdicDerivedContracts CotangentBundleTestModels EtaleLocalAcyclicityModels

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]
  (K : Type) [Field K]

def closureField : GeometricField := ⟨AlgebraicClosure K⟩

def closurePoint : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

def deck (g : Field.absoluteGaloisGroup K) :
    Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of (AlgebraicClosure K)) :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

theorem deck_over (g : Field.absoluteGaloisGroup K) :
    deck K g ≫ closurePoint K = closurePoint K := by
  rw [deck, closurePoint, ← Spec.map_comp]
  congr 1
  ext a
  exact g.commutes a

variable (F : Derived Λ (Spec (.of K)))

def fieldStalk : DerivedCategory.Plus (ModuleCat.{1} Λ) :=
  geometricStalk Λ (closureField K) (closurePoint K) F

def deckPullbackIso (g : Field.absoluteGaloisGroup K) :
    derivedPullback Λ (closurePoint K) ⋙ derivedPullback Λ (deck K g) ≅
      derivedPullback Λ (closurePoint K) :=
  (DerivedPullbackPasting.comparison (R := Λ) (f := deck K g) (g := closurePoint K)) ≪≫
    eqToIso (congrArg (derivedPullback Λ) (deck_over K g))

/-- The actual derived Galois operator on the original field-sheaf stalk. -/
def deckOperator (g : Field.absoluteGaloisGroup K) :
    fieldStalk Λ K F ⟶ fieldStalk Λ K F :=
  globalRestriction Λ (deck K g) ((derivedPullback Λ (closurePoint K)).obj F) ≫
    (derivedSections Λ (Spec (.of (AlgebraicClosure K)))).map
      ((deckPullbackIso Λ K g).hom.app F)

def cohomology (q : ℤ) : ModuleCat.{1} Λ :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} Λ) q).obj (fieldStalk Λ K F)

/-- Each cohomological operator is the homology of that exact derived operator. -/
def cohomologyOperator (q : ℤ) (g : Field.absoluteGaloisGroup K) :
    Module.End Λ (cohomology Λ K F q) :=
  ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{1} Λ) q).map
    (deckOperator Λ K F g)).hom

/-- A group-law adapter has the fixed actual cohomology module and every
native Galois operator as its normalization. -/
structure SourceAction (q : ℤ) where
  action : Field.absoluteGaloisGroup K →* Module.End Λ (cohomology Λ K F q)
  normalized : ∀ g, action g = cohomologyOperator Λ K F q g

end MathlibExt.AlgebraicGeometry.EtaleGaloisStalkActions
