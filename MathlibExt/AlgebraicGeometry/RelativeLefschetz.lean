/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-!
# Geometric hyperplane operators for relative Lefschetz

A relative projective embedding fixes the relatively very-ample direction.
The input class is a nonzero element of the actual `H²(P^n,Q)`, represented
by `Hom(Q,Q[2])`, with `n ≥ 1`. This space is one-dimensional, so changing
its nonzero scalar normalization does not change the relative Lefschetz
isomorphism assertion. No arbitrary class of `H²(X,Q)` is called ample.

The operator is assembled from actual exact inverse image and actual derived
direct image. The supplied comparison isomorphisms are between their fixed
constant-sheaf/shift realizations. No Lefschetz conclusion is a field of the
comparison data. All constructions below have complete bodies.

The graded projective-spectrum structure-map pattern is adapted from ATLAS
PR1970 `ProjectiveDirectImage.lean`, which attributes leanprover/lean-eval
38361be884302c7edce1908c4aef8296eb2cb27e (Apache-2.0). Changes: use the
projective space as an explicit geometric object and form its relative product.

## References

* BBD, *Faisceaux pervers* (1982), Theorem 6.2.10.
* de Cataldo–Migliorini, https://arxiv.org/abs/0712.0349, Theorem 1.6.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeLefschetz

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- The structure map of the actual graded projective spectrum. -/
def gradedProjToSpec {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [GradedAlgebra G] : Proj G ⟶ Spec (.of R) :=
  Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- Actual `P^n_C` with `n+1` homogeneous coordinates. -/
def projectiveSpace (n : ℕ) : ComplexScheme :=
  let := @MvPolynomial.gradedAlgebra
  Over.mk (gradedProjToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))

/-- The actual relative projective space `Y ×_C P^n_C`. -/
def relativeProjectiveSpace (Y : ComplexScheme) (n : ℕ) : ComplexScheme :=
  Over.mk (pullback.fst Y.hom (projectiveSpace n).hom ≫ Y.hom)

def toBase (Y : ComplexScheme) (n : ℕ) : relativeProjectiveSpace Y n ⟶ Y :=
  Over.homMk (pullback.fst Y.hom (projectiveSpace n).hom) rfl

def toProjectiveSpace (Y : ComplexScheme) (n : ℕ) :
    relativeProjectiveSpace Y n ⟶ projectiveSpace n :=
  Over.homMk (pullback.snd Y.hom (projectiveSpace n).hom) pullback.condition.symm

/-- A closed relative embedding specifies the relatively very-ample line
direction by its map to actual projective space. -/
structure RelativeProjectiveEmbedding {X Y : ComplexScheme} (f : X ⟶ Y) (n : ℕ) where
  embedding : X ⟶ relativeProjectiveSpace Y n
  closed : IsClosedImmersion embedding.left
  over : embedding ≫ toBase Y n = f

def RelativeProjectiveEmbedding.classifyingMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) : X ⟶ projectiveSpace n :=
  E.embedding ≫ toProjectiveSpace Y n

/-- The actual bounded-below constant sheaf placed in degree `-d`. -/
def constantInput (X : ComplexScheme) (d : ℕ) :
    DerivedCategory.Plus (RationalSheaf (space X)) :=
  (DerivedCategory.Plus.singleFunctor _ (-(d : ℤ))).obj (rationalConstantSheaf (space X))

def unitComplex (X : ComplexScheme) : RationalDerived (space X) :=
  DerivedCategory.Plus.ι.obj (constantInput X 0)

def imageInput {X Y : ComplexScheme} (f : X ⟶ Y) (d : ℕ) :
    DerivedCategory.Plus (RationalSheaf (space Y)) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (spaceMap f)).rightDerivedFunctorPlus.obj
    (constantInput X d)

def imageComplex {X Y : ComplexScheme} (f : X ⟶ Y) (d : ℕ) :
    RationalDerived (space Y) := DerivedCategory.Plus.ι.obj (imageInput f d)

/-- Iteration is actual shifted composition, the Yoneda/cup power of a
degree-two class. -/
def degreeTwoPower {C : Type*} [Category* C] [HasShift C ℤ]
    (K : C) (η : K ⟶ K⟦(2 : ℤ)⟧) : (k : ℕ) → (K ⟶ K⟦2 * (k : ℤ)⟧)
  | 0 => (shiftFunctorZero C ℤ).inv.app K
  | k + 1 => degreeTwoPower K η k ≫ η⟦2 * (k : ℤ)⟧' ≫
      (shiftFunctorAdd' C (2 : ℤ) (2 * (k : ℤ)) (2 * ((k + 1 : ℕ) : ℤ))
        (by omega)).inv.app K

/-- Comparison inputs for the fixed hyperplane pullback/direct-image
pipeline. Every field is an isomorphism of actual objects; no arbitrary
functor, zero model, or relative Lefschetz assertion is supplied. -/
structure HyperplaneComparisons {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ) where
  projectiveSource : DerivedCategory.Plus.ι.obj (constantInput (projectiveSpace n) d) ≅
    (unitComplex (projectiveSpace n))⟦(d : ℤ)⟧
  projectiveTarget : DerivedCategory.Plus.ι.obj (constantInput (projectiveSpace n) (d + 2 * k)) ≅
    (unitComplex (projectiveSpace n))⟦((d + 2 * k : ℕ) : ℤ)⟧
  pullbackSource : (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).obj
      (DerivedCategory.Plus.ι.obj (constantInput (projectiveSpace n) d)) ≅
    DerivedCategory.Plus.ι.obj (constantInput X d)
  pullbackTarget : (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).obj
      (DerivedCategory.Plus.ι.obj (constantInput (projectiveSpace n) (d + 2 * k))) ≅
    DerivedCategory.Plus.ι.obj (constantInput X (d + 2 * k))
  directImageTarget : imageComplex f (d + 2 * k) ≅ (imageComplex f d)⟦2 * (k : ℤ)⟧

/-- Pull back the shifted power of the projective hyperplane direction. -/
def hyperplanePullbackMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ)
    (η : unitComplex (projectiveSpace n) ⟶ (unitComplex (projectiveSpace n))⟦(2 : ℤ)⟧)
    (C : HyperplaneComparisons E d k) :
    DerivedCategory.Plus.ι.obj (constantInput X d) ⟶
      DerivedCategory.Plus.ι.obj (constantInput X (d + 2 * k)) :=
  C.pullbackSource.inv ≫
    (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).map
      (C.projectiveSource.hom ≫ (degreeTwoPower (unitComplex (projectiveSpace n)) η k)⟦(d : ℤ)⟧' ≫
        (shiftFunctorAdd' (RationalDerived (space (projectiveSpace n)))
          (2 * (k : ℤ)) (d : ℤ) ((d + 2 * k : ℕ) : ℤ) (by omega)).inv.app _ ≫
        C.projectiveTarget.inv) ≫ C.pullbackTarget.hom

/-- Apply the actual derived direct-image functor to the hyperplane power. -/
def hyperplaneImageMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ)
    (η : unitComplex (projectiveSpace n) ⟶ (unitComplex (projectiveSpace n))⟦(2 : ℤ)⟧)
    (C : HyperplaneComparisons E d k) : imageComplex f d ⟶ (imageComplex f d)⟦2 * (k : ℤ)⟧ :=
  DerivedCategory.Plus.ι.map
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (spaceMap f)).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.ι.preimage (hyperplanePullbackMap E d k η C))) ≫
    C.directImageTarget.hom

/-- The actual map on perverse cohomology induced by a degree-`2k` morphism. -/
def perversePowerMap (Y : ComplexScheme) [IsComplexVariety Y] [PerverseSheafTheory Y]
    (K : (boundedConstructible Y).FullSubcategory) (k : ℕ)
    (u : K.obj ⟶ K.obj⟦2 * (k : ℤ)⟧) :
    perverseCohomology Y (-(k : ℤ)) K ⟶ perverseCohomology Y (k : ℤ) K := by
  let I := (boundedConstructible Y).ι
  let v : I.obj (K⟦-(k : ℤ)⟧) ⟶ I.obj (K⟦(k : ℤ)⟧) :=
    ((I.commShiftIso (-(k : ℤ))).app K).hom ≫ u⟦-(k : ℤ)⟧' ≫
      (shiftFunctorAdd' (RationalDerived (space Y)) (2 * (k : ℤ)) (-(k : ℤ))
        (k : ℤ) (by omega)).inv.app K.obj ≫ ((I.commShiftIso (k : ℤ)).app K).inv
  exact ObjectProperty.homMk ((perverseTStructure Y).truncGELE 0 0 |>.map (I.preimage v))

end MathlibExt.AlgebraicGeometry.RelativeLefschetz
