/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

/-!
# Geometric hyperplane operators for relative Lefschetz

A relative projective embedding `X ⟶ Y ×_ℂ ℙⁿ` over `Y` fixes the relatively
very ample direction. The input class is a nonzero element of the actual
`H²(ℙⁿ, ℚ)`, represented by `Hom(ℚ, ℚ[2])`, with `n ≥ 1`. This space is
one-dimensional, so changing its nonzero scalar normalization does not change
the relative Lefschetz isomorphism assertion. No arbitrary class of
`H²(X, ℚ)` is called ample.

The operator is assembled from the actual exact inverse image and the actual
derived direct image `ConstructibleComplexes.normalizedDirectImage`. The
supplied comparison isomorphisms identify their constant-sheaf and shift
realizations; changing them composes the perverse power map with isomorphisms
on both sides, so whether it is an isomorphism does not depend on them. No
Lefschetz conclusion is a field of the comparison data. All constructions
below are complete.

## References

* A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982), Theorem 6.2.10.
* M. A. de Cataldo and L. Migliorini, https://arxiv.org/abs/0712.0349,
  Theorem 1.6.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeLefschetz

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- The actual relative projective space `Y ×_ℂ ℙⁿ_ℂ`. -/
def relativeProjectiveSpace (Y : ComplexScheme) (n : ℕ) : ComplexScheme :=
  Over.mk (pullback.fst Y.hom (ProjectiveSpace.projectiveSpace ℂ n).hom ≫ Y.hom)

/-- The projection of the relative projective space to the base. -/
def toBase (Y : ComplexScheme) (n : ℕ) : relativeProjectiveSpace Y n ⟶ Y :=
  Over.homMk (pullback.fst Y.hom (ProjectiveSpace.projectiveSpace ℂ n).hom) rfl

/-- The projection of the relative projective space to `ℙⁿ_ℂ`. -/
def toProjectiveSpace (Y : ComplexScheme) (n : ℕ) :
    relativeProjectiveSpace Y n ⟶ ProjectiveSpace.projectiveSpace ℂ n :=
  Over.homMk (pullback.snd Y.hom (ProjectiveSpace.projectiveSpace ℂ n).hom) pullback.condition.symm

/-- A closed relative embedding specifies the relatively very-ample line
direction by its map to actual projective space. -/
structure RelativeProjectiveEmbedding {X Y : ComplexScheme} (f : X ⟶ Y) (n : ℕ) where
  /-- The embedding into the relative projective space. -/
  embedding : X ⟶ relativeProjectiveSpace Y n
  /-- It is a closed immersion. -/
  closed : IsClosedImmersion embedding.left
  /-- It lies over `Y`. -/
  over : embedding ≫ toBase Y n = f

/-- The map to `ℙⁿ_ℂ` given by a relative projective embedding. -/
def RelativeProjectiveEmbedding.classifyingMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) : X ⟶ ProjectiveSpace.projectiveSpace ℂ n :=
  E.embedding ≫ toProjectiveSpace Y n

/-- The actual bounded-below constant sheaf placed in degree `-d`. -/
def constantInput (X : ComplexScheme) (d : ℕ) :
    DerivedCategory.Plus (RationalSheaf (space X)) :=
  (DerivedCategory.Plus.singleFunctor _ (-(d : ℤ))).obj (rationalConstantSheaf (space X))

/-- The rational constant sheaf in degree zero, in the derived category. -/
def unitComplex (X : ComplexScheme) : RationalDerived (space X) :=
  DerivedCategory.Plus.ι.obj (constantInput X 0)

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
  /-- `ℚ[d]` on `ℙⁿ` in its two presentations. -/
  projectiveSource : DerivedCategory.Plus.ι.obj (constantInput (ProjectiveSpace.projectiveSpace ℂ n) d) ≅
    (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦(d : ℤ)⟧
  /-- `ℚ[d + 2k]` on `ℙⁿ` in its two presentations. -/
  projectiveTarget : DerivedCategory.Plus.ι.obj (constantInput (ProjectiveSpace.projectiveSpace ℂ n) (d + 2 * k)) ≅
    (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦((d + 2 * k : ℕ) : ℤ)⟧
  /-- The inverse image of `ℚ[d]` on `ℙⁿ` is `ℚ[d]` on `X`. -/
  pullbackSource : (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).obj
      (DerivedCategory.Plus.ι.obj (constantInput (ProjectiveSpace.projectiveSpace ℂ n) d)) ≅
    DerivedCategory.Plus.ι.obj (constantInput X d)
  /-- The inverse image of `ℚ[d + 2k]` on `ℙⁿ` is `ℚ[d + 2k]` on `X`. -/
  pullbackTarget : (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).obj
      (DerivedCategory.Plus.ι.obj (constantInput (ProjectiveSpace.projectiveSpace ℂ n) (d + 2 * k))) ≅
    DerivedCategory.Plus.ι.obj (constantInput X (d + 2 * k))
  /-- `Rf_* ℚ[d + 2k]` is `Rf_* ℚ[d]` shifted by `2k`. -/
  directImageTarget : ConstructibleComplexes.normalizedDirectImage ℚ X Y f (d + 2 * k) ≅
    (ConstructibleComplexes.normalizedDirectImage ℚ X Y f d)⟦2 * (k : ℤ)⟧

/-- Pull back the shifted power of the projective hyperplane direction. -/
def hyperplanePullbackMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ)
    (η : unitComplex (ProjectiveSpace.projectiveSpace ℂ n) ⟶ (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦(2 : ℤ)⟧)
    (C : HyperplaneComparisons E d k) :
    DerivedCategory.Plus.ι.obj (constantInput X d) ⟶
      DerivedCategory.Plus.ι.obj (constantInput X (d + 2 * k)) :=
  C.pullbackSource.inv ≫
    (ConstructibleComplexes.derivedPullback ℚ (spaceMap E.classifyingMap)).map
      (C.projectiveSource.hom ≫
        (degreeTwoPower (unitComplex (ProjectiveSpace.projectiveSpace ℂ n)) η k)⟦(d : ℤ)⟧' ≫
        (shiftFunctorAdd' (RationalDerived (space (ProjectiveSpace.projectiveSpace ℂ n)))
          (2 * (k : ℤ)) (d : ℤ) ((d + 2 * k : ℕ) : ℤ) (by omega)).inv.app _ ≫
        C.projectiveTarget.inv) ≫ C.pullbackTarget.hom

/-- Apply the actual derived direct-image functor to the hyperplane power. -/
def hyperplaneImageMap {X Y : ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) (d k : ℕ)
    (η : unitComplex (ProjectiveSpace.projectiveSpace ℂ n) ⟶ (unitComplex (ProjectiveSpace.projectiveSpace ℂ n))⟦(2 : ℤ)⟧)
    (C : HyperplaneComparisons E d k) :
    ConstructibleComplexes.normalizedDirectImage ℚ X Y f d ⟶
      (ConstructibleComplexes.normalizedDirectImage ℚ X Y f d)⟦2 * (k : ℤ)⟧ :=
  (ConstructibleComplexes.derivedPushforwardPlus ℚ f).map
      (DerivedCategory.Plus.ι.preimage (hyperplanePullbackMap E d k η C)) ≫
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
