/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialSplitting
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitComparison
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialRelativePrism

/-!
# Comparison with the canonical polynomial resolution

The canonical polynomial resolution of a commutative `k`-algebra `A` has a compatible
polynomial splitting and an additively aspherical augmentation. For any augmented
simplicial algebra `P → const A` with these two properties, comparison maps exist in
both directions and their composites are simplicially homotopic to the identities.

Applying degreewise Kähler differentials with coefficients in `A` and normalizing gives
a chain homotopy equivalence with the cotangent complex. Applying a coefficient tensor
functor preserves that equivalence for arbitrary coefficients in an independent universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace CommAlgCat.CanonicalPolynomialResolutionComparison

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The canonical augmented polynomial resolution of `A`, viewed as an object over the
constant simplicial diagram on `A`.
-/
def canonical : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) :=
  (polynomialResolutionOverFunctor.{u, v} k A).obj (Over.mk (𝟙 A))

/--
The compatible polynomial splitting of the canonical augmented resolution of `A`.
-/
def compatibleGenerators : PolynomialSplitting k (canonical k A).left :=
  canonicalPolynomialSplitting.{u, v} k A

/--
The normalized module augmentation of the canonical polynomial resolution is a
quasi-isomorphism.
-/
theorem canonicalAsphericity : additiveResolutionCondition k A (canonical k A) := by
  change QuasiIso (ModuleResolutionAsphericity.augmentation (polynomialAdditiveResolution k A))
  exact polynomialAdditiveAugmentation_quasiIso k A

variable {k A}
  {P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (hP : additiveResolutionCondition k A P)

/--
The augmented-algebra comparison map from a simplicial algebra `P` with compatible
polynomial splitting `s` to the canonical resolution of `A`.
-/
def forward : P ⟶ canonical k A :=
  PolynomialSplitComparison.comparison s (canonicalAsphericity k A)

/--
The augmented-algebra comparison map from the canonical resolution of `A` to `P`,
using additive asphericity `hP` of the target augmentation.
-/
def backward : canonical k A ⟶ P :=
  PolynomialSplitComparison.comparison (compatibleGenerators k A) hP

/--
The simplicial homotopy from the composite `forward s ≫ backward hP` on the augmented
algebra `P` to its identity, obtained from the compatible splitting and additive asphericity.
-/
def forwardBackwardHomotopy :
    SimplicialObject.Homotopy (Over.liftDiagramMap A (forward s ≫ backward hP))
      (Over.liftDiagramMap A (𝟙 P)) :=
  PolynomialRelativePrism.homotopy s (forward s ≫ backward hP) (𝟙 P) hP

/--
The simplicial homotopy from `backward hP ≫ forward s` on the canonical augmented
resolution to its identity.
-/
def backwardForwardHomotopy :
    SimplicialObject.Homotopy (Over.liftDiagramMap A (backward hP ≫ forward s))
      (Over.liftDiagramMap A (𝟙 (canonical k A))) :=
  PolynomialRelativePrism.homotopy (compatibleGenerators k A)
    (backward hP ≫ forward s) (𝟙 (canonical k A)) (canonicalAsphericity k A)

include s hP in
/--
For a compatible polynomial splitting `s` and additive asphericity `hP`, there are
augmented-algebra maps between `P` and the canonical resolution whose two composites
are simplicially homotopic to the respective identities.
-/
theorem exists_relative_homotopy_equivalence :
    ∃ (f : P ⟶ canonical k A) (g : canonical k A ⟶ P),
      Nonempty (SimplicialObject.Homotopy (Over.liftDiagramMap A (f ≫ g))
        (Over.liftDiagramMap A (𝟙 P))) ∧
      Nonempty (SimplicialObject.Homotopy (Over.liftDiagramMap A (g ≫ f))
        (Over.liftDiagramMap A (𝟙 (canonical k A)))) :=
  ⟨forward s, backward hP, ⟨forwardBackwardHomotopy s hP⟩, ⟨backwardForwardHomotopy s hP⟩⟩

/--
The chain homotopy equivalence from the normalized cotangent model of `P` to the
cotangent complex of `A` over `k`, induced by the augmented-algebra comparison maps
and their simplicial homotopies.
-/
def normalizedCotangentHomotopyEquiv : HomotopyEquiv
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).obj (cotangentSimplicial k A P))
    (cotangentComplex k A) where
  hom := (normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A (forward s))
  inv := (normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A (backward hP))
  homotopyHomInvId := by
    let G := cotangentSimplicialFunctor k A ⋙ normalizedMooreComplex (ModuleCat.{max u v} A)
    have H : _root_.Homotopy (G.map (forward s ≫ backward hP)) (G.map (𝟙 P)) :=
      PolynomialRelativePrism.normalizedCotangentHomotopy s (forward s ≫ backward hP) (𝟙 P) hP
    rw [G.map_comp (forward s) (backward hP), G.map_id P] at H
    exact H
  homotopyInvHomId := by
    let G := cotangentSimplicialFunctor k A ⋙ normalizedMooreComplex (ModuleCat.{max u v} A)
    have H : _root_.Homotopy (G.map (backward hP ≫ forward s)) (G.map (𝟙 (canonical k A))) :=
      PolynomialRelativePrism.normalizedCotangentHomotopy (compatibleGenerators k A)
        (backward hP ≫ forward s) (𝟙 (canonical k A)) (canonicalAsphericity k A)
    rw [G.map_comp (backward hP) (forward s), G.map_id (canonical k A)] at H
    exact H

/--
The chain homotopy equivalence obtained by applying `M ⊗[A] −` to the normalized
cotangent comparison, with `M` as first tensor factor in an independent universe.
No flatness or projectivity condition on `M` is needed.
-/
def coefficientHomotopyEquiv (M : ModuleCat.{t} A) : HomotopyEquiv
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        ((normalizedMooreComplex (ModuleCat.{max u v} A)).obj (cotangentSimplicial k A P)))
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (cotangentComplex k A)) :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomotopyEquiv
    (normalizedCotangentHomotopyEquiv s hP)

end CommAlgCat.CanonicalPolynomialResolutionComparison

end
