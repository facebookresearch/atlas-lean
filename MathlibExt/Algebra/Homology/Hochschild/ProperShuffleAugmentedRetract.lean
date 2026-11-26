/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AugmentedHochschildCoefficients
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleEulerianNaturality
public import MathlibExt.AlgebraicTopology.AugmentedChainTotal
public import Mathlib.CategoryTheory.Retract

/-!
# Rational retractions of augmented proper-shuffle diagrams

Let `k` be a commutative `ℚ`-algebra, `B` a commutative `k`-algebra, and `M` a compatible
`B`-module. For each augmentation `P → B`, quotient Hochschild chains by shuffle products with
both factors of positive degree. The rational Eulerian section splits this quotient projection
naturally in maps over `B`.

Restricting the chain index along `n ↦ n+1` gives the corresponding positive-degree functors
and their retraction. For an augmented simplicial algebra, the section and projection also
preserve the augmentation to the identity-augmented algebra `B`. They therefore give a retract
of augmented chain diagrams and an arrow retract of their total augmentations. The coefficient
carrier universe is independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

attribute [local instance] coefficientModule coefficientCommutes coefficientTower

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- The proper-shuffle quotient functor in all chain degrees.

For `P → B`, take the quotient by both-positive shuffle relations with coefficients `M`,
retaining degree zero before any positive-index restriction. -/
def fullQuotientFunctor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ where
  obj P := positiveQuotient k P.left M
  map f := chainMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M f)
  map_id P := by
    change chainMap k (AlgHom.id k P.left) (LinearMap.id : M →ₗ[k] M) _ = 𝟙 (positiveQuotient k P.left M)
    exact chainMap_id k
  map_comp {P Q S} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change quotientLinearMap k (g.left.hom.comp f.left.hom) (LinearMap.id : M →ₗ[k] M) n =
      (quotientLinearMap k g.left.hom (LinearMap.id : M →ₗ[k] M) n).comp
        (quotientLinearMap k f.left.hom (LinearMap.id : M →ₗ[k] M) n)
    exact (by simpa only [LinearMap.id_comp] using
      (quotientLinearMap_comp k f.left.hom g.left.hom (LinearMap.id : M →ₗ[k] M)
        (LinearMap.id : M →ₗ[k] M) n).symm)

/-- The natural full proper-shuffle quotient projection.

The quotient maps from coefficient Hochschild complexes to their proper-shuffle quotients form
a natural transformation on `Over B`. -/
def fullProjectionNat : AugmentedCoefficients.functor k B M ⟶ fullQuotientFunctor k B M where
  app P := properShuffleProjection k P.left M
  naturality {_P _Q} f := (chainMap_projection k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)).symm

/-- The natural Eulerian section of full proper-shuffle quotients.

Over the rational ground algebra, the Eulerian sections form a natural transformation from
proper quotients to coefficient Hochschild complexes. -/
def fullSectionNat : fullQuotientFunctor k B M ⟶ AugmentedCoefficients.functor k B M where
  app P := properEulerianSection k P.left M
  naturality {_P _Q} f := section_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- The proper-shuffle functor as a Hochschild functor retract.

The natural Eulerian section followed by the natural quotient projection is the identity on
the proper-shuffle quotient functor. -/
def fullFunctorRetract : Retract (fullQuotientFunctor k B M) (AugmentedCoefficients.functor k B M) where
  i := fullSectionNat k B M
  r := fullProjectionNat k B M
  retract := by
    apply NatTrans.ext
    funext P
    change properEulerianSection k P.left M ≫ properShuffleProjection k P.left M = 𝟙 (positiveQuotient k P.left M)
    exact properEulerianSection_projection k P.left M

/-- The positive-index Hochschild functor on augmented algebras.

Restrict the coefficient Hochschild chain functor along `n ↦ n+1`, so its displayed degree `n`
is full Hochschild degree `n+1`. -/
def positiveHochschildFunctor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  AugmentedCoefficients.functor k B M ⋙
    ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)

/-- The positive-index proper-shuffle quotient functor.

Restrict the full proper-shuffle quotient functor along the same embedding `n ↦ n+1`. -/
def positiveQuotientFunctor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  fullQuotientFunctor k B M ⋙
    ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)

/-- The natural quotient projection after positive-index restriction.

Restrict the full proper-shuffle projection degreewise along `n ↦ n+1`. -/
def positiveProjectionNat : positiveHochschildFunctor k B M ⟶ positiveQuotientFunctor k B M :=
  Functor.whiskerRight (fullProjectionNat k B M)
    (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k))

/-- The natural Eulerian section after positive-index restriction.

Restrict the full Eulerian section degreewise along `n ↦ n+1`. -/
def positiveSectionNat : positiveQuotientFunctor k B M ⟶ positiveHochschildFunctor k B M :=
  Functor.whiskerRight (fullSectionNat k B M)
    (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k))

/-- The positive proper-shuffle functor as a positive Hochschild retract.

Positive-index restriction carries the full section–projection retraction to a retraction of
the corresponding positive chain functors. -/
def positiveFunctorRetract : Retract (positiveQuotientFunctor k B M) (positiveHochschildFunctor k B M) :=
  (fullFunctorRetract k B M).map
    ((CategoryTheory.Functor.whiskeringRight (Over B)
      (ChainComplex (ModuleCat.{max u v w} k) ℕ) (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
        (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)))

/-- The terminal algebra in an augmented proper-shuffle diagram.

The terminal object of `Over B` is the identity augmentation `B → B`. -/
abbrev terminal : Over B := AugmentedCoefficients.terminalAlgebra k B

/-- The natural augmentation of positive Hochschild chain diagrams.

Maps `P → B` induce a natural transformation from the positive Hochschild functor to its
constant value at the identity augmentation of `B`. -/
def positiveHochschildAugmentationNat : positiveHochschildFunctor k B M ⟶
    (CategoryTheory.Functor.const (Over B)).obj ((positiveHochschildFunctor k B M).obj (terminal k B)) where
  app P := (positiveHochschildFunctor k B M).map (AugmentedCoefficients.toTerminal k B P)
  naturality {P Q} f := by
    change (positiveHochschildFunctor k B M).map f ≫
        (positiveHochschildFunctor k B M).map (AugmentedCoefficients.toTerminal k B Q) =
      (positiveHochschildFunctor k B M).map (AugmentedCoefficients.toTerminal k B P) ≫ 𝟙 _
    exact ((positiveHochschildFunctor k B M).map_comp _ _).symm.trans
      ((congrArg (positiveHochschildFunctor k B M).map (AugmentedCoefficients.toTerminal_naturality k B f)).trans
        (Category.comp_id _).symm)

/-- The natural augmentation of positive proper-shuffle chain diagrams.

Maps `P → B` induce a natural transformation from the positive quotient functor to its
constant value at the identity augmentation of `B`. -/
def positiveQuotientAugmentationNat : positiveQuotientFunctor k B M ⟶
    (CategoryTheory.Functor.const (Over B)).obj ((positiveQuotientFunctor k B M).obj (terminal k B)) where
  app P := (positiveQuotientFunctor k B M).map (AugmentedCoefficients.toTerminal k B P)
  naturality {P Q} f := by
    change (positiveQuotientFunctor k B M).map f ≫
        (positiveQuotientFunctor k B M).map (AugmentedCoefficients.toTerminal k B Q) =
      (positiveQuotientFunctor k B M).map (AugmentedCoefficients.toTerminal k B P) ≫ 𝟙 _
    exact ((positiveQuotientFunctor k B M).map_comp _ _).symm.trans
      ((congrArg (positiveQuotientFunctor k B M).map (AugmentedCoefficients.toTerminal_naturality k B f)).trans
        (Category.comp_id _).symm)

/-- The augmented simplicial diagram of positive Hochschild complexes.

For `P_• → B`, apply the positive Hochschild functor in every simplicial degree and augment to
its value at `id_B`. -/
def positiveHochschildAugmented
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject.Augmented (ChainComplex (ModuleCat.{max u v w} k) ℕ) where
  left := Over.lift P.left P.hom ⋙ positiveHochschildFunctor k B M
  right := (positiveHochschildFunctor k B M).obj (terminal k B)
  hom := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveHochschildAugmentationNat k B M)

/-- The augmented simplicial diagram of positive proper-shuffle complexes.

For `P_• → B`, apply the positive proper-shuffle quotient functor degreewise and augment to
its value at `id_B`. -/
def positiveQuotientAugmented
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject.Augmented (ChainComplex (ModuleCat.{max u v w} k) ℕ) where
  left := Over.lift P.left P.hom ⋙ positiveQuotientFunctor k B M
  right := (positiveQuotientFunctor k B M).obj (terminal k B)
  hom := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveQuotientAugmentationNat k B M)

/-- The Eulerian section of augmented positive chain diagrams.

The natural positive section gives a map from the augmented proper-shuffle diagram to the
augmented Hochschild diagram, preserving their terminal augmentations. -/
def positiveAugmentedSection
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    positiveQuotientAugmented k B M P ⟶ positiveHochschildAugmented k B M P where
  left := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveSectionNat k B M)
  right := (positiveSectionNat k B M).app (terminal k B)
  w := by
    apply NatTrans.ext
    funext i
    exact ((positiveSectionNat k B M).naturality
      (AugmentedCoefficients.toTerminal k B ((Over.lift P.left P.hom).obj i))).symm

/-- The quotient projection of augmented positive chain diagrams.

The natural positive projection gives a map from the augmented Hochschild diagram to the
augmented proper-shuffle diagram, preserving their terminal augmentations. -/
def positiveAugmentedProjection
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    positiveHochschildAugmented k B M P ⟶ positiveQuotientAugmented k B M P where
  left := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveProjectionNat k B M)
  right := (positiveProjectionNat k B M).app (terminal k B)
  w := by
    apply NatTrans.ext
    funext i
    exact ((positiveProjectionNat k B M).naturality
      (AugmentedCoefficients.toTerminal k B ((Over.lift P.left P.hom).obj i))).symm

/-- The augmented proper-shuffle diagram as a Hochschild retract.

The augmented Eulerian section and quotient projection exhibit the positive proper-shuffle
diagram as a retract of the positive Hochschild diagram. -/
def positiveAugmentedRetract
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    Retract (positiveQuotientAugmented k B M P) (positiveHochschildAugmented k B M P) where
  i := positiveAugmentedSection k B M P
  r := positiveAugmentedProjection k B M P
  retract := by
    apply Comma.hom_ext
    · apply NatTrans.ext
      funext i
      exact congrArg (fun t => t.app ((Over.lift P.left P.hom).obj i))
        (positiveFunctorRetract k B M).retract
    · exact congrArg (fun t => t.app (terminal k B)) (positiveFunctorRetract k B M).retract

/-- The arrow retract of positive proper-shuffle total augmentation.

Taking augmented chain totals carries the augmented-diagram retraction to an arrow retract of
the proper-shuffle total augmentation inside the positive Hochschild total augmentation. -/
def positiveTotalAugmentationRetract
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    RetractArrow
      ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveQuotientAugmented k B M P))
      ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveHochschildAugmented k B M P)) :=
  augmentedChainTotalAugmentation_retract (ModuleCat.{max u v w} k) (positiveAugmentedRetract k B M P)

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
