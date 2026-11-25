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
# Retractions of augmented proper-shuffle diagrams

Over a rational ground algebra, the
proper quotient projection and Eulerian
section are natural in coefficient
and algebra maps. They give a split
pair of augmented chain diagrams,
also after positive-index restriction.
The coefficient module is arbitrary.
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

/-- The original full proper quotient functor, before the native positive-index restriction. -/
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

/-- The original quotient projection is a natural transformation of the original Over-algebra functors. -/
def fullProjectionNat : AugmentedCoefficients.functor k B M ⟶ fullQuotientFunctor k B M where
  app P := properShuffleProjection k P.left M
  naturality {_P _Q} f := (chainMap_projection k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)).symm

/-- The Eulerian section is natural for all original algebra operators. -/
def fullSectionNat : fullQuotientFunctor k B M ⟶ AugmentedCoefficients.functor k B M where
  app P := properEulerianSection k P.left M
  naturality {_P _Q} f := section_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- The source functor is a native retract, with the original section and projection. -/
def fullFunctorRetract : Retract (fullQuotientFunctor k B M) (AugmentedCoefficients.functor k B M) where
  i := fullSectionNat k B M
  r := fullProjectionNat k B M
  retract := by
    apply NatTrans.ext
    funext P
    change properEulerianSection k P.left M ≫ properShuffleProjection k P.left M = 𝟙 (positiveQuotient k P.left M)
    exact properEulerianSection_projection k P.left M

/-- Restricting the original Hochschild functor uses the same positive-index embedding
as the proper cotangent complex. -/
def positiveHochschildFunctor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  AugmentedCoefficients.functor k B M ⋙
    ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)

/-- The original quotient functor after the same native positive-index restriction. -/
def positiveQuotientFunctor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  fullQuotientFunctor k B M ⋙
    ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)

/-- The positive projection retains the original quotient maps. -/
def positiveProjectionNat : positiveHochschildFunctor k B M ⟶ positiveQuotientFunctor k B M :=
  Functor.whiskerRight (fullProjectionNat k B M)
    (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k))

/-- The positive section retains the original Eulerian section. -/
def positiveSectionNat : positiveQuotientFunctor k B M ⟶ positiveHochschildFunctor k B M :=
  Functor.whiskerRight (fullSectionNat k B M)
    (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k))

/-- The original positive quotient is a native retract of the original positive Hochschild diagram. -/
def positiveFunctorRetract : Retract (positiveQuotientFunctor k B M) (positiveHochschildFunctor k B M) :=
  (fullFunctorRetract k B M).map
    ((CategoryTheory.Functor.whiskeringRight (Over B)
      (ChainComplex (ModuleCat.{max u v w} k) ℕ) (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
        (ComplexShape.positiveNatEmbedding.restrictionFunctor (ModuleCat.{max u v w} k)))

/-- The terminal point is the original coefficient algebra with the identity augmentation. -/
abbrev terminal : Over B := AugmentedCoefficients.terminalAlgebra k B

/-- Original algebra augmentations supply the positive Hochschild augmentation at every source algebra. -/
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

/-- Original algebra augmentations supply the positive proper-quotient augmentation. -/
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

/-- The augmented positive Hochschild chain diagram of an original simplicial algebra. -/
def positiveHochschildAugmented
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject.Augmented (ChainComplex (ModuleCat.{max u v w} k) ℕ) where
  left := Over.lift P.left P.hom ⋙ positiveHochschildFunctor k B M
  right := (positiveHochschildFunctor k B M).obj (terminal k B)
  hom := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveHochschildAugmentationNat k B M)

/-- The augmented positive proper-quotient chain diagram of the same original simplicial algebra. -/
def positiveQuotientAugmented
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject.Augmented (ChainComplex (ModuleCat.{max u v w} k) ℕ) where
  left := Over.lift P.left P.hom ⋙ positiveQuotientFunctor k B M
  right := (positiveQuotientFunctor k B M).obj (terminal k B)
  hom := Functor.whiskerLeft (Over.lift P.left P.hom) (positiveQuotientAugmentationNat k B M)

/-- The original natural section is an morphism of the original augmented positive diagrams. -/
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

/-- The original natural projection is an morphism of the same original augmented positive diagrams. -/
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

/-- The original positive proper diagram is a computed native retract as an augmented diagram. -/
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

/-- The augmented proper-shuffle total arrow is a native retract
of the positive Hochschild total arrow. -/
def positiveTotalAugmentationRetract
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    RetractArrow
      ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveQuotientAugmented k B M P))
      ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveHochschildAugmented k B M P)) :=
  augmentedChainTotalAugmentation_retract (ModuleCat.{max u v w} k) (positiveAugmentedRetract k B M P)

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
