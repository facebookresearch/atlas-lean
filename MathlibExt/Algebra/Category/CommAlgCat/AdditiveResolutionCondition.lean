/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModuleAsphericityNativeCondition
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolutionAdditiveAsphericity
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentResolutionFunctor

/-!
# Additive asphericity of augmented simplicial algebras

For a commutative ring `k`, let `Q → const A` be an augmented simplicial commutative
`k`-algebra. Its underlying module augmentation induces a map of normalized Moore
complexes. The additive resolution condition says that this map is a quasi-isomorphism;
it is equivalent to the trivial-fibration condition on the underlying simplicial sets.

A polynomial cotangent resolution is an augmentation satisfying this condition together
with a polynomial presentation in every simplicial degree. The ground-ring universe and
the algebra-carrier universe are independent.

For polynomial resolutions and the cotangent complex, see Loday, §3.5.3, and the Stacks
Project, §§92.3–92.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The augmented simplicial algebra with diagram `Q.left`, target `A`, and augmentation
`Q.hom`, for `Q` in the over category of the constant diagram on `A`.
-/
def augmentedAlgebraOfOver
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject.Augmented (CommAlgCat.{max u v} k) where
  left := Q.left
  right := A
  hom := Q.hom

/--
The augmented simplicial `k`-module obtained from `Q → const A` by forgetting the
algebra structure in every degree and on the augmentation.
-/
def additiveAugmentedResolution
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject.Augmented (ModuleCat.{max u v} k) :=
  ((SimplicialObject.Augmented.whiskering (CommAlgCat.{max u v} k)
    (ModuleCat.{max u v} k)).obj (algebraModuleFunctor k)).obj (augmentedAlgebraOfOver k A Q)

/--
The additive asphericity condition on `Q → const A`: the induced normalized module
augmentation is a quasi-isomorphism.
-/
def additiveResolutionCondition
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) : Prop :=
  QuasiIso (ModuleResolutionAsphericity.augmentation (additiveAugmentedResolution k A Q))

/--
For an augmented simplicial algebra `Q → const A`, the trivial-fibration condition on
the underlying simplicial sets is equivalent to the quasi-isomorphism condition on its
normalized module augmentation.
-/
theorem polynomialCotangentResolutionCondition_iff_additive
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentResolutionCondition k A Q ↔ additiveResolutionCondition k A Q := by
  change trivialFibrations SSet.{max u v}
    (ModuleResolutionAsphericity.underlying (additiveAugmentedResolution k A Q)).hom ↔
      QuasiIso (ModuleResolutionAsphericity.augmentation (additiveAugmentedResolution k A Q))
  exact ModuleResolutionAsphericity.underlying_trivialFibration_iff_additive_asphericity
    (additiveAugmentedResolution k A Q)

/--
An augmentation is a polynomial cotangent resolution exactly when every degree admits
a polynomial presentation and its normalized module augmentation is a quasi-isomorphism.
The variable type in each presentation may depend on the degree.
-/
theorem polynomialCotangentResolutionObjects_iff_additive
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    polynomialCotangentResolutionObjects k A Q ↔
      (∀ n : ℕ, ∃ σ : Type (max u v),
        Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (Opposite.op ⦋n⦌))) ∧
          additiveResolutionCondition k A Q := by
  exact and_congr_right (fun _ => polynomialCotangentResolutionCondition_iff_additive k A Q)

/--
The polynomial cotangent resolution determined by degreewise polynomial presentations
`hpoly` and additive asphericity `hadd` of the augmentation `Q → const A`.
-/
def polynomialCotangentResolutionOfAdditive
    (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (hpoly : ∀ n : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (Opposite.op ⦋n⦌)))
    (hadd : additiveResolutionCondition k A Q) : PolynomialCotangentResolutions k A :=
  ⟨Q, hpoly, (polynomialCotangentResolutionCondition_iff_additive k A Q).mpr hadd⟩

end CommAlgCat

end
