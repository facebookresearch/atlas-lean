/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolutionAsphericity
public import MathlibExt.AlgebraicTopology.ModuleResolutionAsphericity
public import Mathlib.Algebra.Category.AlgCat.Basic

/-!
# Additive homology of the canonical polynomial resolution

For any commutative ring k and commutative k-algebra A, forget the canonical augmented
polynomial resolution to k-modules and take normalized Moore chains. The resulting complex
augments to the underlying k-module of A concentrated in degree zero.

The underlying augmentation is a trivial fibration of simplicial sets, and the normalized module
augmentation is a quasi-isomorphism. Thus degree-zero homology is naturally the underlying
k-module of A, and homology in degree n+1 is zero for every n∈ℕ. These constructions are
functorial in k-algebra maps.

The ground-ring universe u and algebra parameter v remain independent; the algebra and module
carriers use the stable height max(u,v).

References: Stacks Project, Sections 92.3–92.4; Loday, Cyclic Homology, 3.5.2–3.5.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- For a commutative ring k, the forgetful functor from commutative k-algebras to k-modules retains
each algebra's underlying additive group and k-scalar action, and sends algebra maps to their
underlying linear maps. -/
def algebraModuleFunctor : CommAlgCat.{max u v} k ⥤ ModuleCat.{max u v} k :=
  forget₂ (CommAlgCat.{max u v} k) (AlgCat.{max u v} k) ⋙
    forget₂ (AlgCat.{max u v} k) (ModuleCat.{max u v} k)

/-- For a commutative ring k, forgetting the canonical polynomial resolution to k-modules gives a
functor from commutative k-algebras to augmented simplicial k-modules. -/
def polynomialAdditiveResolutionFunctor : CommAlgCat.{max u v} k ⥤
    SimplicialObject.Augmented (ModuleCat.{max u v} k) :=
  polynomialResolutionFunctor k ⋙
    (SimplicialObject.Augmented.whiskering (CommAlgCat.{max u v} k)
      (ModuleCat.{max u v} k)).obj (algebraModuleFunctor k)

/-- For a commutative ring k and a commutative k-algebra A, take the canonical augmented polynomial
resolution of A and forget to its underlying augmented simplicial k-module. -/
abbrev polynomialAdditiveResolution (A : CommAlgCat.{max u v} k) :=
  (polynomialAdditiveResolutionFunctor k).obj A

/-- For a commutative ring k and a commutative k-algebra A, the augmented simplicial set underlying
the additive polynomial resolution agrees with the augmented simplicial set underlying the
canonical polynomial algebra resolution. -/
theorem polynomialAdditiveResolution_underlying (A : CommAlgCat.{max u v} k) :
    ModuleResolutionAsphericity.underlying (polynomialAdditiveResolution k A) =
      polynomialResolutionUnderlying k A := rfl

/-- For a commutative ring k and a commutative k-algebra A, the underlying simplicial-set
augmentation of its additive polynomial resolution is a trivial fibration in the Quillen model
structure. -/
theorem polynomialAdditiveResolution_condition (A : CommAlgCat.{max u v} k) :
    trivialFibrations SSet.{max u v}
      (ModuleResolutionAsphericity.underlying (polynomialAdditiveResolution k A)).hom := by
  rw [polynomialAdditiveResolution_underlying]
  exact polynomialResolutionUnderlying_trivialFibration k A

/-- For a commutative ring k, normalize the underlying simplicial k-modules of the canonical
polynomial resolutions. This gives a natural-number-indexed chain-complex functor on commutative
k-algebras. -/
def polynomialAdditiveComplexFunctor : CommAlgCat.{max u v} k ⥤
    ChainComplex (ModuleCat.{max u v} k) ℕ :=
  polynomialAdditiveResolutionFunctor k ⋙ SimplicialObject.Augmented.drop ⋙
    normalizedMooreComplex (ModuleCat.{max u v} k)

/-- For a commutative ring k and a commutative k-algebra A, the normalized additive polynomial
complex augments to the underlying k-module of A concentrated in degree zero, and this
augmentation is a quasi-isomorphism. -/
theorem polynomialAdditiveAugmentation_quasiIso (A : CommAlgCat.{max u v} k) :
    QuasiIso (ModuleResolutionAsphericity.augmentation (polynomialAdditiveResolution k A)) :=
  ModuleResolutionAsphericity.augmentation_quasiIso _ (polynomialAdditiveResolution_condition k A)

/-- For a commutative ring k, degree-zero homology of the normalized additive polynomial-resolution
functor is naturally isomorphic to the underlying-module functor. Its components are induced by
the augmentation to A. -/
def polynomialAdditiveHomologyZeroNatIso :
    polynomialAdditiveComplexFunctor k ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℕ) 0 ≅
        algebraModuleFunctor k :=
  NatIso.ofComponents
    (fun A => ModuleResolutionAsphericity.homologyZeroIso
      (polynomialAdditiveResolution k A) (polynomialAdditiveResolution_condition k A))
    (by
      intro A B g
      exact ModuleResolutionAsphericity.homologyZeroIso_naturality
        ((polynomialAdditiveResolutionFunctor k).map g)
        (polynomialAdditiveResolution_condition k A) (polynomialAdditiveResolution_condition k B))

/-- For a commutative ring k and a commutative k-algebra A, the normalized additive polynomial
resolution has zero homology in degree n+1 for every n∈ℕ. -/
theorem polynomialAdditiveHomology_isZero_positive (A : CommAlgCat.{max u v} k) (n : ℕ) :
    IsZero (((polynomialAdditiveComplexFunctor k).obj A).homology (n + 1)) :=
  ModuleResolutionAsphericity.normalized_homology_isZero_positive
    (polynomialAdditiveResolution k A) (polynomialAdditiveResolution_condition k A) n

end CommAlgCat

end
