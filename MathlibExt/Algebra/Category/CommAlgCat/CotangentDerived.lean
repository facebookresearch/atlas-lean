/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Polynomial cotangent models in the derived category

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. For an algebra over
`A`, its normalized polynomial cotangent chain model extends to an integer-indexed cochain
complex along `n ↦ -n`, with zero terms in positive cochain degrees. This extension is
functorial on `Over A`.

With `HasDerivedCategory.{w} (ModuleCat.{max u v} A)`, applying the localization functor
`DerivedCategory.Q` gives a functor to the derived category. At the identity object `A → A`,
it defines `cotangentDerived k A`. The localization universe `w` is independent of `u,v`.

## References

* Stacks Project, Definition 92.3.2 and Sections 92.5–92.7.
* J.-L. Loday, *Cyclic Homology*, second edition, Definition 3.5.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The functor
`polynomialCotangentCochainFunctor k A : Over A → CochainComplex (ModuleCat A) ℤ` extends each
normalized polynomial cotangent chain model along `ComplexShape.embeddingDownNat`, whose index
map is `n ↦ -n`. Positive cochain degrees are zero, and morphisms are the extensions of the
polynomial cotangent chain maps. -/
def polynomialCotangentCochainFunctor :
    Over A ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ where
  obj P := ((polynomialCotangentChainFunctor k A).obj P).extend
    ComplexShape.embeddingDownNat
  map f := HomologicalComplex.extendMap
    ((polynomialCotangentChainFunctor k A).map f) ComplexShape.embeddingDownNat
  map_id P := by
    rw [(polynomialCotangentChainFunctor.{u, v} k A).map_id P, HomologicalComplex.extendMap_id]
  map_comp f g := by
    rw [(polynomialCotangentChainFunctor.{u, v} k A).map_comp f g, HomologicalComplex.extendMap_comp]

/-- For a commutative ring `k : Type u` and `A : CommAlgCat.{max u v} k`, `cotangentCochainComplex
k A` is the value of `polynomialCotangentCochainFunctor k A` at `Over.mk (𝟙 A)`. It is the
normalized polynomial cotangent chain complex of `A/k` placed in cochain degree `-n` for chain
degree `n`. -/
def cotangentCochainComplex : CochainComplex (ModuleCat.{max u v} A) ℤ :=
  (polynomialCotangentCochainFunctor k A).obj (Over.mk (𝟙 A))

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and assume
`HasDerivedCategory.{w} (ModuleCat.{max u v} A)`. The functor `Over A → DerivedCategory
(ModuleCat A)` is `polynomialCotangentCochainFunctor k A ⋙ DerivedCategory.Q`. The source
algebra varies over `A`, while the coefficient algebra `A` stays fixed. -/
def polynomialCotangentDerivedFunctor : Over A ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  polynomialCotangentCochainFunctor k A ⋙ DerivedCategory.Q

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and a derived-category
structure at independent universe `w` on `ModuleCat.{max u v} A`, `cotangentDerived k A` is
the value of the polynomial cotangent derived functor at the identity algebra `A → A`. It is
an object of `DerivedCategory (ModuleCat A)`. -/
def cotangentDerived : DerivedCategory (ModuleCat.{max u v} A) :=
  (polynomialCotangentDerivedFunctor k A).obj (Over.mk (𝟙 A))

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and assume
`HasDerivedCategory.{w} (ModuleCat.{max u v} A)`. Then `cotangentDerived k A =
DerivedCategory.Q.obj (cotangentCochainComplex k A)`: the derived object is the localization
image of the integer cochain representative. -/
theorem cotangentDerived_eq :
    cotangentDerived k A = DerivedCategory.Q.obj (cotangentCochainComplex k A) := rfl

end CommAlgCat

end
