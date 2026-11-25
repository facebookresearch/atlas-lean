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
# The canonical polynomial cotangent object in the native derived category

Extend the genuine normalized cotangent chain model along `n ↦ -n` and
apply the native localization functor `DerivedCategory.Q`. Morphisms use
the constructed polynomial cotangent chain maps and native extension maps.
The resulting object is an actual derived category object associated to the
standard polynomial model. It is defined without supplied comparison data.

The localization universe is independent of the ring and carrier universes;
the only category choice is Mathlib's native `HasDerivedCategory` parameter.
Resolution independence, the derived derivation universal property and the
transitivity triangle are distinct theorem obligations. No identification
with the naive two-term presentation complex is asserted here.

References: Stacks Project, Definition 92.3.2, the degree convention following
it, Sections 92.5–92.7; Loday, second edition, Definition 3.5.3.

-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The canonical cotangent cochain model is the extension of the normalized
chain model by zero to positive cochain degrees, via `n ↦ -n`. -/
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

/-- The actual cochain representative of the canonical cotangent complex. -/
def cotangentCochainComplex : CochainComplex (ModuleCat.{max u v} A) ℤ :=
  (polynomialCotangentCochainFunctor k A).obj (Over.mk (𝟙 A))

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/-- The native derived image of the constructed polynomial cotangent model,
functorial in the source algebra over the fixed coefficient target. -/
def polynomialCotangentDerivedFunctor : Over A ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  polynomialCotangentCochainFunctor k A ⋙ DerivedCategory.Q

/-- The genuine native derived category object of the canonical polynomial
cotangent complex of `A/k`. -/
def cotangentDerived : DerivedCategory (ModuleCat.{max u v} A) :=
  (polynomialCotangentDerivedFunctor k A).obj (Over.mk (𝟙 A))

/-- This object is the native derived image of the actual normalized
cotangent complex after the literal negative-degree extension. -/
theorem cotangentDerived_eq :
    cotangentDerived k A = DerivedCategory.Q.obj (cotangentCochainComplex k A) := rfl

end CommAlgCat

end
