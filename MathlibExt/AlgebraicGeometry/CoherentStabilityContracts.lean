/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Triangulated.BridgelandStability
public import MathlibExt.CategoryTheory.DerivedQuiverStability
public import MathlibExt.AlgebraicGeometry.SphericalTwists

/-!
# General stability contracts on actual bounded coherent derived categories

DbCoh uses the actual scheme-module derived category and the actual
bounded coherent homology property. Standard triangulated/isomorphism
closure is a named shared dependency. Numerical realization, slicing,
HN, local finiteness and support are data for the paper's construction;
no stability-existence theorem on arbitrary varieties is asserted.

The existing concrete quiver HN tower maps into the same general triangle
language. A complete quiver stability-condition provider on its bounded
subcategory remains a separate bridge from the existing quiver request.

Sources: Bridgeland, https://arxiv.org/abs/math/0212237, Definitions 3.3
and 5.1, Proposition 5.3; the existing actual bounded coherent and quiver
constructions imported here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.CategoryTheory.BridgelandStability
open MathlibExt.AlgebraicGeometry.SphericalTwists

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The actual bounded coherent derived category, with its inherited morphisms. -/
abbrev DbCoh (X : Scheme.{u}) := (boundedCoherent X).FullSubcategory

/-- A general stability object on actual DbCoh, conditional only
on the named category-closure dependencies. This is a type of data, not
an existence assertion. -/
abbrev StabilityCondition (X : Scheme.{u}) [IsNoetherian X]
    [(boundedCoherent X).IsTriangulated]
    [(boundedCoherent X).IsClosedUnderIsomorphisms] :=
  MathlibExt.CategoryTheory.BridgelandStability.StabilityCondition (DbCoh X)

/-- The finite-rank numerical/support specialization of that same general
actual coherent-category interface. -/
abbrev NumericalStabilityCondition (X : Scheme.{u}) [IsNoetherian X]
    [(boundedCoherent X).IsTriangulated]
    [(boundedCoherent X).IsClosedUnderIsomorphisms] (rank : ℕ) :=
  MathlibExt.CategoryTheory.BridgelandStability.NumericalStabilityCondition (DbCoh X) rank

end MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

namespace MathlibExt.CategoryTheory.DerivedQuiverStability

open _root_.CategoryTheory

attribute [local instance] HasDerivedCategory.standard

variable {k V : Type} [Field k] [Quiver V] [Fintype V]

/-- The concrete quiver tower is an instance of the general actual
distinguished-triangle tower language, in the same ambient category. -/
def HNFiltration.toGeneral {z : V → ℂ} {K : D k V}
    (F : HNFiltration k V z K) :
    MathlibExt.CategoryTheory.BridgelandStability.HNFiltration
      (D k V) (slicing k V z) K := F

/-- The actual bounded quiver-derived category for a stability provider.
No assertion is made on the unbounded ambient derived category. -/
abbrev BoundedDerivedQuiver (k V : Type) [Field k] [Quiver V] [Fintype V] :=
  (show ObjectProperty (D k V) from Bounded k V).FullSubcategory

end MathlibExt.CategoryTheory.DerivedQuiverStability
