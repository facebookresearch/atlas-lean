/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedCoherent
public import MathlibExt.CategoryTheory.Triangulated.BridgelandStability
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# General stability contracts on actual bounded coherent derived categories

DbCoh uses the actual scheme-module derived category and the actual
bounded coherent homology property. Standard triangulated/isomorphism
closure is a named shared dependency. Numerical realization, slicing,
HN, local finiteness and support are data for the paper's construction;
no stability-existence theorem on arbitrary varieties is asserted.

Sources: Bridgeland, https://arxiv.org/abs/math/0212237, Definitions 3.3
and 5.1, Proposition 5.3; the existing actual bounded coherent and quiver
constructions imported here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.CategoryTheory.BridgelandStability
open MathlibExt.AlgebraicGeometry.BoundedCoherent

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
