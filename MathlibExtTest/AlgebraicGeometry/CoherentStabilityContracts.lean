/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

@[expose] public section

open CategoryTheory
open MathlibExt.CategoryTheory.BridgelandStability
open MathlibExt.AlgebraicGeometry.BoundedCoherent
open MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

attribute [local instance] HasDerivedCategory.standard

universe u

variable (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]
  [(boundedCoherent X).IsTriangulated]
  [(boundedCoherent X).IsClosedUnderIsomorphisms]

-- Stability conditions on `DbCoh X` are the general ones on that full subcategory.
example (s : StabilityCondition X) :
    MathlibExt.CategoryTheory.BridgelandStability.StabilityCondition (DbCoh X) := s

-- Objects of `DbCoh X` are bounded coherent derived objects.
example (E : DbCoh X) : boundedCoherent X E.obj := E.property

-- Numerical stability conditions forget to stability conditions.
noncomputable example (rank : ℕ) (s : NumericalStabilityCondition X rank) :
    StabilityCondition X :=
  s.toStabilityCondition
