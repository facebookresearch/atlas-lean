/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoherentStabilityContracts

/-! # General category scope and nonvacuity checks

The general structures do not require a quiver, curve, surface or proper
variety. A zero charge cannot be a provider on a category with a nonzero
object. The DbCoh specialization retains the actual carrier and only its
named category-closure dependencies.
-/

open CategoryTheory CategoryTheory.Limits
open MathlibExt.CategoryTheory.BridgelandStability
open MathlibExt.AlgebraicGeometry.SphericalTwists

universe u v

section General

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

example (s : StabilityCondition C) (E : C) (hE : ¬ IsZero E) : s.charge ≠ 0 := by
  intro hz
  exact hE (s.isZero_of_charge_zero hz E)

example {rank : ℕ} (s : NumericalStabilityCondition C rank) :
    StabilityCondition C := s.toStabilityCondition

end General

section Coherent

variable (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]
  [(boundedCoherent X).IsTriangulated]
  [(boundedCoherent X).IsClosedUnderIsomorphisms]

example (s : MathlibExt.AlgebraicGeometry.CoherentStabilityContracts.StabilityCondition X) :
    StabilityCondition (MathlibExt.AlgebraicGeometry.CoherentStabilityContracts.DbCoh X) := s

end Coherent
