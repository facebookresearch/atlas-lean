/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FifteenA1SelmerBound

@[expose] public section

open ModularCurve.FifteenA1

example (P : shortW.Point) :
    ∃ v ∈ V₀, IsSqClass v.1 (deltaPair P).1 ∧ IsSqClass v.2 (deltaPair P).2 :=
  ModularCurve.FifteenA1.selmerBound P

example : deltaPair (0 : shortW.Point) = (1, 1) := deltaPair_zero

example : ((2 : ℚ), (2 : ℚ)) ∉ V₀ := by
  norm_num [V₀]
