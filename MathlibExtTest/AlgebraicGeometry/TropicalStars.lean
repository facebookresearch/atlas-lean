/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegralTropicalCycles

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles

private def halfLine : Polyhedron 1 where
  count := 1
  normal _ _ := 1
  constant _ := 0

example (x : RealSpace 1) : x ∈ halfLine.carrier ↔ 0 ≤ x 0 := by
  simp [Polyhedron.carrier, halfLine, character]

example (v : RealSpace 1) : v ∈ starDirections halfLine (0 : RealSpace 1) ↔ 0 ≤ v 0 := by
  simp [starDirections, halfLine, character]

example (v : RealSpace 1) : v ∈ starDirections halfLine (1 : RealSpace 1) := by
  simp [starDirections, halfLine, character]
