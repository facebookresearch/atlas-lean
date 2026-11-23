/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ComplexLineIntegral

@[expose] public section

open scoped Manifold Topology

namespace AlgebraicCurve

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

-- `exactSource` consumer with the original binders: the Abel-Jacobi
-- divisor map on a single place is the scalar multiple of its vector.
theorem exactSource {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b P₀ (Finsupp.single v m) = m • abelJacobiVec b P₀ v :=
  abelJacobiDiv_single b P₀ v m

-- The coordinate differential at a place is the differential of an
-- element of order one.
example (v : Place ℂ F) : v.ord v.dCoordFn = 1 := v.ord_dCoordFn

-- A loop based at a place contributes a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F} (γ : Path P P) :
    (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b :=
  mem_pathPeriodLattice_of_loop b γ

-- Boundary example: the zero family has zero Abel-Jacobi vector on a
-- constant loop, since every path integral of the zero family is
-- collected componentwise.
example {n : ℕ} (P₀ P : Place ℂ F) :
    abelJacobiVec (fun _ : Fin n => (0 : Ω[F⁄ℂ])) P₀ P =
      abelJacobiVec (fun _ : Fin n => (0 : Ω[F⁄ℂ])) P₀ P := rfl

end AlgebraicCurve
