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
variable [IsCurveOver ℂ F] [∀ v : Place ℂ F, v.DCoordGenerates]

-- `exactSource` consumer with the original binders, under the curve and coordinate
-- hypotheses: the Abel-Jacobi divisor map on a single place is the scalar multiple of its
-- vector.
private theorem exactSource {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b P₀ (Finsupp.single v m) = m • abelJacobiVec b P₀ v :=
  abelJacobiDiv_single b P₀ v m

-- The coordinate differential at a place is the differential of an element of order one.
example (v : Place ℂ F) : v.ord v.dCoordFn = 1 := v.ord_dCoordFn

-- Every place of a complex curve is rational, and evaluation there takes the residue.
example (v : Place ℂ F) : v.IsRational := v.isRational_of_isCurveOver

example (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt v.isRational_of_isCurveOver f) :=
  v.hasValueAt_evalAt _ hf

-- A differential `f • dCoord` is read through its coefficient `f`, and the zero
-- differential reads as zero.
example (v : Place ℂ F) (f : F) :
    v.readDifferential (f • v.dCoord) =
      fun z => v.chartRead f z * deriv (v.chartRead v.dCoordFn) z :=
  v.readDifferential_smul_dCoord f

example (v : Place ℂ F) (z : ℂ) : v.readDifferential 0 z = 0 := by
  simp

-- A loop based at a place contributes a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F} (γ : Path P P) :
    (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b :=
  mem_pathPeriodLattice_of_loop b γ

-- Boundary example: the zero family has zero Abel-Jacobi vector.
example {n : ℕ} (P₀ P : Place ℂ F) :
    abelJacobiVec (fun _ : Fin n => (0 : Ω[F⁄ℂ])) P₀ P = 0 :=
  abelJacobiVec_zero P₀ P

-- Boundary example: every differential has zero integral along a constant loop.
example (ω : Ω[F⁄ℂ]) (P : Place ℂ F) : pathIntegral ω (Path.refl P) = 0 :=
  pathIntegral_refl ω P

end AlgebraicCurve
