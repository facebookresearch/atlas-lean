/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Genus of a compact Riemann surface -/

@[expose] public section

open scoped ContDiff

namespace RiemannSurface

universe u

/-- **Genus of a compact Riemann surface.** For a compact connected complex curve, the genus
is half the dimension of its first singular homology with rational coefficients. The underlying
closed orientable surface of genus `g` has first Betti number `2g` (Hatcher, *Algebraic Topology*,
§2.2, cellular homology of closed orientable surfaces).

This is the genus in Kevin Buzzard's *Jacobian challenge*, via `jacobian_challenge_diffgeo`
in `leanprover/lean-eval`. -/
noncomputable def genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  let coeff := ModuleCat.of ℚ (ULift.{u} ℚ)
  let h₁ := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) 1).obj coeff).obj
    (TopCat.of X)
  Module.finrank ℚ h₁ / 2

end RiemannSurface
