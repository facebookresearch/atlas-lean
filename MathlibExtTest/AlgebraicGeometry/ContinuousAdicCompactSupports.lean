/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

/-! # Tests for compactly supported cohomology through a compactification

The map of compact-support coefficient sheaves is functorial in the coefficients, the reductions
of compactly supported cohomology are compatible with the transitions, and the comparison with the
inverse limit has the reductions as coordinates.
-/

namespace MathlibExtTest.AlgebraicGeometry.ContinuousAdicCompactSupports

open CategoryTheory
open MathlibExt.AlgebraicGeometry.EllAdicCohomology
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

variable {k : Type} [Field k] {X : Over (AlgebraicGeometry.Spec (.of k))}
  (c : ClosedCompactification X)

/-- The coefficient-sheaf map of a composite is the composite of the coefficient-sheaf maps. -/
example {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [IsTopologicalAddGroup A]
    [IsTopologicalAddGroup B] [IsTopologicalAddGroup C] (f : A →ₜ+ B) (g : B →ₜ+ C) :
    compactCoefficientMap c (g.comp f) = compactCoefficientMap c f ≫ compactCoefficientMap c g := by
  have hg : globalCoefficientMap (g.comp f) = globalCoefficientMap f ≫ globalCoefficientMap g := by
    ext U s
    rfl
  simp only [compactCoefficientMap, coefficientMap]
  rw [hg, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]

/-- The coefficient-sheaf map of the identity is the identity. -/
example (A : Type) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A] :
    compactCoefficientMap c (ContinuousAddMonoidHom.id A) = 𝟙 _ := by
  have hg : globalCoefficientMap (ContinuousAddMonoidHom.id A) = 𝟙 _ := by
    ext U s
    rfl
  simp only [compactCoefficientMap, coefficientMap]
  rw [hg, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

variable (ell : ℕ) [Fact ell.Prime] (n : ℕ)

/-- The reductions are compatible with the transitions (canonical reduction maps). -/
example (r : ℕ) (x : integralCompactSupport ell c n) :
    compactTransition ell c n r (compactReduction ell c n (r + 1) x) =
      compactReduction ell c n r x :=
  compactReductionsCommute ell c n r x

/-- The coordinates of the comparison with the inverse limit are the reductions. -/
example (r : ℕ) (x : integralCompactSupport ell c n) :
    (compactSupportLimitComparison ell c n x : ∀ r, finiteCompactSupport ell c n r) r =
      compactReduction ell c n r x :=
  rfl

/-- The comparison sends zero to zero. -/
example : compactSupportLimitComparison ell c n 0 = 0 := map_zero _

end MathlibExtTest.AlgebraicGeometry.ContinuousAdicCompactSupports
