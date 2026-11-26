/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RightHodgeSourceRequestsActualGradedEulerLocalNilpotence

/-!
# Tests for actual graded Euler local nilpotence

Corollaries of graded Euler local nilpotence: the killing exponent gives the zero
endomorphism on every open below the nilpotence neighborhood, and the next iterate
(index `r + 1`) also vanishes on graded sections there.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.RightHodgeSourceRequestsActualGradedEulerLocalNilpotence

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.RightDifferentialModules
open MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels
open WantedExt.AlgebraicGeometry.RightHodgeSourceRequests

/-- The killing iterate of the graded Euler map is the zero map below `U`. -/
theorem eulerIterate_eq_zero (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (a : ℚ) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ r : ℕ, 0 < r ∧ ∀ (W : Opens M), W ≤ U →
      ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r]) = 0 := by
  obtain ⟨U, hxU, r, hrpos, hvanish⟩ :=
    actual_graded_euler_local_nilpotence k M O C N V A a x
  exact ⟨U, hxU, r, hrpos, fun W hWU => funext (hvanish W hWU)⟩

/-- The graded Euler iterate of index `r + 1` also vanishes on graded sections below `U`. -/
theorem eulerIterate_succ_eq_zero (k : Type) [CommRing k] [Algebra ℚ k]
    (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
    [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (V : RationalVFiltration k M O C N) (A : GradedVOperators k M O C N V)
    (a : ℚ) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ r : ℕ, 0 < r ∧ ∀ (W : Opens M), W ≤ U →
      ∀ s : (gradedV k M O C N V a).val.obj (op W),
        ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r + 1]) s = 0 := by
  obtain ⟨U, hxU, r, hrpos, hvanish⟩ :=
    actual_graded_euler_local_nilpotence k M O C N V A a x
  refine ⟨U, hxU, r, hrpos, ?_⟩
  intro W hWU s
  have h0 : ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r]) s = 0 :=
    hvanish W hWU s
  have hstep : ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r + 1]) s =
      (((A.eulerMap a).asHom.val.app (op W)).hom)
        ((((A.eulerMap a).asHom.val.app (op W)).hom)^[r] s) := by
    simp only [Function.iterate_succ_apply']
  rw [hstep, h0]
  exact map_zero _

end MathlibExtTest.AlgebraicGeometry.RightHodgeSourceRequestsActualGradedEulerLocalNilpotence
