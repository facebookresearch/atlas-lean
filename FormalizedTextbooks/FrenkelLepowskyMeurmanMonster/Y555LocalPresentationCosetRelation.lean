/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Right-coset certificates in arbitrary genuine groups, without a normality assumption. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationContextChains

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equality of right cosets of an arbitrary actual subgroup, expressed by exact membership. -/
def y522CosetRelation {G : Type*} [Group G] (H : Subgroup G) (x y : G) : Prop :=
  x * y⁻¹ ∈ H

/-- Every actual group element lies in the same right coset as itself. -/
theorem y522CosetRelation_refl {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    y522CosetRelation H x x := by
  simp only [y522CosetRelation, mul_inv_cancel]
  exact H.one_mem

/-- Right-coset equality is symmetric by actual subgroup closure under inversion. -/
theorem y522CosetRelation_symm {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (h : y522CosetRelation H x y) : y522CosetRelation H y x := by
  have hi := H.inv_mem h
  simpa only [y522CosetRelation, mul_inv_rev, inv_inv] using hi

/-- Right-coset equality is transitive by actual subgroup closure under multiplication. -/
theorem y522CosetRelation_trans {G : Type*} [Group G] (H : Subgroup G) {x y z : G}
    (hxy : y522CosetRelation H x y) (hyz : y522CosetRelation H y z) :
    y522CosetRelation H x z := by
  have h := H.mul_mem hxy hyz
  simpa only [y522CosetRelation, mul_assoc, inv_mul_cancel_left] using h

/-- Equal right cosets remain equal under right multiplication by any actual group element. -/
theorem y522CosetRelation_right {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (h : y522CosetRelation H x y) (z : G) : y522CosetRelation H (x * z) (y * z) := by
  simpa only [y522CosetRelation, mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h

/-- An actual group equality implies right-coset equality for every subgroup. -/
theorem y522CosetRelation_of_eq {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (h : x = y) : y522CosetRelation H x y := by
  subst y
  exact y522CosetRelation_refl H x

/-- A literal source word pair claims equality of the actual right cosets of its values. -/
def Y322WordEquation.CosetValid {alphabet G : Type*} [Group G]
    (equation : Y322WordEquation alphabet) (values : alphabet → G) (H : Subgroup G) : Prop :=
  y522CosetRelation H (y322EquationWordValue values equation.left)
    (y322EquationWordValue values equation.right)

/-- Exact free reduction transports a right-coset claim without changing either group value. -/
theorem y522WordEquation_coset_transport {alphabet G : Type*}
    [DecidableEq alphabet] [Group G] (values : alphabet → G) (H : Subgroup G)
    (source target : Y322WordEquation alphabet) (hs : source.CosetValid values H)
    (hl : FreeGroup.reduce target.left = FreeGroup.reduce source.left)
    (hr : FreeGroup.reduce target.right = FreeGroup.reduce source.right) :
    target.CosetValid values H := by
  unfold Y322WordEquation.CosetValid
  rw [y322EquationWordValue_eq_of_reduce values _ _ hl,
    y322EquationWordValue_eq_of_reduce values _ _ hr]
  exact hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
