/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Group

/-! Point-line hypotheses and elementary group identities for Ivanov–Shpectorov II,
Lemma 2.3.7. This file does not assert these hypotheses for the actual Conway geometry. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement

/-- The two connectivity hypotheses of II Lemma 2.3.7, with genuine three-point
lines and at least one line. The complementary set A(x) is `¬ distant x y`. -/
structure Co1GeometryCommutatorGeometry (P : Type*) where
  /-- Membership in the complementary set B(x), giving global graph edges. -/
  distant : P → P → Prop
  /-- An ordered listing of the three distinct points of a genuine line. -/
  line : P → P → P → Prop
  distant_symm : ∀ x y, distant x y → distant y x
  connected : ∀ x y, Relation.ReflTransGen distant x y
  line_distinct : ∀ x y z, line x y z → x ≠ y ∧ y ≠ z ∧ z ≠ x
  line_exists : ∃ x y z, line x y z
  local_connected : ∀ x (u v : {y // distant x y}),
    Relation.ReflTransGen (fun u v : {y // distant x y} =>
      ∃ w, (line u.val v.val w ∨ line v.val u.val w) ∧ ¬ distant x w) u v

/-- A group representation by involutory point images and original line products.
The images generate the ambient group; nearby points have commuting images. -/
structure Co1GeometryCommutatorRepresentation {P : Type*}
    (geometry : Co1GeometryCommutatorGeometry P) (R : Type*) [Group R] where
  /-- The group element representing each original geometry point. -/
  point : P → R
  square : ∀ x, point x * point x = 1
  line_product : ∀ x y z, geometry.line x y z → point x * point y * point z = 1
  close_commute : ∀ x y, ¬ geometry.distant x y → Commute (point x) (point y)
  generates : Subgroup.closure (Set.range point) = ⊤

/-- A connected graph with a genuine line has a neighbor at every point. -/
theorem co1GeometryCommutator_neighbor {P : Type*}
    (geometry : Co1GeometryCommutatorGeometry P) (x : P) :
    ∃ y, geometry.distant x y := by
  obtain ⟨a, b, c, habc⟩ := geometry.line_exists
  have hab := (geometry.line_distinct a b c habc).1
  have ht : ∃ t : P, x ≠ t := by
    by_cases hxa : x = a
    · exact ⟨b, hxa ▸ hab⟩
    · exact ⟨a, hxa⟩
  obtain ⟨t, hxt⟩ := ht
  rcases (geometry.connected x t).cases_head with he | ⟨y, hxy, _⟩
  · exact (hxt he).elim
  · exact ⟨y, hxy⟩

/-- Three involutory images with line product one satisfy the original two-image formula. -/
theorem co1GeometryCommutator_line_pair {R : Type*} [Group R] (a b c : R)
    (ha : a * a = 1) (hline : a * b * c = 1) : a = b * c := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have h := congrArg (a⁻¹ * ·) hline
  simpa only [← mul_assoc, hai, ha, one_mul, mul_one] using h.symm

/-- Two point images on a three-point line commute. -/
theorem co1GeometryCommutator_line_commute {R : Type*} [Group R] (a b c : R)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hline : a * b * c = 1) : Commute b c := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc
  have hp := co1GeometryCommutator_line_pair a b c ha hline
  change b * c = c * b
  calc
    b * c = a := hp.symm
    _ = a⁻¹ := hai.symm
    _ = c * b := by rw [hp, mul_inv_rev, hbi, hci]

/-- Multiplying an image by one commuting with both entries changes no commutator. -/
theorem co1GeometryCommutator_close_factor {R : Type*} [Group R] (a b c : R)
    (hac : Commute a c) (hbc : Commute b c) : ⁅a, c * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, hac.commutator_eq, one_mul]
  have h : Commute c ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hac.symm.mul_right hbc.symm).mul_right hac.symm.inv_right).mul_right
      hbc.symm.inv_right
  exact h.mul_inv_cancel

/-- Conjugation by the first involutory entry inverts a point commutator. -/
theorem co1GeometryCommutator_entry_inverts {R : Type*} [Group R] (a b : R)
    (ha : a * a = 1) (hb : b * b = 1) :
    a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  simp only [commutatorElement_def, mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
