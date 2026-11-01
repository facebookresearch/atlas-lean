/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorCentral

/-! Ivanov–Shpectorov II Lemma 2.3.7: the generated group has a commutator subgroup
of order at most two, under the explicit point-line connectivity hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
variable {P R : Type*} [Group R]

/-- Generator commutators in a normal subgroup place the full commutator subgroup there. -/
theorem co1GeometryCommutator_generated_le (phi : P → R)
    (hgen : Subgroup.closure (Set.range phi) = ⊤)
    (C : Subgroup R) [hC : C.Normal]
    (hpair : ∀ x y, ⁅phi x, phi y⁆ ∈ C) : commutator R ≤ C := by
  have hright (x : P) (b : R) (hb : b ∈ Subgroup.closure (Set.range phi)) :
      ⁅phi x, b⁆ ∈ C := by
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      exact hpair x y
    | one => simpa only [commutatorElement_one_right] using C.one_mem
    | mul b c hb hc ihb ihc =>
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa only [mul_assoc] using C.mul_mem ihb (hC.conj_mem _ ihc b)
    | inv b hb ih =>
      rw [commutatorElement_inv_right]
      have hi : ⁅b, phi x⁆ ∈ C := by
        rw [← commutatorElement_inv]
        exact C.inv_mem ih
      simpa only [inv_inv] using hC.conj_mem _ hi b⁻¹
  have hleft (a b : R) (ha : a ∈ Subgroup.closure (Set.range phi)) : ⁅a, b⁆ ∈ C := by
    have hb : b ∈ Subgroup.closure (Set.range phi) := by
      rw [hgen]
      trivial
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨x, rfl⟩ := ha
      exact hright x b hb
    | one => simpa only [commutatorElement_one_left] using C.one_mem
    | mul a c ha hc iha ihc =>
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact C.mul_mem (hC.conj_mem _ ihc a) iha
    | inv a ha ih =>
      rw [commutatorElement_inv_left]
      have hi : ⁅b, a⁆ ∈ C := by
        rw [← commutatorElement_inv]
        exact C.inv_mem ih
      simpa only [inv_inv] using hC.conj_mem _ hi a⁻¹
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  apply hleft
  rw [hgen]
  trivial

/-- The full group commutator is precisely the common point-associated cyclic subgroup. -/
theorem co1GeometryCommutator_eq_pointSubgroup
    (geometry : Co1GeometryCommutatorGeometry P)
    (representation : Co1GeometryCommutatorRepresentation geometry R) (base : P) :
    commutator R = co1GeometryPointCommutatorSubgroup geometry representation base := by
  apply le_antisymm
  · let C := co1GeometryPointCommutatorSubgroup geometry representation base
    have : C.Normal := Subgroup.normal_of_le_center
      (co1GeometryPointCommutatorSubgroup_le_center geometry representation base)
    exact co1GeometryCommutator_generated_le representation.point representation.generates C
      (co1GeometryPointCommutatorSubgroup_contains_pairs geometry representation base)
  · apply Subgroup.zpowers_le.mpr
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The commutator subgroup in II Lemma 2.3.7 is central. -/
theorem co1GeometryCommutator_le_center
    (geometry : Co1GeometryCommutatorGeometry P)
    (representation : Co1GeometryCommutatorRepresentation geometry R) :
    commutator R ≤ Subgroup.center R := by
  obtain ⟨base, _, _, _⟩ := geometry.line_exists
  rw [co1GeometryCommutator_eq_pointSubgroup geometry representation base]
  exact co1GeometryPointCommutatorSubgroup_le_center geometry representation base

/-- II Lemma 2.3.7, with genuine finiteness as well as the numerical order bound.
This requires the stated connectivity and representation data, not actual Co1 graph facts. -/
theorem co1GeometryCommutator_finite_card_le_two
    (geometry : Co1GeometryCommutatorGeometry P)
    (representation : Co1GeometryCommutatorRepresentation geometry R) :
    Finite (commutator R) ∧ Nat.card (commutator R) ≤ 2 := by
  obtain ⟨base, _, _, _⟩ := geometry.line_exists
  rw [co1GeometryCommutator_eq_pointSubgroup geometry representation base]
  exact co1GeometryPointCommutatorSubgroup_finite_card geometry representation base

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
