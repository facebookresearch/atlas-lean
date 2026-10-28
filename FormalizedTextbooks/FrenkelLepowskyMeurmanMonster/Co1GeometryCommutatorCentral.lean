/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorLocal
public import Mathlib.SetTheory.Cardinal.Finite

/-! One genuine line forces the common cyclic commutator subgroup to be central
of order at most two. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
variable {P R : Type*} [Group R]
variable (geometry : Co1GeometryCommutatorGeometry P)
variable (representation : Co1GeometryCommutatorRepresentation geometry R)

/-- Each element of the common cyclic subgroup equals its inverse. A line image is
both an inverter and a product of two inverters, so it also centralizes that subgroup. -/
theorem co1GeometryPointCommutatorSubgroup_self_inverse (base : P) (c : R)
    (hc : c ∈ co1GeometryPointCommutatorSubgroup geometry representation base) : c⁻¹ = c := by
  obtain ⟨x, y, z, hline⟩ := geometry.line_exists
  have hx := co1GeometryPointCommutatorSubgroup_inverted geometry representation base x c hc
  have hy := co1GeometryPointCommutatorSubgroup_inverted geometry representation base y c hc
  have hz := co1GeometryPointCommutatorSubgroup_inverted geometry representation base z c hc
  have hpair := co1GeometryCommutator_line_pair _ _ _ (representation.square x)
    (representation.line_product x y z hline)
  have he : representation.point x * c * (representation.point x)⁻¹ = c := by
    rw [hpair, mul_inv_rev]
    calc
      _ = representation.point y *
          (representation.point z * c * (representation.point z)⁻¹) *
            (representation.point y)⁻¹ := by group
      _ = representation.point y * c⁻¹ * (representation.point y)⁻¹ := by rw [hz]
      _ = (representation.point y * c * (representation.point y)⁻¹)⁻¹ := by group
      _ = c := by rw [hy, inv_inv]
  exact hx.symm.trans he

/-- Every element of the common cyclic subgroup has square one. -/
theorem co1GeometryPointCommutatorSubgroup_square (base : P) (c : R)
    (hc : c ∈ co1GeometryPointCommutatorSubgroup geometry representation base) : c ^ 2 = 1 := by
  have hi := co1GeometryPointCommutatorSubgroup_self_inverse geometry representation base c hc
  rw [pow_two]
  calc
    c * c = c⁻¹ * c := congrArg (· * c) hi.symm
    _ = 1 := inv_mul_cancel c

/-- Every original generator commutes with every element of the common cyclic subgroup. -/
theorem co1GeometryPointCommutatorSubgroup_generator_commute (base x : P) (c : R)
    (hc : c ∈ co1GeometryPointCommutatorSubgroup geometry representation base) :
    Commute (representation.point x) c := by
  have h := co1GeometryPointCommutatorSubgroup_inverted geometry representation base x c hc
  rw [co1GeometryPointCommutatorSubgroup_self_inverse geometry representation base c hc] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- Generation by the point images makes the common cyclic subgroup central in R. -/
theorem co1GeometryPointCommutatorSubgroup_le_center (base : P) :
    co1GeometryPointCommutatorSubgroup geometry representation base ≤ Subgroup.center R := by
  intro c hc
  have hle : Subgroup.closure (Set.range representation.point) ≤ Subgroup.centralizer {c} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (co1GeometryPointCommutatorSubgroup_generator_commute geometry representation base x c hc)
  rw [representation.generates] at hle
  exact Subgroup.mem_center_iff.mpr fun r =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top r))

/-- The common subgroup is genuinely finite, with cardinality at most two. -/
theorem co1GeometryPointCommutatorSubgroup_finite_card (base : P) :
    Finite (co1GeometryPointCommutatorSubgroup geometry representation base) ∧
      Nat.card (co1GeometryPointCommutatorSubgroup geometry representation base) ≤ 2 := by
  let c := co1GeometryPointCommutator geometry representation base
  have hs : c ^ 2 = 1 := co1GeometryPointCommutatorSubgroup_square geometry representation base c
    (Subgroup.mem_zpowers c)
  have hf : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
  have he := finEquivZPowers hf
  refine ⟨Finite.of_equiv (Fin (orderOf c)) he, ?_⟩
  change Nat.card (Subgroup.zpowers c) ≤ 2
  rw [← Nat.card_congr he, Nat.card_fin]
  exact orderOf_le_of_pow_eq_one (by decide : 0 < 2) hs

/-- Every pair of point images has commutator in the same central cyclic subgroup. -/
theorem co1GeometryPointCommutatorSubgroup_contains_pairs (base x y : P) :
    ⁅representation.point x, representation.point y⁆ ∈
      co1GeometryPointCommutatorSubgroup geometry representation base := by
  by_cases hxy : geometry.distant x y
  · rw [co1GeometryPointCommutatorSubgroup_constant geometry representation base x,
      co1GeometryPointCommutatorSubgroup,
      co1GeometryPointCommutator_eq geometry representation x y hxy]
    exact Subgroup.mem_zpowers _
  · rw [(representation.close_commute x y hxy).commutator_eq]
    exact Subgroup.one_mem _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
