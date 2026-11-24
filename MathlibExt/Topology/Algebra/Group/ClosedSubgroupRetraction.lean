/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Algebra.Group.ProfiniteCosetSectionZorn
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Continuous equivariant coordinates for closed profinite subgroups

A genuine continuous closed-coset section gives a continuous left
`H`-equivariant retraction `G → H`, normalized on `H`. No normality or
finite-index hypothesis is used. The coordinate is noncanonical; its
existence and normalization are proved from the actual quotient section.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open QuotientGroup

universe g

namespace Subgroup

variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every closed subgroup of a profinite group has a continuous,
left-equivariant retraction, with no normality or index restriction. -/
theorem exists_continuous_equivariant_retraction
    (H : Subgroup G) [IsClosed (H : Set G)] :
    ∃ r : C(G, H), (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧
      (∀ h : H, r (h : G) = h) := by
  obtain ⟨s₀, hs₀⟩ := QuotientGroup.exists_continuous_section_of_closedSubgroup_le
    (⊥ : Subgroup G) H bot_le
  let e : (G ⧸ (⊥ : Subgroup G)) ≃ₜ G :=
    { toEquiv := QuotientGroup.quotientBot.toEquiv
      continuous_toFun := continuous_quot_lift _ continuous_id
      continuous_invFun := QuotientGroup.continuous_mk }
  let q : C(G, G ⧸ H) := ⟨QuotientGroup.mk, QuotientGroup.continuous_mk⟩
  let s : C(G ⧸ H, G) := (⟨e, e.continuous⟩ : C(G ⧸ (⊥ : Subgroup G), G)).comp s₀
  have he (a : G ⧸ (⊥ : Subgroup G)) :
      q (e a) = QuotientGroup.cosetProjection (bot_le : (⊥ : Subgroup G) ≤ H) a := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rfl
  have hs (a : G ⧸ H) : q (s a) = a := (he (s₀ a)).trans (hs₀ a)
  let right : C(G, H) :=
    ⟨fun g => ⟨(s (q g))⁻¹ * g, QuotientGroup.eq.mp (hs (q g))⟩,
      Continuous.subtype_mk
        ((s.continuous.comp q.continuous).inv.mul continuous_id) _⟩
  have hright (g : G) (h : H) : right (g * (h : G)) = right g * h := by
    apply Subtype.ext
    change (s (q (g * (h : G))))⁻¹ * (g * (h : G)) =
      ((s (q g))⁻¹ * g) * (h : G)
    have hq : q (g * (h : G)) = q g := QuotientGroup.mk_mul_of_mem g h.property
    rw [hq, mul_assoc]
  let left : C(G, H) :=
    ⟨fun g => (right g⁻¹)⁻¹, (right.continuous.comp continuous_inv).inv⟩
  have hleft (h : H) (g : G) : left ((h : G) * g) = h * left g := by
    change (right (((h : G) * g)⁻¹))⁻¹ = h * (right g⁻¹)⁻¹
    rw [mul_inv_rev]
    have hr := hright g⁻¹ h⁻¹
    change right (g⁻¹ * (h : G)⁻¹) = right g⁻¹ * h⁻¹ at hr
    rw [hr, mul_inv_rev, inv_inv]
  let r : C(G, H) :=
    ⟨fun g => left g * (left 1)⁻¹, left.continuous.mul_const _⟩
  have hr (h : H) (g : G) : r ((h : G) * g) = h * r g := by
    change left ((h : G) * g) * (left 1)⁻¹ = h * (left g * (left 1)⁻¹)
    rw [hleft, mul_assoc]
  refine ⟨r, hr, fun h => ?_⟩
  have h := hr h 1
  simpa only [mul_one, r, ContinuousMap.coe_mk, mul_inv_cancel, mul_one] using h

/-- A chosen actual continuous left-equivariant retraction of a closed
subgroup; the choice is made from the proved closed-coset section theorem. -/
def continuousEquivariantRetraction (H : Subgroup G) [IsClosed (H : Set G)] : C(G, H) :=
  (exists_continuous_equivariant_retraction H).choose

/-- The chosen coordinate is left-equivariant for every subgroup element. -/
theorem continuousEquivariantRetraction_equivariant
    (H : Subgroup G) [IsClosed (H : Set G)] (h : H) (g : G) :
    continuousEquivariantRetraction H ((h : G) * g) =
      h * continuousEquivariantRetraction H g :=
  (exists_continuous_equivariant_retraction H).choose_spec.1 h g

/-- The chosen coordinate fixes every actual element of the closed subgroup. -/
theorem continuousEquivariantRetraction_subtype
    (H : Subgroup G) [IsClosed (H : Set G)] (h : H) :
    continuousEquivariantRetraction H (h : G) = h :=
  (exists_continuous_equivariant_retraction H).choose_spec.2 h

/-- The normalization fixes the identity element. -/
theorem continuousEquivariantRetraction_one
    (H : Subgroup G) [IsClosed (H : Set G)] :
    continuousEquivariantRetraction H (1 : G) = 1 :=
  continuousEquivariantRetraction_subtype H 1

end Subgroup
