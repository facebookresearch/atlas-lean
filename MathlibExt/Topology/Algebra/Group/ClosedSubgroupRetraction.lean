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
# Continuous equivariant retraction onto a closed profinite subgroup

For a closed subgroup `H` of a compact Hausdorff totally disconnected topological group `G`,
there exists a continuous retraction `r : G → H` with `r(hg)=h r(g)` for all `h∈H`, `g∈G`, and
`r(h)=h` on the subgroup.

A choice of such retraction retains these equivariance and normalization equations. No
normality, finite index or homomorphic splitting of `H` is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open QuotientGroup

universe g

namespace Subgroup

variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **Continuous left-equivariant retraction onto a closed subgroup.** Let `G` be a compact
Hausdorff totally disconnected topological group. Let `H≤G` be a closed subgroup, without
a normality or finite-index condition. there exists `r∈C(G,H)` with `r(hg)=h r(g)` for
every `h∈H`, `g∈G`, and `r(h)=h` on `H`. -/
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

/-- **Chosen continuous equivariant closed-subgroup coordinate.** Let `G` be a compact
Hausdorff totally disconnected topological group. Let `H≤G` be a closed subgroup, without
a normality or finite-index condition. `continuousEquivariantRetraction H : C(G,H)` is a
retraction with `r(hg)=h r(g)` and `r(h)=h`; it is not asserted to be a group
homomorphism. -/
def continuousEquivariantRetraction (H : Subgroup G) [IsClosed (H : Set G)] : C(G, H) :=
  (exists_continuous_equivariant_retraction H).choose

/-- **Left subgroup equivariance of the retraction.** Let `G` be a compact Hausdorff totally
disconnected topological group. Let `H≤G` be a closed subgroup, without a normality or
finite-index condition. for `r=continuousEquivariantRetraction H`, `h∈H`, `g∈G`, `r(hg)=h
r(g)`. -/
theorem continuousEquivariantRetraction_equivariant
    (H : Subgroup G) [IsClosed (H : Set G)] (h : H) (g : G) :
    continuousEquivariantRetraction H ((h : G) * g) =
      h * continuousEquivariantRetraction H g :=
  (exists_continuous_equivariant_retraction H).choose_spec.1 h g

/-- **Closed-subgroup retraction fixes subgroup elements.** Let `G` be a compact Hausdorff
totally disconnected topological group. Let `H≤G` be a closed subgroup, without a
normality or finite-index condition. for `r=continuousEquivariantRetraction H` and `h∈H`,
`r(h)=h`. -/
theorem continuousEquivariantRetraction_subtype
    (H : Subgroup G) [IsClosed (H : Set G)] (h : H) :
    continuousEquivariantRetraction H (h : G) = h :=
  (exists_continuous_equivariant_retraction H).choose_spec.2 h

/-- **Identity normalization of the closed-subgroup retraction.** Let `G` be a compact
Hausdorff totally disconnected topological group. Let `H≤G` be a closed subgroup, without
a normality or finite-index condition. `continuousEquivariantRetraction H (1_G)=1_H`. -/
theorem continuousEquivariantRetraction_one
    (H : Subgroup G) [IsClosed (H : Set G)] :
    continuousEquivariantRetraction H (1 : G) = 1 :=
  continuousEquivariantRetraction_subtype H 1

end Subgroup
