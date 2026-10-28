/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorData

/-! Local line paths identify point commutators; global paths identify their cyclic subgroups. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
variable {P R : Type*} [Group R]
variable (geometry : Co1GeometryCommutatorGeometry P)
variable (representation : Co1GeometryCommutatorRepresentation geometry R)

private theorem co1GeometryCommutator_line_edge (x u v w : P)
    (hline : geometry.line u v w) (hw : ¬ geometry.distant x w) :
    ⁅representation.point x, representation.point u⁆ =
      ⁅representation.point x, representation.point v⁆ := by
  have hpair := co1GeometryCommutator_line_pair _ _ _ (representation.square u)
    (representation.line_product u v w hline)
  have hcomm := co1GeometryCommutator_line_commute _ _ _ (representation.square u)
    (representation.square v) (representation.square w)
    (representation.line_product u v w hline)
  rw [hpair, hcomm.eq]
  exact co1GeometryCommutator_close_factor _ _ _
    (representation.close_commute x w hw) hcomm

/-- Connected local B(x) line paths give the same commutator with the point x. -/
theorem co1GeometryCommutator_local_constant (x u v : P)
    (hu : geometry.distant x u) (hv : geometry.distant x v) :
    ⁅representation.point x, representation.point u⁆ =
      ⁅representation.point x, representation.point v⁆ := by
  have hconstant : ∀ (a b : {y // geometry.distant x y}),
      Relation.ReflTransGen (fun a b : {y // geometry.distant x y} =>
        ∃ w, (geometry.line a.val b.val w ∨ geometry.line b.val a.val w) ∧
          ¬ geometry.distant x w) a b →
      ⁅representation.point x, representation.point a.val⁆ =
        ⁅representation.point x, representation.point b.val⁆ := by
    intro a b h
    induction h with
    | refl => rfl
    | @tail b c h hbc ih =>
      obtain ⟨w, hline, hw⟩ := hbc
      apply ih.trans
      rcases hline with hl | hl
      · exact co1GeometryCommutator_line_edge geometry representation x b.val c.val w hl hw
      · exact (co1GeometryCommutator_line_edge geometry representation x c.val b.val w hl hw).symm
  exact hconstant ⟨u, hu⟩ ⟨v, hv⟩ (geometry.local_connected x ⟨u, hu⟩ ⟨v, hv⟩)

/-- A chosen commutator with a genuine B-neighbor of x. -/
def co1GeometryPointCommutator (x : P) : R :=
  ⁅representation.point x,
    representation.point (Classical.choose (co1GeometryCommutator_neighbor geometry x))⁆

/-- The cyclic subgroup attached to a point by any of its B-neighbors. -/
def co1GeometryPointCommutatorSubgroup (x : P) : Subgroup R :=
  Subgroup.zpowers (co1GeometryPointCommutator geometry representation x)

/-- The chosen point commutator equals that for any B-neighbor. -/
theorem co1GeometryPointCommutator_eq (x y : P) (hy : geometry.distant x y) :
    co1GeometryPointCommutator geometry representation x =
      ⁅representation.point x, representation.point y⁆ :=
  co1GeometryCommutator_local_constant geometry representation x _ y
    (Classical.choose_spec (co1GeometryCommutator_neighbor geometry x)) hy

/-- Along a B-edge the two point-associated cyclic subgroups agree. -/
theorem co1GeometryPointCommutatorSubgroup_edge (x y : P) (hy : geometry.distant x y) :
    co1GeometryPointCommutatorSubgroup geometry representation x =
      co1GeometryPointCommutatorSubgroup geometry representation y := by
  unfold co1GeometryPointCommutatorSubgroup
  rw [co1GeometryPointCommutator_eq geometry representation x y hy,
    co1GeometryPointCommutator_eq geometry representation y x (geometry.distant_symm x y hy),
    ← commutatorElement_inv, Subgroup.zpowers_inv]

/-- Global B-connectivity makes the point-associated cyclic subgroup independent of x. -/
theorem co1GeometryPointCommutatorSubgroup_constant (x y : P) :
    co1GeometryPointCommutatorSubgroup geometry representation x =
      co1GeometryPointCommutatorSubgroup geometry representation y := by
  have h := geometry.connected x y
  induction h with
  | refl => rfl
  | @tail b c h hbc ih =>
    exact ih.trans (co1GeometryPointCommutatorSubgroup_edge geometry representation b c hbc)

/-- Every point image acts by inversion on the common cyclic commutator subgroup. -/
theorem co1GeometryPointCommutatorSubgroup_inverted (base x : P) (c : R)
    (hc : c ∈ co1GeometryPointCommutatorSubgroup geometry representation base) :
    representation.point x * c * (representation.point x)⁻¹ = c⁻¹ := by
  rw [co1GeometryPointCommutatorSubgroup_constant geometry representation base x] at hc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hi : representation.point x * co1GeometryPointCommutator geometry representation x *
      (representation.point x)⁻¹ =
        (co1GeometryPointCommutator geometry representation x)⁻¹ :=
    co1GeometryCommutator_entry_inverts _ _ (representation.square x)
      (representation.square _)
  change (MulAut.conj (representation.point x))
    (co1GeometryPointCommutator geometry representation x ^ n) = _
  rw [map_zpow, show (MulAut.conj (representation.point x))
    (co1GeometryPointCommutator geometry representation x) =
      (co1GeometryPointCommutator geometry representation x)⁻¹ from hi, inv_zpow]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
