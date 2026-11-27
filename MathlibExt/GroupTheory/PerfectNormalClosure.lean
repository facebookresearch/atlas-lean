/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.GroupTheory.IsPerfect

/-!
# Normal closures of perfect subgroups

The normal closure of a perfect subgroup is perfect. Its image under any
group homomorphism lies in the target commutator. This lets a finite
elementary subgroup provide a genuine perfect normal subgroup without
assuming that the finite elementary subgroup is itself normal.
-/

set_option autoImplicit false

open scoped commutatorElement

universe u v

namespace Subgroup

variable {G : Type u} {K : Type v} [Group G] [Group K]

/-- Taking normal closure preserves perfectness of a subgroup. -/
public theorem isPerfect_normalClosure (H : Subgroup G) [Group.IsPerfect H] :
    Group.IsPerfect (normalClosure (H : Set G)) := by
  let N : Subgroup G := normalClosure (H : Set G)
  have hH : H ≤ N := le_normalClosure
  have hcomm : H ≤ ⁅N, N⁆ := by
    rw [← commutator_eq_self (H := H)]
    exact commutator_mono hH hH
  apply isPerfect_iff.mpr
  change ⁅N, N⁆ = N
  exact le_antisymm N.commutator_le_self
    (normalClosure_le_normal hcomm)

/-- The image of a perfect subgroup belongs to the whole target
commutator, using the existing commutator image formula. -/
public theorem map_le_commutator_of_isPerfect
    (H : Subgroup G) [Group.IsPerfect H] (f : G →* K) :
    H.map f ≤ _root_.commutator K := by
  rw [← commutator_eq_self (H := H), map_commutator, _root_.commutator_def]
  exact commutator_mono le_top le_top

end Subgroup
