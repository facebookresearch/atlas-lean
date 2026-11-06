/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Transport of actual derived subgroups and abelian kernels through a genuine group isomorphism. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationSmallIndexDerived

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A genuine group isomorphism transports the source derived subgroup onto the target one. -/
theorem y322Derived_map_equiv {S H : Type*} [Group S] [Group H] (e : S ≃* H) :
    (commutator S).map e.toMonoidHom = commutator H := by
  have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  rw [map_commutator_eq, hr]
  rfl

/-- A proved source abelian-kernel identity transports through a genuine group isomorphism. -/
theorem y322Derived_kernel_transport {S H A : Type*} [Group S] [Group H] [CommGroup A]
    (e : S ≃* H) (sign : H →* A)
    (hkernel : (sign.comp e.toMonoidHom).ker = commutator S) :
    sign.ker = commutator H := by
  rw [← y322Derived_map_equiv e]
  ext x
  rw [Subgroup.mem_map_equiv]
  rw [← hkernel]
  change sign x = 1 ↔ sign (e (e.symm x)) = 1
  rw [e.apply_symm_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
