/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from Formal-Math's `MathlibExt/GroupTheory/Abelianization/PerfectKernel.lean`.
Author: @toskua
-/

module

public import Mathlib.GroupTheory.IsPerfect

/-!
# When abelianization preserves a quotient

The map induced by a surjective homomorphism is bijective precisely when
its kernel lies in the source commutator subgroup. In particular this holds
for a perfect kernel, as used in the plus-construction comparison.
-/

public section

namespace Group.Abelianization

variable {G H : Type*} [Group G] [Group H]

/-- The abelianization map kills every element of a perfect subgroup. -/
theorem of_eq_one_of_mem_perfect_subgroup (P : Subgroup G) [Group.IsPerfect P]
    {g : G} (hg : g ∈ P) : (of g : Abelianization G) = 1 := by
  let q : P →* Abelianization G := of.comp P.subtype
  have hp : (⟨g, hg⟩ : P) ∈ commutator P := Group.IsPerfect.mem_commutator
  exact MonoidHom.mem_ker.mp (commutator_le_ker q hp)

/-- A surjection induces a bijection on abelianizations exactly when its kernel
is contained in the source commutator subgroup. -/
theorem map_bijective_iff_ker_le_commutator (f : G →* H) (hf : Function.Surjective f) :
    Function.Bijective (map f) ↔ f.ker ≤ commutator G := by
  have hs : Function.Surjective (map f) := by
    intro y
    obtain ⟨b, rfl⟩ := surjective_of H y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨of a, map_of f a⟩
  rw [Function.Bijective, and_iff_left hs, ← (map f).ker_eq_bot_iff,
    ← map_ker_eq_ker_map f hf, Subgroup.map_eq_bot_iff, ker_of]

/-- A surjective homomorphism with perfect kernel induces a bijection on
abelianizations. -/
theorem map_bijective_of_surjective_of_isPerfect_ker
    (f : G →* H) (hf : Function.Surjective f) [Group.IsPerfect f.ker] :
    Function.Bijective (map f) :=
  (map_bijective_iff_ker_le_commutator f hf).2 (by
    rw [← ker_of]
    intro g hg
    exact MonoidHom.mem_ker.mpr (of_eq_one_of_mem_perfect_subgroup f.ker hg))

end Group.Abelianization
