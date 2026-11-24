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
# Actual homomorphisms from perfect subgroups to commutative groups

The original image subgroup is perfect by the stock image theorem and
commutative by the original target multiplication. The stock
perfect-and-commutative subsingleton theorem then kills every element.
No group structure or homomorphism is replaced.
-/

public section

namespace MonoidHom

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Every original homomorphism to a commutative group kills each
perfect source subgroup. -/
theorem eq_one_of_mem_perfect_subgroup [IsMulCommutative H]
    (f : G →* H) (P : Subgroup G) [Group.IsPerfect P]
    {g : G} (hg : g ∈ P) : f g = 1 := by
  let Q := P.map f
  let : Group.IsPerfect Q := Group.IsPerfect.map f
  let : IsMulCommutative Q := IsMulCommutative.of_comm (fun a b =>
    Subtype.ext (mul_comm' (a : H) (b : H)))
  let : Subsingleton Q := Group.IsPerfect.subsingleton_of_isMulCommutative
  let z : Q := ⟨f g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩
  exact congrArg (fun a : Q => (a : H)) (Subsingleton.elim z 1)

end MonoidHom
