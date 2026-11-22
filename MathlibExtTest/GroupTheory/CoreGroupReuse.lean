/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
Canonical homomorphism, coset, quotient and counting APIs. Subgroup correspondence is checked
through map/comap inverse laws.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

variable {G H : Type*} [Group G] [Group H]

#check Group
#check MonoidHom

example (f : G → H) (h : ∀ a b : G, f (a * b) = f a * f b) : f 1 = 1 :=
  (MonoidHom.mk' f h).map_one

example (f : G → H) (h : ∀ a b : G, f (a * b) = f a * f b) (a : G) :
    f a⁻¹ = (f a)⁻¹ := (MonoidHom.mk' f h).map_inv a

example (S : Subgroup G) : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
example (S : Subgroup G) : S.index * Nat.card S = Nat.card G := S.index_mul_card
example (S : Subgroup G) : Nat.card S * S.index = Nat.card G := S.card_mul_index

example (f : G →* H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.index_ker f]
  exact f.ker.card_mul_index.symm

example (f : G →* H) (hf : Function.Surjective f) (S : Subgroup H) :
    (S.comap f).map f = S := Subgroup.map_comap_eq_self_of_surjective hf S

example (f : G →* H) (S : Subgroup G) (hS : f.ker ≤ S) :
    (S.map f).comap f = S := Subgroup.comap_map_eq_self hS

example (S : Subgroup G) :
    S.Normal ↔ ∀ g : G, g • (S : Set G) = MulOpposite.op g • (S : Set G) :=
  normal_iff_eq_cosets S

example (S : Subgroup G) (a b : G) (hb : b ∈ a • (S : Set G)) :
    a • (S : Set G) = b • (S : Set G) :=
  (leftCoset_eq_iff S).mpr ((mem_leftCoset_iff a).mp hb)

example (N : Subgroup G) [N.Normal] : Group (G ⧸ N) := inferInstance
example (N : Subgroup G) [N.Normal] : Function.Surjective (QuotientGroup.mk' N) :=
  QuotientGroup.mk'_surjective N
example (N : Subgroup G) [N.Normal] : (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N

#print axioms MonoidHom.mk'
#print axioms MonoidHom.map_one
#print axioms MonoidHom.map_inv
#print axioms Subgroup.card_subgroup_dvd_card
#print axioms Subgroup.card_mul_index
#print axioms Subgroup.index_mul_card
#print axioms Subgroup.index_ker
#print axioms Subgroup.map_comap_eq_self_of_surjective
#print axioms Subgroup.comap_map_eq_self
#print axioms normal_iff_eq_cosets
#print axioms leftCoset_eq_iff
#print axioms mem_leftCoset_iff
#print axioms QuotientGroup.mk'_surjective
#print axioms QuotientGroup.ker_mk'

end
