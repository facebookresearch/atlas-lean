/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff.lean`
and
`P2M/Sol/S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

@[expose] public section

namespace Subgroup

/-- Membership in the join of a subgroup with the cyclic subgroup generated
by a central involution.

This is the computation behind "up to sign" arguments: for a subgroup
`Γ` of `SL(2, ℤ)`, an element lies in `Γ` adjoined with `-1` exactly when
it or its negative lies in `Γ`. The same pattern recurs for any group with
a central involution: spin groups, dihedral groups, and congruence
subgroups. -/
theorem mem_sup_zpowers_iff_of_central_sq_eq_one {G : Type*} [Group G]
    (Γ : Subgroup G) {c : G} (hc : c ∈ Subgroup.center G) (hc2 : c ^ 2 = 1)
    (g : G) :
    g ∈ Γ ⊔ Subgroup.zpowers c ↔ g ∈ Γ ∨ c * g ∈ Γ := by
  classical
  have hcent : ∀ x : G, c * x = x * c :=
    fun x => (Subgroup.mem_center_iff.mp hc x).symm
  have hcc : c * c = 1 := by rw [← sq, hc2]
  have hmul : ∀ x y : G, (c * x) * (c * y) = x * y := by
    intro x y
    rw [mul_assoc, ← mul_assoc x c y, ← hcent x, ← mul_assoc, ← mul_assoc, hcc,
      one_mul]
  let pm : Subgroup G :=
    { carrier := {g | g ∈ Γ ∨ c * g ∈ Γ}
      one_mem' := Or.inl Γ.one_mem
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (Γ.mul_mem ha hb)
        · right
          have e : c * (a * b) = a * (c * b) := by
            rw [← mul_assoc, hcent a, mul_assoc]
          rw [e]
          exact Γ.mul_mem ha hb
        · right
          rw [← mul_assoc]
          exact Γ.mul_mem ha hb
        · left
          rw [← hmul a b]
          exact Γ.mul_mem ha hb
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (Γ.inv_mem ha)
        · right
          have h1 : c * a⁻¹ = (c * a)⁻¹ := by
            rw [hcent, mul_inv_rev, inv_eq_of_mul_eq_one_left hcc]
          rw [h1]
          exact Γ.inv_mem ha }
  have hmem : ∀ x : G, x ∈ pm ↔ x ∈ Γ ∨ c * x ∈ Γ := fun _ => Iff.rfl
  constructor
  · intro hg
    have hle : Γ ⊔ Subgroup.zpowers c ≤ pm := by
      refine sup_le (fun x hx => Or.inl hx) ?_
      rw [Subgroup.zpowers_le, hmem]
      right
      rw [hcc]
      exact Γ.one_mem
    exact (hmem g).mp (hle hg)
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have e : (c * g) * c = g := by
        rw [mul_assoc, ← hcent g, ← mul_assoc, hcc, one_mul]
      rw [← e]
      exact Subgroup.mul_mem (Γ ⊔ Subgroup.zpowers c) (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

end Subgroup
