/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.Push
import Mathlib.Tactic.Abel

/-!
# Dihedral groups from an index-two cyclic subgroup

The constructor below is extracted from the generic private argument in
`MathlibExt/GroupTheory/DicksonPGL2Tame.lean`, commit
`8de8f74fa5760eb8b768a9804494ca2ab631cf87`, lines 342-465.
-/
set_option autoImplicit false

namespace MetaMathlibExt
@[expose] public section

/-- **Dihedral groups from a cyclic subgroup of index two.** Let $G$ be a finite group and let
$H$ be a cyclic subgroup of $G$ of index $2$. If $g^2 = 1$ for every element $g$ of $G$ that is
not in $H$, then $G$ is isomorphic to the dihedral group $D_n$ of order $2n$, where $n = |H|$. -/
theorem nonempty_mulEquiv_dihedralGroup_of_index_eq_two {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hHcyc : IsCyclic H) (hindex : H.index = 2)
    (houtside : ∀ g : G, g ∉ H → g ^ 2 = 1) :
    Nonempty (G ≃* DihedralGroup (Nat.card H)) := by
  classical
  let n := Nat.card H
  let _ : NeZero n := ⟨Nat.card_pos.ne'⟩
  let _ : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hHtop : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hindex
    omega
  obtain ⟨t, ht⟩ : ∃ t : G, t ∉ H := by
    by_contra h
    push Not at h
    apply hHtop
    exact (Subgroup.eq_top_iff' H).mpr h
  have hquotcard : Nat.card (G ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hindex
  have hquot_unique : ∃! z : G ⧸ H, z ≠ 1 :=
    (Nat.card_eq_two_iff' 1).mp hquotcard
  have hsame_coset {g : G} (hg : g ∉ H) : (t : G ⧸ H) = (g : G ⧸ H) := by
    apply hquot_unique.unique
    · exact (QuotientGroup.eq_one_iff t).not.mpr ht
    · exact (QuotientGroup.eq_one_iff g).not.mpr hg
  have hdecomp {g : G} (hg : g ∉ H) : t⁻¹ * g ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    change (t : G ⧸ H)⁻¹ * (g : G ⧸ H) = 1
    rw [hsame_coset hg, inv_mul_cancel]
  have ht2 : t ^ 2 = 1 := houtside t ht
  let eH : Multiplicative (ZMod n) ≃* H := zmodCyclicMulEquiv hHcyc
  let rot (i : ZMod n) : G := (eH (Multiplicative.ofAdd i) : H)
  have hrot_mem (i : ZMod n) : rot i ∈ H := (eH (Multiplicative.ofAdd i)).2
  have hrot_zero : rot 0 = 1 := by
    change ((eH 1 : H) : G) = 1
    rw [map_one]
    rfl
  have hrot_add (i j : ZMod n) : rot (i + j) = rot i * rot j := by
    change ((eH (Multiplicative.ofAdd (i + j)) : H) : G) = _
    rw [show Multiplicative.ofAdd (i + j) =
      Multiplicative.ofAdd i * Multiplicative.ofAdd j from rfl, map_mul]
    rfl
  have hrot_neg (i : ZMod n) : rot (-i) = (rot i)⁻¹ := by
    change ((eH (Multiplicative.ofAdd (-i)) : H) : G) = _
    rw [show Multiplicative.ofAdd (-i) = (Multiplicative.ofAdd i)⁻¹ from rfl, map_inv]
    rfl
  have htrot_not (i : ZMod n) : t * rot i ∉ H := by
    intro h
    apply ht
    have hm := H.mul_mem h (H.inv_mem (hrot_mem i))
    simpa [mul_assoc] using hm
  have htrot2 (i : ZMod n) : (t * rot i) ^ 2 = 1 :=
    houtside (t * rot i) (htrot_not i)
  have hconj (i : ZMod n) : t * rot i * t = rot (-i) := by
    rw [hrot_neg]
    apply eq_inv_of_mul_eq_one_left
    simpa [sq, mul_assoc] using htrot2 i
  have htinv : t⁻¹ = t := by
    have htt : t * t = 1 := by simpa [sq] using ht2
    calc
      t⁻¹ = t⁻¹ * 1 := (mul_one _).symm
      _ = t⁻¹ * (t * t) := by rw [htt]
      _ = t := by simp
  have hcross (i : ZMod n) : rot i * t = t * rot (-i) := by
    calc
      rot i * t = t⁻¹ * (t * rot i * t) := by simp [mul_assoc]
      _ = t * (t * rot i * t) := by rw [htinv]
      _ = t * rot (-i) := by rw [hconj]
  let φ : DihedralGroup n →* G := {
    toFun := fun d => match d with
      | .r i => rot i
      | .sr i => t * rot i
    map_one' := hrot_zero
    map_mul' := by
      intro u v
      cases u with
      | r i =>
          cases v with
          | r j => exact hrot_add i j
          | sr j =>
              change t * rot (j - i) = rot i * (t * rot j)
              symm
              calc
                rot i * (t * rot j) = (rot i * t) * rot j := (mul_assoc ..).symm
                _ = (t * rot (-i)) * rot j := by rw [hcross]
                _ = t * (rot (-i) * rot j) := mul_assoc ..
                _ = t * rot (-i + j) := by rw [hrot_add]
                _ = t * rot (j - i) := by congr 2; abel
      | sr i =>
          cases v with
          | r j =>
              change t * rot (i + j) = (t * rot i) * rot j
              rw [hrot_add, mul_assoc]
          | sr j =>
              change rot (j - i) = (t * rot i) * (t * rot j)
              symm
              calc
                (t * rot i) * (t * rot j) = (t * rot i * t) * rot j :=
                  (mul_assoc (t * rot i) t (rot j)).symm
                _ = rot (-i) * rot j := by rw [hconj]
                _ = rot (-i + j) := (hrot_add _ _).symm
                _ = rot (j - i) := by congr 1; abel }
  have hφsurj : Function.Surjective φ := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨z, hz⟩ := eH.surjective ⟨g, hg⟩
      refine ⟨DihedralGroup.r z.toAdd, ?_⟩
      change rot z.toAdd = g
      exact congrArg Subtype.val hz
    · have hk := hdecomp hg
      obtain ⟨z, hz⟩ := eH.surjective ⟨t⁻¹ * g, hk⟩
      refine ⟨DihedralGroup.sr z.toAdd, ?_⟩
      change t * rot z.toAdd = g
      have hz' : rot z.toAdd = t⁻¹ * g := congrArg Subtype.val hz
      rw [hz']
      simp
  have hcard : Nat.card (DihedralGroup n) = Nat.card G := by
    rw [DihedralGroup.nat_card, ← H.card_mul_index, hindex]
    omega
  have hφbij : Function.Bijective φ :=
    hφsurj.bijective_of_nat_card_le (by rw [hcard])
  exact ⟨(MulEquiv.ofBijective φ hφbij).symm⟩

end

end MetaMathlibExt
