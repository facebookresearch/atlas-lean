/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.OddExponentCosetFreePartition
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.Coset.Basic

/-! # Tests for coset-free partitions in odd exponent -/

namespace MathlibExtTest.OddExponentCosetFreePartition

open MathlibExt.GroupTheory.OddExponentCosetFreePartitionKourovka13Problem46Wanted
open scoped Pointwise

private abbrev V := Multiplicative (ℕ → ZMod 3)
private abbrev G := V × Multiplicative (ZMod 5)

-- In this uncountable group of mixed exponent, every slice at a fixed second
-- coordinate must contain points of both colors, with one partition for all five slices.
example : ∃ A B : Set G, A ∪ B = Set.univ ∧ Disjoint A B ∧
    ∀ t : Multiplicative (ZMod 5), (∃ v : V, (v, t) ∈ A) ∧ ∃ w : V, (w, t) ∈ B := by
  classical
  have : Uncountable V := by
    apply uncountable_iff_forall_not_surjective.mpr
    intro f h
    obtain ⟨j, hj⟩ := h (Multiplicative.ofAdd (fun i ↦ (f i).toAdd i + 1))
    have he := congrArg (fun v : V ↦ v.toAdd j) hj
    change (f j).toAdd j = (f j).toAdd j + 1 at he
    simp at he
  have hd : Monoid.exponent G ∣ 15 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Prod.ext
    · change 15 • x.1.toAdd = 0
      ext i
      change 15 • (x.1.toAdd i) = 0
      rw [nsmul_eq_mul, show ((15 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    · change 15 • x.2.toAdd = 0
      rw [nsmul_eq_mul, show ((15 : ℕ) : ZMod 5) = 0 by decide, zero_mul]
  obtain ⟨A, B, hcover, hdisj, hs⟩ := oddExponentCosetFreePartition_holds G
    (Prod.mk_left_injective (1 : Multiplicative (ZMod 5))).uncountable
    (fun h ↦ by simp [h] at hd) (Odd.of_dvd_nat (by decide : Odd 15) hd)
  let H := (MonoidHom.snd V (Multiplicative (ZMod 5))).ker
  have : Infinite H := Infinite.of_injective
    (fun v : V ↦ (⟨(v, 1), rfl⟩ : H)) (fun _ _ h ↦ congrArg (fun x : H ↦ x.val.1) h)
  refine ⟨A, B, hcover, hdisj, fun t ↦ ?_⟩
  let g : G := (1, t)
  have slice (x : G) (hx : x ∈ g • (H : Set G)) : x.2 = t := by
    obtain ⟨y, hy, rfl⟩ := hx
    change y.2 = 1 at hy
    change t * y.2 = t
    rw [hy, mul_one]
  have hit (S T : Set G) (hc : S ∪ T = Set.univ) (hn : ¬ g • (H : Set G) ⊆ T) :
      ∃ v : V, (v, t) ∈ S := by
    obtain ⟨x, hx, hout⟩ := Set.not_subset.mp hn
    have hin : x ∈ S ∪ T := hc ▸ Set.mem_univ x
    exact ⟨x.1, slice x hx ▸ hin.resolve_right hout⟩
  obtain ⟨hna, hnb⟩ := hs H (Set.infinite_coe_iff.mp inferInstance) g
  exact ⟨hit A B hcover hnb, hit B A (Set.union_comm A B ▸ hcover) hna⟩

end MathlibExtTest.OddExponentCosetFreePartition
