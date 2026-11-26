/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup.Symbolic
public import Mathlib.GroupTheory.Coset.Card

/-!
# Agreement of affine labels on a prime-power component

The collision estimate in A. V. Sutherland, *18.783 Elliptic Curves*, MIT, Spring 2013,
Lecture 11, §11.1, proof of Theorem 11.1, equation (2), must allow zero divisors. Here the
estimate follows by counting: a nonempty agreement set with unequal slopes is a translate of
a proper additive subgroup. Its size divides the prime power and is strictly smaller than it.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

open Finset

/-- Two different affine forms modulo `p^(e+1)` agree at no more than `p^e` inputs, a
`1/p` fraction of the uniform domain. No invertibility of the slope difference is required. -/
theorem affEval_eq_card_le_primePow {p e : ℕ} [Fact p.Prime] {u v : Aff (p ^ (e + 1))}
    (huv : u ≠ v) : (univ.filter fun x => affEval x u = affEval x v).card ≤ p ^ e := by
  classical
  let s := univ.filter fun x => affEval x u = affEval x v
  change s.card ≤ p ^ e
  obtain hs | hs := s.eq_empty_or_nonempty
  · simp [hs]
  obtain ⟨x₀, hx₀⟩ := hs
  have at_root (x) (hx : x ∈ s) : u.1 + u.2 * x = v.1 + v.2 * x := (mem_filter.mp hx).2
  have h₀ := at_root x₀ hx₀
  have hne : u.2 - v.2 ≠ 0 := by
    refine sub_ne_zero.mpr fun h => huv (Prod.ext ?_ h)
    rw [h] at h₀
    exact add_right_cancel h₀
  let f := AddMonoidHom.mulLeft (u.2 - v.2)
  -- Subtracting one solution embeds all solutions in the kernel of multiplication by the slope.
  have hbound : s.card ≤ Nat.card f.ker := by
    rw [← Fintype.card_coe, Nat.card_eq_fintype_card]
    let shift (x : s) : f.ker := ⟨x.val - x₀, by
      change (u.2 - v.2) * (x.val - x₀) = 0
      linear_combination at_root x.val x.property - h₀⟩
    exact Fintype.card_le_of_injective shift fun x y h =>
      Subtype.ext (sub_left_inj.mp (congrArg Subtype.val h))
  have hproper : Nat.card f.ker < p ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card]
    refine lt_of_lt_of_eq ?_ (ZMod.card (p ^ (e + 1)))
    apply Fintype.card_subtype_lt (x := 1)
    change ¬ (u.2 - v.2) * 1 = 0
    simpa using hne
  have hdvd : Nat.card f.ker ∣ p ^ (e + 1) := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using f.ker.card_addSubgroup_dvd_card
  obtain ⟨j, hj, hjcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hj' : j ≤ e := by
    rw [hjcard] at hproper
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hproper)
  exact hbound.trans (hjcard ▸ Nat.pow_le_pow_right (Fact.out : p.Prime).pos hj')

end Cslib.Crypto.Framework.GenericGroup
