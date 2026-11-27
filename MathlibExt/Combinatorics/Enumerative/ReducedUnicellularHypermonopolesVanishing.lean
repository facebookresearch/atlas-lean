/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Fin
public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles

/-!
# Vanishing of the reduced unicellular hypermonopole counts

We prove that the counts vanish for odd differences between the size and the number of cycles,
and that the first nonzero count occurs at size three.
-/

namespace MetaMathlibExt

namespace reduced_unicellular_hypermonopoles_finRotate_vanishing

private theorem cycleCount_zero (σ : Equiv.Perm (Fin 0)) : cycleQuotientCount σ = 0 := by
  rw [Subsingleton.elim σ 1]
  simp [cycleQuotientCount_eq]

private theorem sign_eq_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.sign = (-1 : ℤˣ) ^ (n + cycleQuotientCount σ) := by
  have hsum : σ.cycleType.sum ≤ n := by simpa using σ.sum_cycleType_le
  -- Including the fixed points increases the exponent by twice their number.
  rw [Equiv.Perm.sign_of_cycleType, cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints,
    Fintype.card_fin]
  apply neg_one_pow_congr
  simp only [Nat.even_iff]
  omega

private theorem even_sub_of_face_cycle {n : ℕ} (α : Equiv.Perm (Fin n))
    (hface : cycleQuotientCount (α⁻¹ * finRotate n) = 1) :
    Even ((n : ℤ) - cycleQuotientCount α) := by
  by_cases hn : n = 0
  · subst n
    simp [cycleCount_zero] at hface
  have hface_sign : (α⁻¹ * finRotate n).sign = (finRotate n).sign := by
    rw [sign_eq_pow, hface, sign_finRotate, show n + 1 = (n - 1) + 2 by omega]
    simp [pow_add, pow_two]
  have hsign : α.sign = 1 := by
    rw [map_mul, map_inv] at hface_sign
    exact inv_eq_one.mp (mul_right_cancel (hface_sign.trans (one_mul _).symm))
  rw [sign_eq_pow] at hsign
  have heven := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hsign
  simp only [Nat.even_iff] at heven
  simp only [Int.even_iff]
  omega

end reduced_unicellular_hypermonopoles_finRotate_vanishing

open reduced_unicellular_hypermonopoles_finRotate_vanishing in
/-- **Vanishing of the reduced unicellular hypermonopole counts.** Let $\sigma_n$ be the cyclic
permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$, write $z(\pi)$ for the
number of cycles of a permutation $\pi$, fixed points included, and let $r(n, k)$ be the number
of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with no fixed point such that
$z(\alpha^{-1} \circ \sigma_n) = 1$ and $z(\alpha) = k$. Then $r(n, k) = 0$ for all natural
numbers $n$ and $k$ with $n - k$ odd; $r(3, k) > 0$ for some natural number $k$ with $2k \le 3$;
and $r(n, k) = 0$ whenever $n < 3$ and $2k \le n$.

So the least $n$ with $r(n, k) > 0$ for some $k \le n / 2$ is $n = 3$. In the terms of the
source, $r(n, k)$ counts the reduced unicellular hypermonopoles $(\sigma_n, \alpha)$ with
$\sigma_n = (1, \dots, n)$ and $z(\alpha) = k$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 13 (`jis-2025-25.3.3-cor-13`). -/
public theorem reduced_unicellular_hypermonopoles_finRotate_vanishing :
    (∀ n k : ℕ, Odd ((n : ℤ) - k) →
      Fintype.card {α : Equiv.Perm (Fin n) //
        cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k} = 0) ∧
    (∃ k : ℕ, 2 * k ≤ 3 ∧
      0 < Fintype.card {α : Equiv.Perm (Fin 3) //
        cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k}) ∧
    ∀ n < 3, ∀ k : ℕ, 2 * k ≤ n →
      Fintype.card {α : Equiv.Perm (Fin n) //
        cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k} = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k hodd
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun ⟨α, hface, _, hcycles⟩ ↦ ?_⟩
    have heven := even_sub_of_face_cycle α hface
    rw [hcycles] at heven
    exact (Int.not_even_iff_odd.mpr hodd) heven
  · refine ⟨1, by decide, Fintype.card_pos_iff.mpr ⟨(finRotate 3)⁻¹, ?_⟩⟩
    have hface : ((finRotate 3)⁻¹)⁻¹ * finRotate 3 = (finRotate 3)⁻¹ :=
      Equiv.ext (by decide)
    have hred : ∀ i, (finRotate 3)⁻¹ i ≠ i := by decide
    obtain ⟨hlower, hupper⟩ :=
      cycleCount_bounds_of_reduced (n := 3) (by decide) (finRotate 3)⁻¹ hred
    have hcount : cycleQuotientCount (finRotate 3)⁻¹ = 1 := by omega
    exact ⟨by rw [hface, hcount], hred, hcount⟩
  · intro n hn k hkn
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun ⟨α, hface, hred, hcycles⟩ ↦ ?_⟩
    by_cases hn0 : n = 0
    · subst n
      simp [cycleCount_zero] at hface
    have hlower := (cycleCount_bounds_of_reduced (by omega) α hred).1
    have heven := even_sub_of_face_cycle α hface
    simp only [hcycles, Int.even_iff] at heven
    omega

end MetaMathlibExt
