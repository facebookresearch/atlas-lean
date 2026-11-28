/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Reindexing by an affine map modulo `n`

For an integer `α` prime to `n`, the map `b ↦ (m + α b) mod n` permutes the residues
`0, 1, …, n - 1`, and `b ↦ α b mod n` permutes the nonzero residues `1, …, n - 1`. Sums of
a function of these residues are therefore unchanged by the reindexing.

## Main statements

* `Finset.sum_range_add_mul_emod`: `∑_{b < n} f ((m + α b) mod n) = ∑_{c < n} f c`.
* `Finset.sum_Icc_mul_emod`: `∑_{b = 1}^{n - 1} f (α b mod n) = ∑_{c = 1}^{n - 1} f c`.
-/

@[expose] public section

namespace Finset

/-- For `α` prime to `n`, the affine map `b ↦ (m + α b) mod n` permutes `range n`, so
`∑_{b < n} f ((m + α b) mod n) = ∑_{c < n} f c`. -/
theorem sum_range_add_mul_emod {M : Type*} [AddCommMonoid M] {n : ℕ} {α : ℤ}
    (hα : IsCoprime α (n : ℤ)) (m : ℤ) (f : ℤ → M) :
    ∑ b ∈ range n, f ((m + α * b) % (n : ℤ)) = ∑ c ∈ range n, f (c : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hp0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hppos : (0 : ℤ) < n := by exact_mod_cast hn
  let g : ℕ → ℕ := fun b => ((m + α * b) % (n : ℤ)).toNat
  have hg : ∀ b, ((g b : ℕ) : ℤ) = (m + α * b) % (n : ℤ) := fun b =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
  have maps : ∀ b ∈ range n, g b ∈ range n := by
    intro b _
    have h1 := hg b
    have h2 := Int.emod_lt_of_pos (m + α * b) hppos
    rw [mem_range]
    omega
  have inj : Set.InjOn g (range n) := by
    intro b hb b' hb' h
    simp only [coe_range, Set.mem_Iio] at hb hb'
    have h1 : (m + α * b) % (n : ℤ) = (m + α * b') % (n : ℤ) := by rw [← hg, ← hg, h]
    have hd : (n : ℤ) ∣ α * ((b' : ℤ) - b) := by
      have := Int.ModEq.dvd h1
      have e : m + α * (b' : ℤ) - (m + α * b) = α * ((b' : ℤ) - b) := by ring
      rwa [e] at this
    have hd' := hα.symm.dvd_of_dvd_mul_left hd
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd' (by omega)
    omega
  have himg : (range n).image g = range n :=
    eq_of_subset_of_card_le (image_subset_iff.2 maps) (by rw [card_image_of_injOn inj])
  conv_rhs => rw [← himg, sum_image inj]
  exact sum_congr rfl fun b _ => by rw [hg]

/-- For `α` prime to `n`, the map `b ↦ α b mod n` permutes `{1, …, n - 1}`, so
`∑_{b = 1}^{n - 1} f (α b mod n) = ∑_{c = 1}^{n - 1} f c`. -/
theorem sum_Icc_mul_emod {M : Type*} [AddCommMonoid M] {n : ℕ} {α : ℤ}
    (hα : IsCoprime α (n : ℤ)) (f : ℤ → M) :
    ∑ b ∈ Icc 1 (n - 1), f (α * b % (n : ℤ)) = ∑ c ∈ Icc 1 (n - 1), f (c : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hp0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hppos : (0 : ℤ) < n := by exact_mod_cast hn
  let g : ℕ → ℕ := fun b => (α * b % (n : ℤ)).toNat
  have hg : ∀ b, ((g b : ℕ) : ℤ) = α * b % (n : ℤ) := fun b =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
  have maps : ∀ b ∈ Icc 1 (n - 1), g b ∈ Icc 1 (n - 1) := by
    intro b hb
    rw [mem_Icc] at hb ⊢
    have h1 := hg b
    have h2 := Int.emod_lt_of_pos (α * b) hppos
    have h3 : α * b % (n : ℤ) ≠ 0 := by
      intro h0
      have hd := hα.symm.dvd_of_dvd_mul_left (Int.dvd_of_emod_eq_zero h0)
      have := Int.le_of_dvd (by omega) hd
      omega
    omega
  have inj : Set.InjOn g (Icc 1 (n - 1)) := by
    intro b hb b' hb' h
    simp only [coe_Icc, Set.mem_Icc] at hb hb'
    have h1 : α * b % (n : ℤ) = α * b' % (n : ℤ) := by rw [← hg, ← hg, h]
    have hd : (n : ℤ) ∣ α * ((b' : ℤ) - b) := by
      rw [mul_sub]; exact Int.ModEq.dvd h1
    have hd' := hα.symm.dvd_of_dvd_mul_left hd
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd' (by omega)
    omega
  have himg : (Icc 1 (n - 1)).image g = Icc 1 (n - 1) :=
    eq_of_subset_of_card_le (image_subset_iff.2 maps) (by rw [card_image_of_injOn inj])
  conv_rhs => rw [← himg, sum_image inj]
  exact sum_congr rfl fun b _ => by rw [hg]

end Finset
