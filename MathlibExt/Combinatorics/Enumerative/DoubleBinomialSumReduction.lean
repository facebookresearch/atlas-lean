/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde

@[expose] public section

namespace MetaMathlibExt

/-! # Double binomial sum reduction
-/

/--
**Reduction of a double binomial absolute-value sum.** For all natural numbers $\beta$, $m$ and
$n$,

$$\sum_{i=0}^{2m} \sum_{j=0}^{2n} \binom{2m}{i} \binom{2n}{j} \lvert (i-m)-(j-n) \rvert^{\beta}
= \sum_{k=0}^{2(m+n)} \binom{2(m+n)}{k} \lvert k-m-n \rvert^{\beta},$$

with the convention $0^0 = 1$.

In the source's notation, $S_\beta(n) = \sum_k \binom{2n}{n+k} \lvert k \rvert^\beta$ and
$T_\beta(m,n) = \sum_{k,\ell} \binom{2m}{m+k} \binom{2n}{n+\ell} \lvert k-\ell \rvert^\beta$, and
the identity reads $T_\beta(m,n) = S_\beta(m+n)$, after the shift $i = m + k$, $j = n + \ell$.

Source: Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, and Helmut
Prodinger, "Some Binomial Sums Involving Absolute Values," Journal of Integer
Sequences 19 (2016), Article 16.3.7, Theorem (label thm:reduce2to1),
lines 278–283 (with `S_β` defined at lines 245–247 and `T_β` at 271–274),
https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
-/
theorem double_binomial_sum_eq_single_binomial_sum
    (β m n : ℕ) :
    Finset.sum (Finset.range (2 * m + 1)) (fun i =>
      Finset.sum (Finset.range (2 * n + 1)) (fun j =>
        Nat.choose (2 * m) i * Nat.choose (2 * n) j *
          Int.natAbs ((i : ℤ) - (m : ℤ) - ((j : ℤ) - (n : ℤ))) ^ β)) =
      Finset.sum (Finset.range (2 * (m + n) + 1)) (fun k =>
        Nat.choose (2 * (m + n)) k *
          Int.natAbs ((k : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) := by
  -- Vandermonde fiber identity.
  have hfib : ∀ s ∈ Finset.range (2 * (m + n) + 1),
      (∑ x ∈ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)) with x.1 + x.2 = s,
        Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2) =
      Nat.choose (2 * (m + n)) s := by
    intro s _
    have hN : 2 * (m + n) = 2 * m + 2 * n := by ring
    have hvand : Nat.choose (2 * m + 2 * n) s =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s,
          Nat.choose (2 * m) ij.1 * Nat.choose (2 * n) ij.2 :=
      Nat.add_choose_eq (2 * m) (2 * n) s
    have hsub : (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun x => x.1 + x.2 = s) ⊆ Finset.HasAntidiagonal.antidiagonal s := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      exact hx.2
    have hzero : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal s,
        x ∉ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)).filter
          (fun x => x.1 + x.2 = s) →
        Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 = 0 := by
      intro x hx hxnot
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hxnot
      by_cases h1 : x.1 < 2 * m + 1
      · by_cases h2 : x.2 < 2 * n + 1
        · exfalso; exact hxnot ⟨⟨h1, h2⟩, hx⟩
        · have hlt : 2 * n < x.2 := by omega
          rw [Nat.choose_eq_zero_of_lt hlt, mul_zero]
      · have hlt : 2 * m < x.1 := by omega
        rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
    rw [hN, hvand]
    exact Finset.sum_subset hsub hzero
  -- Reflecting the inner sum (j ↦ 2n - j) turns the index difference into a sum.
  have hrefl : ∀ i ∈ Finset.range (2 * m + 1),
      (∑ j ∈ Finset.range (2 * n + 1),
        Nat.choose (2 * m) i * Nat.choose (2 * n) j *
          Int.natAbs ((i : ℤ) - (m : ℤ) - ((j : ℤ) - (n : ℤ))) ^ β) =
      (∑ j' ∈ Finset.range (2 * n + 1),
        Nat.choose (2 * m) i * Nat.choose (2 * n) j' *
          Int.natAbs (((i + j' : ℕ) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) := by
    intro i _
    have h := (Finset.sum_range_reflect
      (fun j => Nat.choose (2 * m) i * Nat.choose (2 * n) j *
        Int.natAbs ((i : ℤ) - (m : ℤ) - ((j : ℤ) - (n : ℤ))) ^ β) (2 * n + 1)).symm
    rw [h]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hj2 : j ≤ 2 * n := by omega
    have hidx : 2 * n + 1 - 1 - j = 2 * n - j := by omega
    rw [hidx]
    have hchoose : Nat.choose (2 * n) (2 * n - j) = Nat.choose (2 * n) j :=
      Nat.choose_symm hj2
    rw [hchoose]
    have heq : (i : ℤ) - (m : ℤ) - (((2 * n - j : ℕ) : ℤ) - (n : ℤ)) =
        (((i + j : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ) := by
      have h1 : (((i + j : ℕ)) : ℤ) = (i : ℤ) + (j : ℤ) := by push_cast; ring
      have hcast : ((2 * n - j : ℕ) : ℤ) = 2 * (n : ℤ) - (j : ℤ) := by
        rw [Nat.cast_sub hj2]; push_cast; ring
      omega
    rw [heq]
  have hmaps : ∀ x ∈ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)),
      x.1 + x.2 ∈ Finset.range (2 * (m + n) + 1) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  have hinner : ∀ s ∈ Finset.range (2 * (m + n) + 1),
      (∑ x ∈ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)) with x.1 + x.2 = s,
        Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 *
          Int.natAbs ((((x.1 + x.2 : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) =
      Nat.choose (2 * (m + n)) s * Int.natAbs ((s : ℤ) - (m : ℤ) - (n : ℤ)) ^ β := by
    intro s hs
    have hE : ∀ x ∈ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun x => x.1 + x.2 = s),
        (Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 *
          Int.natAbs ((((x.1 + x.2 : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) =
        (Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2) *
          Int.natAbs ((s : ℤ) - (m : ℤ) - (n : ℤ)) ^ β := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      congr 1
      congr 1
      congr 1
      rw [hx.2]
    rw [Finset.sum_congr rfl hE, ← Finset.sum_mul, hfib s hs]
  calc Finset.sum (Finset.range (2 * m + 1)) (fun i =>
        Finset.sum (Finset.range (2 * n + 1)) (fun j =>
          Nat.choose (2 * m) i * Nat.choose (2 * n) j *
            Int.natAbs ((i : ℤ) - (m : ℤ) - ((j : ℤ) - (n : ℤ))) ^ β))
      = Finset.sum (Finset.range (2 * m + 1)) (fun i =>
        Finset.sum (Finset.range (2 * n + 1)) (fun j' =>
          Nat.choose (2 * m) i * Nat.choose (2 * n) j' *
            Int.natAbs (((i + j' : ℕ) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β)) :=
        Finset.sum_congr rfl (fun i hi => hrefl i hi)
    _ = ∑ x ∈ (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)),
        Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 *
          Int.natAbs ((((x.1 + x.2 : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β :=
        (Finset.sum_product _ _ (fun x =>
          Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 *
            Int.natAbs ((((x.1 + x.2 : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β)).symm
    _ = ∑ s ∈ Finset.range (2 * (m + n) + 1), ∑ x ∈
        (Finset.range (2 * m + 1) ×ˢ Finset.range (2 * n + 1)) with x.1 + x.2 = s,
        Nat.choose (2 * m) x.1 * Nat.choose (2 * n) x.2 *
          Int.natAbs ((((x.1 + x.2 : ℕ)) : ℤ) - (m : ℤ) - (n : ℤ)) ^ β :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = Finset.sum (Finset.range (2 * (m + n) + 1)) (fun k =>
        Nat.choose (2 * (m + n)) k *
          Int.natAbs ((k : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) :=
        Finset.sum_congr rfl (fun s hs => hinner s hs)

end MetaMathlibExt
