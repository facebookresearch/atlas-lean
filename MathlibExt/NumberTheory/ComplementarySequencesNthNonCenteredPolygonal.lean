/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring

/-!
# Non-centered polygonal numbers

Counting the integers strictly between two successive centered polygonal numbers locates
the requested term of the complementary sequence.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95.
-/

namespace MetaMathlibExt

private def centeredPolygonal (k j : ℕ) : ℕ := k * j * (j + 1) / 2 + 1

private theorem two_mul_centeredPolygonal (k j : ℕ) :
    2 * centeredPolygonal k j = k * j * (j + 1) + 2 := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self j
  have hdvd : 2 ∣ k * j * (j + 1) := ⟨k * t, by rw [mul_assoc, ht]; ring⟩
  have h := Nat.mul_div_cancel' hdvd
  unfold centeredPolygonal
  omega

private theorem centeredPolygonal_strictMono (k : ℕ) (hk : 3 ≤ k) :
    StrictMono (centeredPolygonal k) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h₁ := two_mul_centeredPolygonal k j
  have h₂ := two_mul_centeredPolygonal k (j + 1)
  have hdiff : k * (j + 1) * (j + 1 + 1) =
      k * j * (j + 1) + 2 * (k * (j + 1)) := by ring
  have hC : k * (j + 1) = k * j + k := by ring
  omega

private theorem centeredPolygonal_sqrt_bounds (k n : ℕ) (hk : 0 < k) :
    Nat.sqrt (2 * n / k) ^ 2 * k ≤ 2 * n ∧
      2 * n < (Nat.sqrt (2 * n / k) + 1) ^ 2 * k := by
  refine ⟨(Nat.le_div_iff_mul_le hk).mp (Nat.sqrt_le' _), ?_⟩
  refine (Nat.div_lt_iff_lt_mul hk).mp ?_
  simpa [pow_two] using Nat.lt_succ_sqrt (2 * n / k)

/-- Between two successive values of `c` there are exactly `t + 1` values below `x`, so `x`
is the `(x - (t + 1))`-th non-value of `c`. -/
private theorem nth_of_gap {c : ℕ → ℕ} (hc : StrictMono c) {x t : ℕ}
    (hlo : c t < x) (hhi : x < c (t + 1)) :
    Nat.nth (fun x => ∀ j, c j ≠ x) (x - (t + 1)) = x := by
  classical
  let p := fun x => ∀ j, c j ≠ x
  have hmem : p x := by
    intro m
    rcases le_or_gt m t with hm | hm
    · exact ((hc.monotone hm).trans_lt hlo).ne
    · exact (hhi.trans_le (hc.monotone hm)).ne'
  let vals := (Finset.range (t + 1)).image c
  have hsub : vals ⊆ Finset.range x := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr
      ((hc.monotone (Nat.le_of_lt_succ (Finset.mem_range.mp hm))).trans_lt hlo)
  have hfilter : (Finset.range x).filter p = Finset.range x \ vals := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range, vals,
      Finset.mem_image]
    refine and_congr_right fun hy => ⟨fun hp ⟨m, _, he⟩ => hp m he, fun hv m he => ?_⟩
    exact hv ⟨m, hc.lt_iff_lt.mp (he ▸ hy.trans hhi), he⟩
  have hcount : Nat.count p x = x - (t + 1) := by
    rw [Nat.count_eq_card_filter_range, hfilter, Finset.card_sdiff_of_subset hsub,
      Finset.card_range]
    simp only [vals, Finset.card_image_of_injective _ hc.injective, Finset.card_range]
  change Nat.nth p (x - (t + 1)) = x
  rw [← hcount, Nat.nth_count hmem]

private theorem nth_nonCenteredPolygonal_aux (k n s : ℕ) (hk : 3 ≤ k) (hn : 1 ≤ n)
    (hs : s = Nat.sqrt (2 * n / k)) :
    Nat.nth (fun x => ∀ j, centeredPolygonal k j ≠ x) (n - 1) =
      if k * s * (s + 1) < 2 * (n + s - 1) then n + s else n + s - 1 := by
  classical
  have hkpos : 0 < k := by omega
  obtain ⟨hlo, hhi⟩ := centeredPolygonal_sqrt_bounds k n hkpos
  rw [← hs] at hlo hhi
  have hmono := centeredPolygonal_strictMono k hk
  split_ifs with hcond
  · have hEq := two_mul_centeredPolygonal k s
    have hNext := two_mul_centeredPolygonal k (s + 1)
    have h1 : centeredPolygonal k s < n + s := by omega
    have hdiff : k * (s + 1) * (s + 1 + 1) =
        (s + 1) ^ 2 * k + k * (s + 1) := by ring
    have hC := Nat.mul_le_mul_right (s + 1) hk
    have h2 : n + s < centeredPolygonal k (s + 1) := by omega
    have hmain := nth_of_gap hmono h1 h2
    rwa [show (n + s) - (s + 1) = n - 1 by omega] at hmain
  · by_cases hs0 : s = 0
    · rw [hs0] at hcond ⊢
      have hn1 : n = 1 := by omega
      subst hn1
      have hmem : (fun x => ∀ j, centeredPolygonal k j ≠ x) 0 := by
        intro j
        have h := two_mul_centeredPolygonal k j
        omega
      have hmain : Nat.nth (fun x => ∀ j, centeredPolygonal k j ≠ x)
          (Nat.count (fun x => ∀ j, centeredPolygonal k j ≠ x) 0) = 0 :=
        Nat.nth_count hmem
      rw [Nat.count_zero] at hmain
      simpa using hmain
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have hLast := two_mul_centeredPolygonal k t
      have hCur := two_mul_centeredPolygonal k (t + 1)
      have h1 : centeredPolygonal k t < n + (t + 1) - 1 := by
        have hdiff : k * t * (t + 1) + k * (t + 1) = (t + 1) ^ 2 * k := by ring
        have hk3 := Nat.mul_le_mul_right (t + 1) hk
        omega
      have h2 : n + (t + 1) - 1 < centeredPolygonal k (t + 1) := by omega
      have hmain := nth_of_gap hmono h1 h2
      rwa [show (n + (t + 1) - 1) - (t + 1) = n - 1 by omega] at hmain

@[expose] public section

/-- **Non-centered polygonal numbers.** Let $k \ge 3$; the centered $k$-gonal numbers are
$k j (j + 1)/2 + 1$ for $j \ge 0$. For $n \ge 1$ let $a(n)$ be the $n$-th nonnegative integer that
is not a centered $k$-gonal number (so $a(1) = 0$), and let $s = \lfloor \sqrt{2n/k} \rfloor$.
Then $a(n) = n + s$ if $k s (s + 1) < 2(n + s - 1)$, and $a(n) = n + s - 1$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 8. -/
public theorem nth_nonCenteredPolygonal (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / k)
    Nat.nth (fun x => ∀ j, k * j * (j + 1) / 2 + 1 ≠ x) (n - 1) =
      if k * s * (s + 1) < 2 * (n + s - 1) then n + s else n + s - 1 := by
  exact nth_nonCenteredPolygonal_aux k n _ hk hn rfl

end

end MetaMathlibExt
