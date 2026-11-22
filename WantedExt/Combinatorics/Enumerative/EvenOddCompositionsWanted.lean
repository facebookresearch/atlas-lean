/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite

namespace MetaMathlibExt

@[expose] public section

/-! A composition or partition is even (odd) if its number of parts is even
(odd). Compositions are Mathlib's `Composition`, partitions are
`Nat.Partition`, and partitions into distinct parts are
`Nat.Partition.distincts`. -/

open Classical in
/-- The signed count `c_o - c_e` of compositions of `N` satisfying `P`: the
number of odd compositions minus the number of even ones, i.e. the sum of
`(-1) ^ (length + 1)`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Section 1. -/
public noncomputable def compositionOddMinusEven (N : ℕ) (P : Composition N → Prop) : ℤ :=
  ∑ c : Composition N, if P c then (-1) ^ (c.length + 1) else 0

/-- The empty composition of `0` is even, so the signed count of all
compositions of `0` is `-1`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Section 1. -/
public theorem compositionOddMinusEven_zero_true :
    compositionOddMinusEven 0 (fun _ => True) = -1 := by
  have h : ∀ c : Composition 0, c = Composition.ones 0 := fun c =>
    Composition.eq_ones_iff.2 fun i hi => by
      have h1 := c.blocks_pos hi
      have h2 : i ≤ c.blocks.sum := List.le_sum_of_mem hi
      rw [c.blocks_sum] at h2
      omega
  rw [compositionOddMinusEven,
    Fintype.sum_eq_single (Composition.ones 0) fun c hc => absurd (h c) hc]
  simp

/-- The restriction on the parts less than `k` in the compositions of
Theorem 15: every part `a < k` sits at a position `i > 0` whose preceding part
is at least `k`, and it is followed by a part which is either the last part
or greater than `k` (so `a` is not itself the last part).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15. -/
public def IsHuangSmallPartPlacement (k : ℕ) (L : List ℕ) : Prop :=
  ∀ (i a : ℕ), L[i]? = some a → a < k →
    0 < i ∧ (∃ b, L[i - 1]? = some b ∧ k ≤ b) ∧
      ∃ c, L[i + 1]? = some c ∧ (i + 2 = L.length ∨ k < c)

/-- A list with no part less than `k` satisfies the placement condition
vacuously.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15. -/
public theorem isHuangSmallPartPlacement_of_forall_le {k : ℕ} {L : List ℕ}
    (h : ∀ a ∈ L, k ≤ a) : IsHuangSmallPartPlacement k L := by
  intro i a hi ha
  have := h a (List.mem_of_getElem? hi)
  omega

/-- Theorem 1 (Legendre): the number of even partitions of `n` into distinct
parts minus the number of odd ones is `(-1)^j` if `n = j(3j ± 1)/2` for some
`j ≥ 0`, and `0` otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 1 (Legendre)
(`jis-2024-24.6.5-thm-1`). -/
public theorem_wanted sum_distincts_neg_one_pow_card (n : ℕ) :
    (∀ j : ℕ, 2 * n = j * (3 * j + 1) ∨ 2 * n = j * (3 * j - 1) →
        ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, 2 * n ≠ j * (3 * j + 1) ∧ 2 * n ≠ j * (3 * j - 1)) →
        ∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ p.parts.card = 0)

/-- Theorem 5: `b_n = c_{n,o} - c_{n,e}`, the signed count of compositions of
`n + 1` with parts greater than one, is `(-1)^j` if `n ∈ {3j+1, 3j+2}` and `0`
otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 5
(`jis-2024-24.6.5-thm-5`). -/
public theorem_wanted compositionOddMinusEven_parts_gt_one (n : ℕ) :
    (∀ j : ℕ, n = 3 * j + 1 ∨ n = 3 * j + 2 →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ 3 * j + 1 ∧ n ≠ 3 * j + 2) →
        compositionOddMinusEven (n + 1) (fun c => ∀ a ∈ c.blocks, 1 < a) = 0)

/-- Theorem 8: for `k, n ≥ 1`, the signed count `b_{k,n}` of compositions of
`n + k - 1` with parts at least `k` is
`∑_{0 ≤ j ≤ (n-1)/k} (-1)^j binom(n - 1 - j(k-1), j)`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 8
(`jis-2024-24.6.5-thm-8`). -/
public theorem_wanted compositionOddMinusEven_parts_ge (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1) (fun c => ∀ a ∈ c.blocks, k ≤ a)
      = ∑ j ∈ Finset.range ((n - 1) / k + 1),
          (-1 : ℤ) ^ j * ((n - 1 - j * (k - 1)).choose j : ℤ)

/-- Theorem 9 (Nyirenda), first part: for `r ≥ 1`, the number of partitions
of `n` into an even number of distinct parts, all congruent to `0` or
`2r ± 1` modulo `4r`, minus the number with an odd number of such parts, is
`(-1)^j` if `n = j(2rj ± 1)` for some `j ≥ 0`, and `0` otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 9 (Nyirenda)
(`jis-2024-24.6.5-thm-9`). -/
public theorem_wanted sum_distincts_mod_four_mul_neg_one_pow_card (r n : ℕ) (hr : 1 ≤ r) :
    (∀ j : ℕ, n = j * (2 * r * j + 1) ∨ n = j * (2 * r * j - 1) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (4 * r) = 0 ∨ a % (4 * r) = 2 * r + 1 ∨ a % (4 * r) = 2 * r - 1),
          (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ j * (2 * r * j + 1) ∧ n ≠ j * (2 * r * j - 1)) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (4 * r) = 0 ∨ a % (4 * r) = 2 * r + 1 ∨ a % (4 * r) = 2 * r - 1),
          (-1 : ℤ) ^ p.parts.card = 0)

/-- Theorem 9 (Nyirenda), second part: for `r ≥ 1`, the number of partitions
of `n` into an even number of distinct parts, all congruent to `0` or `±r`
modulo `2r + 1`, minus the number with an odd number of such parts, is
`(-1)^j` if `n = j((2r+1)j ± 1)/2` for some `j ≥ 0`, and `0` otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 9 (Nyirenda)
(`jis-2024-24.6.5-thm-9`). -/
public theorem_wanted sum_distincts_mod_two_mul_add_one_neg_one_pow_card (r n : ℕ)
    (hr : 1 ≤ r) :
    (∀ j : ℕ, 2 * n = j * ((2 * r + 1) * j + 1) ∨ 2 * n = j * ((2 * r + 1) * j - 1) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (2 * r + 1) = 0 ∨ a % (2 * r + 1) = r ∨ a % (2 * r + 1) = r + 1),
          (-1 : ℤ) ^ p.parts.card = (-1) ^ j) ∧
      ((∀ j : ℕ, 2 * n ≠ j * ((2 * r + 1) * j + 1) ∧ 2 * n ≠ j * ((2 * r + 1) * j - 1)) →
        ∑ p ∈ (Nat.Partition.distincts n).filter (fun p => ∀ a ∈ p.parts,
            a % (2 * r + 1) = 0 ∨ a % (2 * r + 1) = r ∨ a % (2 * r + 1) = r + 1),
          (-1 : ℤ) ^ p.parts.card = 0)

/-- Theorem 10: for `k, n ≥ 1` and `r > s ≥ 0`, the signed count
`b^{r,s}_{k,n}` of compositions of `n + k - 1` with parts at least `k` and
congruent to `k + s` modulo `r` is `∑_{ri + j(k+s) = n-1-s} (-1)^j binom(i+j, i)`
over `i, j ≥ 0` (an empty sum when `n ≤ s`).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 10
(`jis-2024-24.6.5-thm-10`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq (k n r s : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hsr : s < r) :
    compositionOddMinusEven (n + k - 1)
        (fun c => ∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if r * i + j * (k + s) + s + 1 = n then (-1 : ℤ) ^ j * ((i + j).choose i : ℤ)
          else 0

/-- Corollary 12: if `r > s ≥ 0` and `k = r - s`, then `b^{r,s}_{k,n} = 1` for
`n = s + 1` and `0` for every other `n ≥ 1`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Corollary 12
(`jis-2024-24.6.5-cor-12`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq_sub (n r s : ℕ) (hn : 1 ≤ n)
    (hsr : s < r) :
    compositionOddMinusEven (n + (r - s) - 1)
        (fun c => ∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r)
      = if n = s + 1 then 1 else 0

/-- Corollary 13: if `r > s ≥ 0` and `k = 2r - s`, then `b^{r,s}_{k,n} = (-1)^j`
if `n ∈ {3rj + s + 1, 3rj + r + s + 1}` for some `j ≥ 0`, and `0` otherwise.
The record writes `d^{r,s}_{k,n}`; the paper's proof computes `b^{r,s}_{k,n}`
of Theorem 10, which is the quantity stated here.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Corollary 13
(`jis-2024-24.6.5-cor-13`). -/
public theorem_wanted compositionOddMinusEven_parts_ge_modEq_two_mul_sub (n r s : ℕ)
    (hn : 1 ≤ n) (hsr : s < r) :
    (∀ j : ℕ, n = 3 * r * j + s + 1 ∨ n = 3 * r * j + r + s + 1 →
        compositionOddMinusEven (n + (2 * r - s) - 1)
          (fun c => ∀ a ∈ c.blocks, 2 * r - s ≤ a ∧ a % r = (2 * r - s + s) % r)
          = (-1) ^ j) ∧
      ((∀ j : ℕ, n ≠ 3 * r * j + s + 1 ∧ n ≠ 3 * r * j + r + s + 1) →
        compositionOddMinusEven (n + (2 * r - s) - 1)
          (fun c => ∀ a ∈ c.blocks, 2 * r - s ≤ a ∧ a % r = (2 * r - s + s) % r) = 0)

/-- Theorem 14 (Franklin): for `k ≥ 1` and `m ≥ 0`, the number of partitions
of `n` in which exactly `m` distinct part sizes occur `k` or more times equals
the number of partitions of `n` with exactly `m` distinct part sizes divisible
by `k`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 14 (Franklin)
(`jis-2024-24.6.5-thm-14`). -/
public theorem_wanted card_partition_franklin (k m n : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter fun p : n.Partition =>
        (p.parts.toFinset.filter fun a => k ≤ p.parts.count a).card = m).card
      = (Finset.univ.filter fun p : n.Partition =>
        (p.parts.toFinset.filter fun a => k ∣ a).card = m).card

/-- Theorem 15 (Huang): for `k ≥ 1`, `m ≥ 0` and `n ≥ 1`, the number of
compositions of `n` with exactly `m` parts not congruent to `1` modulo `k`,
each greater than `k`, equals the number of compositions of `n + k - 1` with
exactly `m` parts less than `k`, each preceded by a part at least `k` and
followed by either the last part or a part greater than `k`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 15 (Huang)
(`jis-2024-24.6.5-thm-15`). -/
public theorem_wanted card_composition_huang_franklin (k m n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    Nat.card {c : Composition n //
        (c.blocks.filter fun a => a % k ≠ 1 % k).length = m ∧
          ∀ a ∈ c.blocks, a % k ≠ 1 % k → k < a}
      = Nat.card {c : Composition (n + k - 1) //
        (c.blocks.filter fun a => a < k).length = m ∧ IsHuangSmallPartPlacement k c.blocks}

/-- Theorem 16, second formula: for `k, n ≥ 1`, the signed count `b^{(m)}_{k,n}`
of the compositions of `n + k - 1` in Theorem 15 (exactly `m` parts less than
`k`, placed as in `IsHuangSmallPartPlacement`) is
`∑_{i + (k+1)m + jk + ℓ(k-1) + h = n} (-1)^{ℓ+j} binom(i,m) binom(i+j-1,j) binom(m,ℓ) binom(m+h-1,h)`.
The `ℕ`-truncated `binom(i+j-1, j)` and `binom(m+h-1, h)` agree with the
paper's values (`binom(-1, 0) = 1`).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16
(`jis-2024-24.6.5-thm-16`). -/
public theorem_wanted compositionOddMinusEven_huang_eq_sum (k m n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1)
        (fun c => (c.blocks.filter fun a => a < k).length = m ∧
          IsHuangSmallPartPlacement k c.blocks)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ h ∈ Finset.range (n + 1),
            if i + (k + 1) * m + j * k + l * (k - 1) + h = n then
              (-1 : ℤ) ^ (l + j) * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ) *
                (m.choose l : ℤ) * ((m + h - 1).choose h : ℤ)
            else 0

/-- Theorem 16, first formula: for `k ≥ 2` and `n ≥ 1`,
`b^{(m)}_{k,n} = ∑_{λ ⊆ (k-2)^m, i + (k+1)m + jk + |λ| = n} (-1)^j binom(i,m) binom(i+j-1,j) m_λ(1^m)`.
Deviation in form: `∑_λ m_λ(1^m) [|λ| = t]` is the number of functions
`g : Fin m → {0, …, k-2}` with `∑ g = t` (the multinomial `m_λ(1^m)` counts the
distinct arrangements of `λ` padded by zeros to length `m`), so the sum over
`λ` is written as a sum over such `g`.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16
(`jis-2024-24.6.5-thm-16`). -/
public theorem_wanted compositionOddMinusEven_huang_eq_sum_monomial (k m n : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1)
        (fun c => (c.blocks.filter fun a => a < k).length = m ∧
          IsHuangSmallPartPlacement k c.blocks)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), ∑ g : Fin m → Fin (k - 1),
          if i + (k + 1) * m + j * k + ∑ t, (g t : ℕ) = n then
            (-1 : ℤ) ^ j * (i.choose m : ℤ) * ((i + j - 1).choose j : ℤ)
          else 0

/-- Theorem 17: for `k, n ≥ 1`, the signed count of compositions of `n + k - 1`
with exactly `m` parts less than `k` is
`∑_{i + j + (k-1)(ℓ + i - m - 1) = n} (-1)^{i+ℓ+1} binom(i+j-1, j) binom(i, m) binom(m, ℓ)`
over `i, j, ℓ ≥ 0`, the constraint read in `ℤ`. The ranges below contain every
solution (`ℓ ≤ m` and `i, j ≤ n + (k-1)(m+1)` whenever the summand is nonzero).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 17
(`jis-2024-24.6.5-thm-17`). -/
public theorem_wanted compositionOddMinusEven_parts_lt_eq_sum (k m n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1) (fun c => (c.blocks.filter fun a => a < k).length = m)
      = ∑ i ∈ Finset.range (n + k * (m + 1) + 1), ∑ j ∈ Finset.range (n + k * (m + 1) + 1),
          ∑ l ∈ Finset.range (m + 1),
            if (i : ℤ) + j + ((k : ℤ) - 1) * ((l : ℤ) + i - m - 1) = n then
              (-1 : ℤ) ^ (i + l + 1) * ((i + j - 1).choose j : ℤ) * (i.choose m : ℤ) *
                (m.choose l : ℤ)
            else 0

end

end MetaMathlibExt
