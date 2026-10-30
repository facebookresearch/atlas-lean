/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear recurrences from counting Schreier-type multisets

Statements from Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and
Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26
(2026), Article A53.

The paper's `ℕ` is the positive integers. For positive `s, p, n`:

* `A^{(s)}_{p,n}` is the set of multisets `F` drawn from `{1^s, …, (n - 1)^s, n}` (each of
  `1, …, n - 1` with multiplicity at most `s`, and `n` at most once) with `n ∈ F` and
  `min F ≥ p|F|` (`schreierMultisetCount`);
* `B^{(s)}_{p,n}` is the colored version: the `s` copies of each `k < n` carry distinct colors
  `0, …, s - 1`, encoded as pairs `(k, c)`, and `n` is the single pair `(n, 0)`
  (`coloredSchreierMultisetCount`);
* `D_{u,n}` is the set of Schreier sets `F ⊆ G_{u,n}` containing `⌊(un - 1)/(u - 1)⌋`, where
  `G_{u,n}` is the set of the first `n` positive integers not divisible by `u`
  (`schreierAvoidingMultiplesCount`), with `IsSchreier` from
  `WantedExt/Combinatorics/Enumerative/SchreierTypeSetsWanted.lean`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import WantedExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

@[expose] public section

/-- The multiset `{1^s, …, (n - 1)^s, n}`: each of `1, …, n - 1` with multiplicity `s`, and `n`
once.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `A^{(s)}_{p,n}`). -/
def schreierMultisetPool (s n : ℕ) : Multiset ℕ :=
  (∑ k ∈ Finset.Icc 1 (n - 1), Multiset.replicate s k) + {n}

/-- `|A^{(s)}_{p,n}|`: the number of sub-multisets `F` of `{1^s, …, (n - 1)^s, n}` with `n ∈ F`
and `min F ≥ p|F|`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `A^{(s)}_{p,n}`). -/
def schreierMultisetCount (s p n : ℕ) : ℕ :=
  ((schreierMultisetPool s n).powerset.toFinset.filter fun F =>
    n ∈ F ∧ ∀ x ∈ F, p * Multiset.card F ≤ x).card

/-- `|A^{(2)}_{1,4}| = 4` and `|A^{(2)}_{2,5}| = 2` (Table 1 of the paper).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 1. -/
theorem schreierMultisetCount_small :
    schreierMultisetCount 2 1 4 = 4 ∧ schreierMultisetCount 2 2 5 = 2 := by
  decide +kernel

/-- `|B^{(s)}_{p,n}|`: the number of sets `F` of colored integers drawn from
`{1₀, …, 1_{s-1}, …, (n - 1)₀, …, (n - 1)_{s-1}, n}` with `n ∈ F` and `min F ≥ p|F|`; the colored
integer `k_c` is the pair `(k, c)` and `n` is `(n, 0)`, and the minimum is over values `k`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `B^{(s)}_{p,n}`). -/
def coloredSchreierMultisetCount (s p n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1) ×ˢ Finset.range s ∪ {(n, 0)}).powerset.filter fun F =>
    (n, 0) ∈ F ∧ ∀ x ∈ F, p * F.card ≤ x.1).card

/-- `|B^{(2)}_{1,4}| = 6` and `|B^{(2)}_{2,5}| = 3` (Table 2 of the paper).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 2. -/
theorem coloredSchreierMultisetCount_small :
    coloredSchreierMultisetCount 2 1 4 = 6 ∧ coloredSchreierMultisetCount 2 2 5 = 3 := by
  decide

/-- `G_{u,n}`: the first `n` positive integers not divisible by `u`, i.e. the positive `k` with
`u ∤ k` such that at most `n` integers in `[1, k]` are not divisible by `u` (all lie in
`[1, un]`).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `G_{u,n}`). -/
def firstNonMultiples (u n : ℕ) : Finset ℕ :=
  (Finset.range (u * n + 1)).filter fun k =>
    0 < k ∧ ¬ u ∣ k ∧ ((Finset.Icc 1 k).filter fun j => ¬ u ∣ j).card ≤ n

/-- `G_{3,4} = {1, 2, 4, 5}`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1. -/
theorem firstNonMultiples_three_four : firstNonMultiples 3 4 = {1, 2, 4, 5} := by
  decide

/-- `|D_{u,n}|`: the number of Schreier sets `F ⊆ G_{u,n}` with `⌊(un - 1)/(u - 1)⌋ ∈ F`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `D_{u,n}`). -/
def schreierAvoidingMultiplesCount (u n : ℕ) : ℕ :=
  ((firstNonMultiples u n).powerset.filter fun F =>
    (u * n - 1) / (u - 1) ∈ F ∧ IsSchreier F).card

/-- `|D_{2,6}| = 12` and `|D_{3,6}| = 9` (Table 3 of the paper).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 3. -/
theorem schreierAvoidingMultiplesCount_small :
    schreierAvoidingMultiplesCount 2 6 = 12 ∧ schreierAvoidingMultiplesCount 3 6 = 9 := by
  decide

/-- The parent sequence `b^{(s)}_{p,n}`: `0` for `n ≤ (p - 1)s`, `1` for
`(p - 1)s < n ≤ ps + 1`, and `b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}` for
`n ≥ ps + 2` (the paper indexes from `n = 1`; here `b^{(s)}_{p,0} = 0`).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3 (definition of `b^{(s)}_{p,n}`). -/
def schreierParentB (s p : ℕ) (n : ℕ) : ℕ :=
  if n ≤ (p - 1) * s then 0
  else if _h : n ≤ p * s + 1 then 1
  else schreierParentB s p (n - 1) + schreierParentB s p (n - 1 - p * s)
decreasing_by all_goals omega

/-- `b^{(s)}_{p,n} = 0` for `n ≤ (p - 1)s`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_of_le {s p n : ℕ} (hn : n ≤ (p - 1) * s) : schreierParentB s p n = 0 := by
  rw [schreierParentB]
  simp [hn]

/-- `b^{(s)}_{p,n} = 1` for `(p - 1)s < n ≤ ps + 1`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_of_mem {s p n : ℕ} (h₁ : (p - 1) * s < n) (h₂ : n ≤ p * s + 1) :
    schreierParentB s p n = 1 := by
  rw [schreierParentB]
  split_ifs <;> first | rfl | omega

/-- `b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}` for `n ≥ ps + 2`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_rec {s p n : ℕ} (hn : p * s + 2 ≤ n) :
    schreierParentB s p n = schreierParentB s p (n - 1) + schreierParentB s p (n - 1 - p * s) := by
  have : (p - 1) * s ≤ p * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [schreierParentB]
  split_ifs <;> first | rfl | omega

/-- The parent sequence `d_{u,n}`: `1` for `n ≤ 2u - 1`, and `d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}`
for `n ≥ 2u` (the paper takes `u ≥ 2` and indexes from `n = 1`; here `d_{u,0} = 1`, and the
degenerate `u = 0` is set to `1`).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4 (definition of `d_{u,n}`). -/
def schreierParentD (u : ℕ) (n : ℕ) : ℕ :=
  if _h : n < 2 * u ∨ u = 0 then 1
  else schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1)
decreasing_by all_goals omega

/-- `d_{u,n} = 1` for `n < 2u`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4. -/
theorem schreierParentD_of_lt {u n : ℕ} (hn : n < 2 * u) : schreierParentD u n = 1 := by
  rw [schreierParentD]
  split_ifs <;> first | rfl | omega

/-- `d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}` for `u ≥ 1` and `n ≥ 2u`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4. -/
theorem schreierParentD_rec {u n : ℕ} (hu : 1 ≤ u) (hn : 2 * u ≤ n) :
    schreierParentD u n = schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1) := by
  rw [schreierParentD]
  split_ifs <;> first | rfl | omega

/-- Theorem 1: for positive `s, p`, `|A^{(s)}_{p,n}| = ∑_{k=1}^{⌊(sn+1)/(sp+1)⌋}
binom(n - pk + k - 2, k - 1)` for `1 ≤ n ≤ sp + 1`, and
`|A^{(s)}_{p,n}| = ∑_{i=0}^s |A^{(s)}_{p,n-1-ip}|` for `n ≥ sp + 2`. In the sum `n ≥ pk`, and the
natural-number top `n - pk + k - 2` truncates to `0` only at `k = 1`, `n = p`, where the paper's
`binom(-1, 0) = 1` agrees.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 1 (`integers-2026-A53-thm-1`). -/
public theorem_wanted schreierMultisetCount_formula_and_recurrence {s p : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) :
    (∀ n, 1 ≤ n → n ≤ s * p + 1 →
      schreierMultisetCount s p n =
        ∑ k ∈ Finset.Icc 1 ((s * n + 1) / (s * p + 1)), (n - p * k + k - 2).choose (k - 1)) ∧
    ∀ n, s * p + 2 ≤ n →
      schreierMultisetCount s p n = ∑ i ∈ Finset.range (s + 1), schreierMultisetCount s p (n - 1 - i * p)

/-- Theorem 2: for positive `s, p`, `|B^{(s)}_{p,n}| = ∑_{k=1}^{⌊(ns+1)/(ps+1)⌋}
binom((n - kp)s, k - 1)` for `1 ≤ n ≤ sp + 1`, and
`|B^{(s)}_{p,n}| = ∑_{i=0}^s binom(s, i) |B^{(s)}_{p,n-1-ip}|` for `n ≥ sp + 2`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 2 (`integers-2026-A53-thm-2`). -/
public theorem_wanted coloredSchreierMultisetCount_formula_and_recurrence {s p : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) :
    (∀ n, 1 ≤ n → n ≤ s * p + 1 →
      coloredSchreierMultisetCount s p n =
        ∑ k ∈ Finset.Icc 1 ((n * s + 1) / (p * s + 1)), ((n - k * p) * s).choose (k - 1)) ∧
    ∀ n, s * p + 2 ≤ n →
      coloredSchreierMultisetCount s p n =
        ∑ i ∈ Finset.range (s + 1), s.choose i * coloredSchreierMultisetCount s p (n - 1 - i * p)

/-- Proposition 1: for positive `s, p, n`,
`b^{(s)}_{p,n} = ∑_{i=0}^{⌊(n - s(p-1) - 1)/(sp + 1)⌋} binom(n - s(p - 1) - 1 - spi, i)`. The range
`0 ≤ i ≤ ⌊(n - s(p-1) - 1)/(sp + 1)⌋` (empty when `n ≤ s(p - 1)`) is encoded as
`(sp + 1)i + s(p - 1) + 1 ≤ n`, on which the natural-number subtraction does not truncate.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 1 (`integers-2026-A53-prop-1`). -/
public theorem_wanted schreierParentB_eq_sum_choose {s p n : ℕ} (hs : 1 ≤ s) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    schreierParentB s p n =
      ∑ i ∈ (Finset.range n).filter (fun i => (s * p + 1) * i + s * (p - 1) + 1 ≤ n),
        (n - s * (p - 1) - 1 - s * p * i).choose i

/-- Lemma 1: `(|B^{(s)}_{p,n}|)` is a periodic subsequence of `(b^{(s)}_{p,n})`:
`|B^{(s)}_{p,n}| = b^{(s)}_{p,ns-s+1}` for positive `s, p, n`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Lemma 1 (`integers-2026-A53-lem-1`). -/
public theorem_wanted coloredSchreierMultisetCount_eq_schreierParentB {s p n : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    coloredSchreierMultisetCount s p n = schreierParentB s p (n * s - s + 1)

/-- Lemma 2: for `u ≥ 2`, `{⌊(un - 1)/(u - 1)⌋ : n ≥ 1}` is the set of positive integers not
divisible by `u`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Lemma 2 (`integers-2026-A53-lem-2`). -/
public theorem_wanted image_floor_eq_nonMultiples {u : ℕ} (hu : 2 ≤ u) :
    (fun n => (u * n - 1) / (u - 1)) '' {n | 1 ≤ n} = {m | 1 ≤ m ∧ ¬ u ∣ m}

/-- Proposition 2: for `u ≥ 2` and `n ≥ 1`,
`d_{u,n} = ∑_{i=0}^{⌊(n-1)/u⌋} binom(⌊(n + (u - 1)i - u)/(2u - 1)⌋, i)`. The natural-number
subtraction truncates only at `i = 0`, `n < u`, where both the paper's `binom(-1, 0)` and
`binom(0, 0)` equal `1`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 2 (`integers-2026-A53-prop-2`). -/
public theorem_wanted schreierParentD_eq_sum_choose {u n : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n) :
    schreierParentD u n =
      ∑ i ∈ Finset.range ((n - 1) / u + 1), ((n + (u - 1) * i - u) / (2 * u - 1)).choose i

/-- Proposition 3: for `u ≥ 2`, `(|D_{u,n}|)` is a periodic subsequence of `(d_{u,n})`:
`|D_{u,n}| = d_{u,un-(u-1)}` for all `n ≥ 1`.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 3 (`integers-2026-A53-prop-3`). -/
public theorem_wanted schreierAvoidingMultiplesCount_eq_schreierParentD {u n : ℕ} (hu : 2 ≤ u)
    (hn : 1 ≤ n) :
    schreierAvoidingMultiplesCount u n = schreierParentD u (u * n - (u - 1))

/-- Theorem 3: for `u ≥ 2`, `|D_{u,n}| = F_n` for `1 ≤ n ≤ 2u - 1`, and
`|D_{u,n}| = ∑_{i=1}^u (-1)^{i-1} binom(u, i) |D_{u,n-i}| + |D_{u,n-2u+1}|` for `n ≥ 2u`
(stated in `ℤ`).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 3 (`integers-2026-A53-thm-3`). -/
public theorem_wanted schreierAvoidingMultiplesCount_fib_and_recurrence {u : ℕ} (hu : 2 ≤ u) :
    (∀ n, 1 ≤ n → n ≤ 2 * u - 1 → schreierAvoidingMultiplesCount u n = Nat.fib n) ∧
    ∀ n, 2 * u ≤ n →
      (schreierAvoidingMultiplesCount u n : ℤ) =
        ∑ i ∈ Finset.Icc 1 u,
            (-1 : ℤ) ^ (i - 1) * u.choose i * schreierAvoidingMultiplesCount u (n - i) +
          schreierAvoidingMultiplesCount u (n - 2 * u + 1)

end

end MetaMathlibExt
