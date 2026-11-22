/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Tree.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction

/-!
# Takagi function identities on dyadic rationals

Statements from Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of
Integer Sequences 27 (2024), Article 24.2.7 (arXiv 2111.05996).

Conventions shared by all declarations below.

* The Takagi function `τ(r / 2^k)` is `takagiNewdef r (k - 1)`, the paper's own Definition
  `takagi_newdef` (already in `MathlibExt`), which evaluates `τ` at `n / 2^(k+1)`.
* Notation `not_n`: a positive integer is `n = 2^k + r` with `0 ≤ r < 2^k`, and `x = r / 2^k`.
* The binary digit `nᵢ` is `n / 2^i % 2`, the Hamming weight `s₁(n)` is
  `(Nat.digits 2 n).sum`, `⌊log₂ n⌋` is `Nat.log 2 n`, and the position `ρ₁` of the
  lowest nonzero bit of `r > 0` is `padicValNat 2 r`.
* `S₁(n) = ∑_{i<n} s₁(i)` is written out as a `Finset.range` sum.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The number `δ(n)` of `D`-nodes in the divide-and-conquer tree on `n` leaves (OEIS
A296062), defined by the recurrence the paper quotes from Coronado et al.:
`δ(1) = 0`, `δ(2m) = 2 δ(m)`, `δ(2m+1) = δ(m) + δ(m+1) + 1`. The value at `0` is a
junk value `0`; no statement below uses it.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public def dcDNodes : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then 2 * dcDNodes ((n + 2) / 2)
    else dcDNodes ((n + 2) / 2) + dcDNodes ((n + 2) / 2 + 1) + 1
decreasing_by all_goals omega

/-- `δ(1) = 0`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_one : dcDNodes 1 = 0 := by
  simp [dcDNodes]

/-- `δ(2m) = 2 δ(m)` for `m > 0`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_two_mul {m : ℕ} (hm : 0 < m) : dcDNodes (2 * m) = 2 * dcDNodes m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, dcDNodes]
  simp only [show (2 * j + 2) % 2 = 0 by omega, ↓reduceDIte]
  congr 2
  omega

/-- `δ(2m+1) = δ(m) + δ(m+1) + 1` for `m > 0`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_two_mul_add_one {m : ℕ} (hm : 0 < m) :
    dcDNodes (2 * m + 1) = dcDNodes m + dcDNodes (m + 1) + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, dcDNodes]
  simp only [show ¬(2 * j + 1 + 2) % 2 = 0 by omega, ↓reduceDIte]
  have h : (2 * j + 1 + 2) / 2 = j + 1 := by omega
  rw [h]

/-- Small values `δ(2), …, δ(7) = 0, 1, 0, 2, 2, 2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_small :
    dcDNodes 2 = 0 ∧ dcDNodes 3 = 1 ∧ dcDNodes 4 = 0 ∧ dcDNodes 5 = 2 ∧ dcDNodes 6 = 2 ∧
      dcDNodes 7 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [dcDNodes]

/-- The number `λᵢ(n)` of `D`-nodes on level `i` of the divide-and-conquer tree on `n`
leaves: `n mod 2^i` if the binary digit `nᵢ` is `0`, and `2^i - (n mod 2^i)` if it is `1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public def dcLevelDNodes (n i : ℕ) : ℕ :=
  if n / 2 ^ i % 2 = 0 then n % 2 ^ i else 2 ^ i - n % 2 ^ i

/-- `λᵢ(n) = n mod 2^i` when `nᵢ = 0`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_zero {n i : ℕ} (h : n / 2 ^ i % 2 = 0) :
    dcLevelDNodes n i = n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- `λᵢ(n) = 2^i - (n mod 2^i)` when `nᵢ = 1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_one {n i : ℕ} (h : n / 2 ^ i % 2 = 1) :
    dcLevelDNodes n i = 2 ^ i - n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- On level `0`, `λ₀(n) = n mod 2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_zero (n : ℕ) : dcLevelDNodes n 0 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [dcLevelDNodes, h, Nat.mod_one]

/-- The number of `D`-nodes of a full binary tree (`BinaryTree Unit`, leaves are `nil`):
interior nodes whose two subtrees have different numbers of leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public def treeDNodes : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => (if l.numLeaves = r.numLeaves then 0 else 1) + treeDNodes l + treeDNodes r

/-- The number of `S`-nodes of a full binary tree: interior nodes whose two subtrees have
the same number of leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public def treeSNodes : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => (if l.numLeaves = r.numLeaves then 1 else 0) + treeSNodes l + treeSNodes r

/-- A divide-and-conquer tree: a full binary tree in which, at every interior node, the leaf
counts of the two subtrees differ by at most `1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (Divide-and-conquer tree). -/
public def IsDivideConquerTree : BinaryTree Unit → Prop
  | .nil => True
  | .node _ l r =>
    (l.numLeaves ≤ r.numLeaves + 1 ∧ r.numLeaves ≤ l.numLeaves + 1) ∧
      IsDivideConquerTree l ∧ IsDivideConquerTree r

/-- Unfolding of `treeDNodes` at an interior node.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public theorem treeDNodes_node (u : Unit) (l r : BinaryTree Unit) :
    treeDNodes (.node u l r) =
      (if l.numLeaves = r.numLeaves then 0 else 1) + treeDNodes l + treeDNodes r := rfl

/-- Unfolding of `treeSNodes` at an interior node.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public theorem treeSNodes_node (u : Unit) (l r : BinaryTree Unit) :
    treeSNodes (.node u l r) =
      (if l.numLeaves = r.numLeaves then 1 else 0) + treeSNodes l + treeSNodes r := rfl

/-- The single-leaf tree has no `D`-nodes and no `S`-nodes and is divide-and-conquer.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definitions (`S`-nodes and `D`-nodes;
Divide-and-conquer tree). -/
public theorem treeNodes_nil :
    treeDNodes .nil = 0 ∧ treeSNodes .nil = 0 ∧ IsDivideConquerTree .nil :=
  ⟨rfl, rfl, trivial⟩

/-- Unfolding of `IsDivideConquerTree` at an interior node.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (Divide-and-conquer tree). -/
public theorem isDivideConquerTree_node (u : Unit) (l r : BinaryTree Unit) :
    IsDivideConquerTree (.node u l r) ↔
      (l.numLeaves ≤ r.numLeaves + 1 ∧ r.numLeaves ≤ l.numLeaves + 1) ∧
        IsDivideConquerTree l ∧ IsDivideConquerTree r := Iff.rfl

/-- Lemma 2: with `n = 2^k + r`, `0 ≤ r < 2^k`, and `n = 2^k (1 + x)`, one has
`x = r / 2^k` and `1 + x = n / 2^k`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 2 (`jis-2024-24.2.7-lem-2`). -/
public theorem_wanted dyadic_mantissa_eq (n k r : ℕ) (x : ℚ) (hr : r < 2 ^ k)
    (hn : n = 2 ^ k + r) (hx : (n : ℚ) = 2 ^ k * (1 + x)) :
    x = r / 2 ^ k ∧ 1 + x = n / 2 ^ k

/-- Lemma 5: in a full binary tree with `n` leaves and `a(n)` `S`-nodes, the number of
`D`-nodes is `n - 1 - a(n)`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 5 (`jis-2024-24.2.7-lem-5`). -/
public theorem_wanted treeDNodes_eq_numLeaves_sub_one_sub_treeSNodes (t : BinaryTree Unit) :
    treeDNodes t = t.numLeaves - 1 - treeSNodes t

/-- Theorem 8 (Coronado et al.): for `0 ≤ r ≤ 2^k`, `τ(r / 2^k) = δ(2^k + r) / 2^k`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 8 (`jis-2024-24.2.7-thm-8`). -/
public theorem_wanted takagi_dyadic_eq_dcDNodes_div (k r : ℕ) (hr : r ≤ 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) = (dcDNodes (2 ^ k + r) : ℝ) / 2 ^ k

/-- Theorem 9 (Coronado et al.), tree form: every divide-and-conquer tree with `n` leaves
has `δ(n)` `D`-nodes, where `δ` is the recurrence `dcDNodes`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`jis-2024-24.2.7-thm-9`). -/
public theorem_wanted treeDNodes_eq_dcDNodes_of_isDivideConquerTree (t : BinaryTree Unit)
    (ht : IsDivideConquerTree t) : treeDNodes t = dcDNodes t.numLeaves

/-- Corollary 10: for `n = 2^k + r` with `0 < r < 2^k` and `ρ₁` the position of the lowest
nonzero bit of `r`, `δ(n) = (δ(n-1) + δ(n+1))/2 + 1 - ρ₁`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 10 (`jis-2024-24.2.7-cor-10`). -/
public theorem_wanted dcDNodes_eq_midpoint_add_one_sub_lowestBit (k r : ℕ) (hr0 : 0 < r)
    (hr : r < 2 ^ k) :
    (dcDNodes (2 ^ k + r) : ℚ) =
      ((dcDNodes (2 ^ k + r - 1) : ℚ) + dcDNodes (2 ^ k + r + 1)) / 2 + 1 - padicValNat 2 r

/-- Theorem 11: for `n > 0`, `δ(n) = ∑_{i=0}^{⌊log₂ n⌋-1} λᵢ(n)`, and explicitly
`δ(n) = ∑_{i=0}^{⌊log₂ n⌋-1} (nᵢ 2^i + (-1)^{nᵢ} (n mod 2^i))`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`jis-2024-24.2.7-thm-11`). -/
public theorem_wanted dcDNodes_eq_sum_dcLevelDNodes (n : ℕ) (hn : 0 < n) :
    dcDNodes n = ∑ i ∈ range (Nat.log 2 n), dcLevelDNodes n i ∧
      (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          (((n / 2 ^ i % 2 : ℕ) : ℤ) * 2 ^ i + (-1) ^ (n / 2 ^ i % 2) * ((n % 2 ^ i : ℕ) : ℤ))

/-- Lemma 13: for `n = 2^k + r` with `0 ≤ r < 2^k`, `s₁(n) = s₁(r) + 1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 13 (`jis-2024-24.2.7-lem-13`). -/
public theorem_wanted hammingWeight_two_pow_add (k r : ℕ) (hr : r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k + r)).sum = (Nat.digits 2 r).sum + 1

/-- Lemma 14: if `n` is even, then `s₁(n+1) = s₁(n) + 1` (also at `n = 0`).

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 14 (`jis-2024-24.2.7-lem-14`). -/
public theorem_wanted hammingWeight_succ_of_even (n : ℕ) (hn : Even n) :
    (Nat.digits 2 (n + 1)).sum = (Nat.digits 2 n).sum + 1

/-- Lemma 15: if `n` is odd, then `s₁(n-1) = s₁(n) - 1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 15 (`jis-2024-24.2.7-lem-15`). -/
public theorem_wanted hammingWeight_pred_of_odd (n : ℕ) (hn : Odd n) :
    (Nat.digits 2 (n - 1)).sum = (Nat.digits 2 n).sum - 1

/-- Lemma 16: if `r` is odd and `r < 2^(k-1)` (written `2r < 2^k`), then
`s₁(2^k - r) = 1 + k - s₁(r)`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 16 (`jis-2024-24.2.7-lem-16`). -/
public theorem_wanted hammingWeight_two_pow_sub_of_odd (k r : ℕ) (hodd : Odd r)
    (hr : 2 * r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k - r)).sum = 1 + k - (Nat.digits 2 r).sum

/-- Lemma 17: for `n = 2^k + r` with `r` odd, `0 < r < 2^k`, and `0 < i < k`,
`λᵢ(n) - λᵢ(n-1)` is `1` if `nᵢ = 0` and `-1` if `nᵢ = 1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 17 (`jis-2024-24.2.7-lem-17`). -/
public theorem_wanted dcLevelDNodes_sub_pred (k r i : ℕ) (hodd : Odd r) (hr : r < 2 ^ k)
    (hi0 : 0 < i) (hik : i < k) :
    (dcLevelDNodes (2 ^ k + r) i : ℤ) - dcLevelDNodes (2 ^ k + r - 1) i =
      if (2 ^ k + r) / 2 ^ i % 2 = 0 then 1 else -1

/-- Lemma 18: for `0 ≤ r ≤ 2^k`, `δ(2^(k+1) - r) = δ(2^k + r)`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 18 (`jis-2024-24.2.7-lem-18`). -/
public theorem_wanted dcDNodes_two_pow_succ_sub (k r : ℕ) (hr : r ≤ 2 ^ k) :
    dcDNodes (2 ^ (k + 1) - r) = dcDNodes (2 ^ k + r)

/-- Lemma 19: for even `n > 0`, `δ(n+1) = δ(n) + ⌊log₂ n⌋ - 2 s₁(n) + 2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 19 (`jis-2024-24.2.7-lem-19`). -/
public theorem_wanted dcDNodes_succ_of_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- Lemma 20: for odd `n`, `δ(n+1) = δ(n) + ⌊log₂ n⌋ - 2 s₁(n) + 2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 20 (`jis-2024-24.2.7-lem-20`). -/
public theorem_wanted dcDNodes_succ_of_odd (n : ℕ) (hodd : Odd n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- Theorem 21: for every `n > 0`, `δ(n+1) = δ(n) + ⌊log₂ n⌋ - 2 s₁(n) + 2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 21 (`jis-2024-24.2.7-thm-21`). -/
public theorem_wanted dcDNodes_succ (n : ℕ) (hn : 0 < n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- Theorem 22: for `n > 0` with `k = ⌊log₂ n⌋`,
`δ(n) = ∑_{i=0}^{k-1} 2^i nᵢ (k - i - 2 ∑_{j=i}^{k} nⱼ + 4)`, and equivalently with
`∑_{j=i}^{k} nⱼ` replaced by `s₁(⌊n / 2^i⌋)`. The printed inner sum `∑_{j=i}^k n_i` is read
as `∑_{j=i}^k n_j`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 22 (`jis-2024-24.2.7-thm-22`). -/
public theorem_wanted dcDNodes_eq_sum_digit_weight (n : ℕ) (hn : 0 < n) :
    (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          2 ^ i * ((n / 2 ^ i % 2 : ℕ) : ℤ) *
            ((Nat.log 2 n : ℤ) - i - 2 * ∑ j ∈ Icc i (Nat.log 2 n), ((n / 2 ^ j % 2 : ℕ) : ℤ) + 4) ∧
      (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          2 ^ i * ((n / 2 ^ i % 2 : ℕ) : ℤ) *
            ((Nat.log 2 n : ℤ) - i - 2 * (Nat.digits 2 (n / 2 ^ i)).sum + 4)

/-- Corollary 23: for `n > 0`, `s₁(n) = (δ(n) - δ(n+1) + ⌊log₂ n⌋)/2 + 1`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 23 (`jis-2024-24.2.7-cor-23`). -/
public theorem_wanted hammingWeight_eq_dcDNodes_diff (n : ℕ) (hn : 0 < n) :
    ((Nat.digits 2 n).sum : ℚ) =
      ((dcDNodes n : ℚ) - dcDNodes (n + 1) + Nat.log 2 n) / 2 + 1

/-- Theorem 24: for `1 ≤ r ≤ 2^k - 1` and `ρ₁` the position of the lowest nonzero bit of
`r`, `τ(r/2^k) = (τ((r-1)/2^k) + τ((r+1)/2^k))/2 + (1 - ρ₁)/2^k`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 24 (`jis-2024-24.2.7-thm-24`). -/
public theorem_wanted takagi_dyadic_eq_midpoint_add (k r : ℕ) (hr0 : 1 ≤ r) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
      (takagiNewdef (r - 1) ((k : ℤ) - 1) + takagiNewdef (r + 1) ((k : ℤ) - 1)) / 2 +
        (1 - (padicValNat 2 r : ℝ)) / 2 ^ k

/-- Theorem 25: for `n = 2^k + r` with `0 ≤ r < 2^k`,
`τ(r/2^k) = 2^(-k) ∑_{i=0}^{k-1} λᵢ(n)`, and explicitly
`τ(r/2^k) = 2^(-k) ∑_{i=0}^{k-1} (nᵢ 2^i + (-1)^{nᵢ} (n mod 2^i))`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 25 (`jis-2024-24.2.7-thm-25`). -/
public theorem_wanted takagi_dyadic_eq_sum_dcLevelDNodes (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k, (dcLevelDNodes (2 ^ k + r) i : ℝ)) / 2 ^ k ∧
      takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          (((((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ)) * 2 ^ i +
            (-1) ^ ((2 ^ k + r) / 2 ^ i % 2) * (((2 ^ k + r) % 2 ^ i : ℕ) : ℝ))) / 2 ^ k

/-- Theorem 26: for `n = 2^k + r` with `0 ≤ r < 2^k`,
`τ((r+1)/2^k) = τ(r/2^k) + (k - 2 s₁(n) + 2)/2^k`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 26 (`jis-2024-24.2.7-thm-26`). -/
public theorem_wanted takagi_dyadic_succ (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef (r + 1) ((k : ℤ) - 1) =
      takagiNewdef r ((k : ℤ) - 1) +
        ((k : ℝ) - 2 * (Nat.digits 2 (2 ^ k + r)).sum + 2) / 2 ^ k

/-- Theorem 27: for `n = 2^k + r` with `0 ≤ r < 2^k`,
`τ(r/2^k) = 2^(-k) ∑_{i=0}^{k-1} 2^i nᵢ (k - i - 2 ∑_{j=i}^{k} nⱼ + 4)`, and equivalently
with `∑_{j=i}^{k} nⱼ` replaced by `s₁(⌊n / 2^i⌋)`. The printed inner sum `∑_{j=i}^k n_i` is
read as `∑_{j=i}^k n_j`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 27 (`jis-2024-24.2.7-thm-27`). -/
public theorem_wanted takagi_dyadic_eq_sum_digit_weight (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          2 ^ i * (((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ) *
            ((k : ℝ) - i - 2 * ∑ j ∈ Icc i k, (((2 ^ k + r) / 2 ^ j % 2 : ℕ) : ℝ) + 4)) /
          2 ^ k ∧
      takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          2 ^ i * (((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ) *
            ((k : ℝ) - i - 2 * (Nat.digits 2 ((2 ^ k + r) / 2 ^ i)).sum + 4)) / 2 ^ k

/-- Theorem 28: for `n = 2^k + r` with `0 ≤ r < 2^k`,
`s₁(n) = 2^(k-1) (τ(r/2^k) - τ((r+1)/2^k)) + (k+2)/2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 28 (`jis-2024-24.2.7-thm-28`). -/
public theorem_wanted hammingWeight_eq_takagi_diff (k r : ℕ) (hr : r < 2 ^ k) :
    ((Nat.digits 2 (2 ^ k + r)).sum : ℝ) =
      2 ^ k / 2 * (takagiNewdef r ((k : ℤ) - 1) - takagiNewdef (r + 1) ((k : ℤ) - 1)) +
        ((k : ℝ) + 2) / 2

/-- Lemma 29: `S₁(2^m) = ∑_{i<2^m} s₁(i) = 2^m · m / 2` (stated as `2 S₁(2^m) = 2^m m`).

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 29 (`jis-2024-24.2.7-lem-29`). -/
public theorem_wanted two_mul_sum_hammingWeight_range_two_pow (m : ℕ) :
    2 * ∑ i ∈ range (2 ^ m), (Nat.digits 2 i).sum = 2 ^ m * m

/-- Corollary 30 (Trollope): for `n = 2^k + r` with `0 ≤ r < 2^k` and `x = r/2^k`,
`S₁(n) = n log₂ n / 2 + 2^(k-1) (2x - τ(x) - (1+x) log₂(1+x))`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 30 (`jis-2024-24.2.7-cor-30`). -/
public theorem_wanted sum_hammingWeight_range_eq_trollope (k r : ℕ) (hr : r < 2 ^ k) :
    ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
      ((2 ^ k + r : ℕ) : ℝ) * Real.logb 2 ((2 ^ k + r : ℕ) : ℝ) / 2 +
        2 ^ k / 2 *
          (2 * ((r : ℝ) / 2 ^ k) - takagiNewdef r ((k : ℤ) - 1) -
            (1 + (r : ℝ) / 2 ^ k) * Real.logb 2 (1 + (r : ℝ) / 2 ^ k))

/-- Corollary 31: for `n = 2^k + r` with `0 ≤ r < 2^k` and `x = r/2^k`,
(1) `S₁(n) = (n k + 2^k (2x - τ(x)))/2`, (2) `S₁(n) = (n k + 2r - 2^k τ(r/2^k))/2`, and
(3) `S₁(n) = (n k + 2r - δ(n))/2`.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 31 (`jis-2024-24.2.7-cor-31`). -/
public theorem_wanted sum_hammingWeight_range_eq_takagi_dcDNodes (k r : ℕ) (hr : r < 2 ^ k) :
    ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k +
          2 ^ k * (2 * ((r : ℝ) / 2 ^ k) - takagiNewdef r ((k : ℤ) - 1))) / 2 ∧
      ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k + 2 * r - 2 ^ k * takagiNewdef r ((k : ℤ) - 1)) / 2 ∧
      ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k + 2 * r - dcDNodes (2 ^ k + r)) / 2

end

end MetaMathlibExt
