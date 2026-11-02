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

/-- **Number of D-nodes of the divide-and-conquer tree.** The number $\delta(n)$ of D-nodes in the
divide-and-conquer tree on $n$ leaves (OEIS A296062) is defined by the recurrence the paper
quotes from Coronado et al.: $\delta(1) = 0$, and for every natural number $m \ge 1$,
$\delta(2m) = 2\,\delta(m)$ and $\delta(2m+1) = \delta(m) + \delta(m+1) + 1$. The value at $0$
is the junk value $\delta(0) = 0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public def dcDNodes : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    if h : (n + 2) % 2 = 0 then 2 * dcDNodes ((n + 2) / 2)
    else dcDNodes ((n + 2) / 2) + dcDNodes ((n + 2) / 2 + 1) + 1
decreasing_by all_goals omega

/-- **The divide-and-conquer D-node count at one leaf.** The divide-and-conquer D-node count
$\delta$ satisfies $\delta(1) = 0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_one : dcDNodes 1 = 0 := by
  simp [dcDNodes]

/-- **Doubling recurrence for the divide-and-conquer D-node count.** For every integer $m > 0$,
the divide-and-conquer D-node count $\delta$ satisfies $\delta(2m) = 2\delta(m)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_two_mul {m : ℕ} (hm : 0 < m) : dcDNodes (2 * m) = 2 * dcDNodes m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, dcDNodes]
  simp only [show (2 * j + 2) % 2 = 0 by omega, ↓reduceDIte]
  congr 2
  omega

/-- **Odd-argument recurrence for the divide-and-conquer D-node count.** For every integer
$m > 0$, the divide-and-conquer D-node count $\delta$ satisfies
$\delta(2m+1) = \delta(m) + \delta(m+1) + 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_two_mul_add_one {m : ℕ} (hm : 0 < m) :
    dcDNodes (2 * m + 1) = dcDNodes m + dcDNodes (m + 1) + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, dcDNodes]
  simp only [show ¬(2 * j + 1 + 2) % 2 = 0 by omega, ↓reduceDIte]
  have h : (2 * j + 1 + 2) / 2 = j + 1 := by omega
  rw [h]

/-- **Small values of the divide-and-conquer D-node count.** The divide-and-conquer D-node count
$\delta$ satisfies $\delta(2) = 0$, $\delta(3) = 1$, $\delta(4) = 0$, $\delta(5) = 2$,
$\delta(6) = 2$ and $\delta(7) = 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`). -/
public theorem dcDNodes_small :
    dcDNodes 2 = 0 ∧ dcDNodes 3 = 1 ∧ dcDNodes 4 = 0 ∧ dcDNodes 5 = 2 ∧ dcDNodes 6 = 2 ∧
      dcDNodes 7 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [dcDNodes]

/-- **Level counts of D-nodes.** For natural numbers $n$ and $i$, let $n_i$ be the binary digit
of $n$ at position $i$ (the coefficient of $2^i$ in the binary expansion of $n$). The level count
$\lambda_i(n)$ is $n \bmod 2^i$ if $n_i = 0$, and $2^i - (n \bmod 2^i)$ if $n_i = 1$.

This is the paper's closed form for the number of D-nodes on level $i$ of the
divide-and-conquer tree on $n$ leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public def dcLevelDNodes (n i : ℕ) : ℕ :=
  if n / 2 ^ i % 2 = 0 then n % 2 ^ i else 2 ^ i - n % 2 ^ i

/-- **Level count of D-nodes when the binary digit is zero.** Let $n$ and $i$ be natural numbers
such that the binary digit $n_i$ of $n$ (the coefficient of $2^i$ in the binary expansion of
$n$) equals $0$. Then the level count of D-nodes is $\lambda_i(n) = n \bmod 2^i$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_zero {n i : ℕ} (h : n / 2 ^ i % 2 = 0) :
    dcLevelDNodes n i = n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- **Level count of D-nodes when the binary digit is one.** Let $n$ and $i$ be natural numbers
such that the binary digit $n_i$ of $n$ (the coefficient of $2^i$ in the binary expansion of
$n$) equals $1$. Then the level count of D-nodes is $\lambda_i(n) = 2^i - (n \bmod 2^i)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_one {n i : ℕ} (h : n / 2 ^ i % 2 = 1) :
    dcLevelDNodes n i = 2 ^ i - n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- **Level count of D-nodes on level zero.** For every natural number $n$, the level count of
D-nodes on level $0$ is $\lambda_0(n) = n \bmod 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_zero (n : ℕ) : dcLevelDNodes n 0 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [dcLevelDNodes, h, Nat.mod_one]

/-- **Number of $D$-nodes of a full binary tree.** A $D$-node of a full binary tree is an
interior node whose two subtrees have different numbers of leaves. The number of $D$-nodes of a
full binary tree is the number of its interior nodes that are $D$-nodes.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public def treeDNodes : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => (if l.numLeaves = r.numLeaves then 0 else 1) + treeDNodes l + treeDNodes r

/-- **Number of $S$-nodes of a full binary tree.** An $S$-node of a full binary tree is an
interior node whose two subtrees have the same number of leaves. The number of $S$-nodes of a
full binary tree is the number of its interior nodes that are $S$-nodes.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public def treeSNodes : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => (if l.numLeaves = r.numLeaves then 1 else 0) + treeSNodes l + treeSNodes r

/-- **Divide-and-conquer trees.** A divide-and-conquer tree is a full binary tree in which, at
every interior node, the numbers of leaves of the two subtrees differ by at most $1$. In
particular a single leaf is a divide-and-conquer tree.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (Divide-and-conquer tree). -/
public def IsDivideConquerTree : BinaryTree Unit → Prop
  | .nil => True
  | .node _ l r =>
    (l.numLeaves ≤ r.numLeaves + 1 ∧ r.numLeaves ≤ l.numLeaves + 1) ∧
      IsDivideConquerTree l ∧ IsDivideConquerTree r

/-- **Recursion for the number of $D$-nodes.** Write $D(t)$ for the number of $D$-nodes of a
full binary tree $t$. If the root of $t$ has left subtree $l$ and right subtree $r$, then
$D(t) = \varepsilon + D(l) + D(r)$, where $\varepsilon = 0$ if $l$ and $r$ have the same number
of leaves and $\varepsilon = 1$ otherwise.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public theorem treeDNodes_node (u : Unit) (l r : BinaryTree Unit) :
    treeDNodes (.node u l r) =
      (if l.numLeaves = r.numLeaves then 0 else 1) + treeDNodes l + treeDNodes r := rfl

/-- **Recursion for the number of $S$-nodes.** Write $S(t)$ for the number of $S$-nodes of a
full binary tree $t$. If the root of $t$ has left subtree $l$ and right subtree $r$, then
$S(t) = \varepsilon + S(l) + S(r)$, where $\varepsilon = 1$ if $l$ and $r$ have the same number
of leaves and $\varepsilon = 0$ otherwise.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes). -/
public theorem treeSNodes_node (u : Unit) (l r : BinaryTree Unit) :
    treeSNodes (.node u l r) =
      (if l.numLeaves = r.numLeaves then 1 else 0) + treeSNodes l + treeSNodes r := rfl

/-- **The single-leaf tree.** The full binary tree consisting of a single leaf has no $D$-nodes
and no $S$-nodes, and it is a divide-and-conquer tree.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definitions (`S`-nodes and `D`-nodes;
Divide-and-conquer tree). -/
public theorem treeNodes_nil :
    treeDNodes .nil = 0 ∧ treeSNodes .nil = 0 ∧ IsDivideConquerTree .nil :=
  ⟨rfl, rfl, trivial⟩

/-- **The divide-and-conquer condition at the root.** A full binary tree whose root has left
subtree $L$ and right subtree $R$ is a divide-and-conquer tree if and only if the numbers of
leaves of $L$ and $R$ differ by at most $1$ and both $L$ and $R$ are divide-and-conquer trees.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition (Divide-and-conquer tree). -/
public theorem isDivideConquerTree_node (u : Unit) (l r : BinaryTree Unit) :
    IsDivideConquerTree (.node u l r) ↔
      (l.numLeaves ≤ r.numLeaves + 1 ∧ r.numLeaves ≤ l.numLeaves + 1) ∧
        IsDivideConquerTree l ∧ IsDivideConquerTree r := Iff.rfl

/-- **Normalized form of $n = 2^k + r$.** Let $n$, $k$ and $r$ be natural numbers with $r < 2^k$
and $n = 2^k + r$, and let $x$ be a rational number with $n = 2^k (1 + x)$. Then $x = r / 2^k$
and $1 + x = n / 2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 2 (`jis-2024-24.2.7-lem-2`). -/
public theorem_wanted dyadic_mantissa_eq (n k r : ℕ) (x : ℚ) (hr : r < 2 ^ k)
    (hn : n = 2 ^ k + r) (hx : (n : ℚ) = 2 ^ k * (1 + x)) :
    x = r / 2 ^ k ∧ 1 + x = n / 2 ^ k

/-- **$D$-nodes and $S$-nodes of a full binary tree.** Let $t$ be a full binary tree with $n$
leaves and let $a$ be the number of $S$-nodes of $t$. Then the number of $D$-nodes of $t$ is
$n - 1 - a$ (subtraction of natural numbers, truncated at $0$).

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 5 (`jis-2024-24.2.7-lem-5`). -/
public theorem_wanted treeDNodes_eq_numLeaves_sub_one_sub_treeSNodes (t : BinaryTree Unit) :
    treeDNodes t = t.numLeaves - 1 - treeSNodes t

/-- **The Takagi function at dyadic rationals counts D-nodes (Coronado et al.).** Let $k$ and $r$
be natural numbers with $r \le 2^k$. Write $\tau(r / 2^k)$ for the Takagi value of the dyadic
presentation $r / 2^k$, and $\delta(n)$ for the number of $D$-nodes of the divide-and-conquer
tree on $n$ leaves, given by $\delta(1) = 0$, $\delta(2m) = 2 \delta(m)$ and
$\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$. Then
$\tau(r / 2^k) = \delta(2^k + r) / 2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 8 (`jis-2024-24.2.7-thm-8`). -/
public theorem_wanted takagi_dyadic_eq_dcDNodes_div (k r : ℕ) (hr : r ≤ 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) = (dcDNodes (2 ^ k + r) : ℝ) / 2 ^ k

/-- **Coronado et al.'s count of $D$-nodes in divide-and-conquer trees.** Every
divide-and-conquer tree with $n$ leaves has exactly $\delta(n)$ $D$-nodes, where $\delta$ is the
function on positive integers given by $\delta(1) = 0$, $\delta(2m) = 2\delta(m)$ and
$\delta(2m+1) = \delta(m) + \delta(m+1) + 1$ for $m \ge 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 9 (`jis-2024-24.2.7-thm-9`). -/
public theorem_wanted treeDNodes_eq_dcDNodes_of_isDivideConquerTree (t : BinaryTree Unit)
    (ht : IsDivideConquerTree t) : treeDNodes t = dcDNodes t.numLeaves

/-- **Midpoint identity for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count. Let $k$ and $r$ be natural numbers with $0 < r < 2^k$, put
$n = 2^k + r$, and let $\nu_2(r)$ be the position of the lowest nonzero binary digit of $r$,
counted from $0$ (the exponent of the largest power of $2$ dividing $r$). Then
$\delta(n) = \frac{\delta(n-1) + \delta(n+1)}{2} + 1 - \nu_2(r)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 10 (`jis-2024-24.2.7-cor-10`). -/
public theorem_wanted dcDNodes_eq_midpoint_add_one_sub_lowestBit (k r : ℕ) (hr0 : 0 < r)
    (hr : r < 2 ^ k) :
    (dcDNodes (2 ^ k + r) : ℚ) =
      ((dcDNodes (2 ^ k + r - 1) : ℚ) + dcDNodes (2 ^ k + r + 1)) / 2 + 1 - padicValNat 2 r

/-- **Level-sum formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$,
let $\lambda_i(n)$ be the level-$i$ D-node count, and let $n_i$ be the binary digit of $n$ at
$2^i$. Then
$$\delta(n) = \sum_{i=0}^{k-1} \lambda_i(n),$$
and explicitly
$$\delta(n) = \sum_{i=0}^{k-1} \left(n_i 2^i + (-1)^{n_i} (n \bmod 2^i)\right).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`jis-2024-24.2.7-thm-11`). -/
public theorem_wanted dcDNodes_eq_sum_dcLevelDNodes (n : ℕ) (hn : 0 < n) :
    dcDNodes n = ∑ i ∈ range (Nat.log 2 n), dcLevelDNodes n i ∧
      (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          (((n / 2 ^ i % 2 : ℕ) : ℤ) * 2 ^ i + (-1) ^ (n / 2 ^ i % 2) * ((n % 2 ^ i : ℕ) : ℤ))

/-- **Adding a larger power of two raises the Hamming weight by one.** For a natural number $m$,
write $s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary
expansion). For all natural numbers $k$ and $r$ with $r < 2^k$, $s_1(2^k + r) = s_1(r) + 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 13 (`jis-2024-24.2.7-lem-13`). -/
public theorem_wanted hammingWeight_two_pow_add (k r : ℕ) (hr : r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k + r)).sum = (Nat.digits 2 r).sum + 1

/-- **Hamming weight of the successor of an even number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
If $n$ is an even natural number (including $n = 0$), then $s_1(n + 1) = s_1(n) + 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 14 (`jis-2024-24.2.7-lem-14`). -/
public theorem_wanted hammingWeight_succ_of_even (n : ℕ) (hn : Even n) :
    (Nat.digits 2 (n + 1)).sum = (Nat.digits 2 n).sum + 1

/-- **Hamming weight of the predecessor of an odd number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
If $n$ is an odd natural number, then $s_1(n - 1) = s_1(n) - 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 15 (`jis-2024-24.2.7-lem-15`). -/
public theorem_wanted hammingWeight_pred_of_odd (n : ℕ) (hn : Odd n) :
    (Nat.digits 2 (n - 1)).sum = (Nat.digits 2 n).sum - 1

/-- **Hamming weight of a power of two minus an odd number.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ (the number of ones in its binary expansion).
Let $k$ and $r$ be natural numbers with $r$ odd and $2r < 2^k$, that is, $r < 2^{k-1}$. Then
$s_1(2^k - r) = 1 + k - s_1(r)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 16 (`jis-2024-24.2.7-lem-16`). -/
public theorem_wanted hammingWeight_two_pow_sub_of_odd (k r : ℕ) (hodd : Odd r)
    (hr : 2 * r < 2 ^ k) :
    (Nat.digits 2 (2 ^ k - r)).sum = 1 + k - (Nat.digits 2 r).sum

/-- **Level counts of D-nodes at consecutive integers.** Let $k$, $r$ and $i$ be natural numbers
with $r$ odd, $r < 2^k$ and $0 < i < k$, and let $n = 2^k + r$. Then the level counts of
D-nodes satisfy $\lambda_i(n) - \lambda_i(n-1) = 1$ if the binary digit $n_i$ of $n$ is $0$,
and $\lambda_i(n) - \lambda_i(n-1) = -1$ if $n_i = 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 17 (`jis-2024-24.2.7-lem-17`). -/
public theorem_wanted dcLevelDNodes_sub_pred (k r i : ℕ) (hodd : Odd r) (hr : r < 2 ^ k)
    (hi0 : 0 < i) (hik : i < k) :
    (dcLevelDNodes (2 ^ k + r) i : ℤ) - dcLevelDNodes (2 ^ k + r - 1) i =
      if (2 ^ k + r) / 2 ^ i % 2 = 0 then 1 else -1

/-- **Symmetry of the D-node counts.** For all natural numbers $k$ and $r$ with $r \le 2^k$,
$\delta(2^{k+1} - r) = \delta(2^k + r)$, where $\delta(n)$ denotes the number of D-nodes in the
divide-and-conquer tree on $n$ leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 18 (`jis-2024-24.2.7-lem-18`). -/
public theorem_wanted dcDNodes_two_pow_succ_sub (k r : ℕ) (hr : r ≤ 2 ^ k) :
    dcDNodes (2 ^ (k + 1) - r) = dcDNodes (2 ^ k + r)

/-- **Successor formula for the D-node count at even arguments.** Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every even integer $n > 0$, $\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 19 (`jis-2024-24.2.7-lem-19`). -/
public theorem_wanted dcDNodes_succ_of_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- **Successor formula for the D-node count at odd arguments.** Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every odd natural number $n$,
$\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 20 (`jis-2024-24.2.7-lem-20`). -/
public theorem_wanted dcDNodes_succ_of_odd (n : ℕ) (hodd : Odd n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- **Successor formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every integer $n > 0$,
$\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 21 (`jis-2024-24.2.7-thm-21`). -/
public theorem_wanted dcDNodes_succ (n : ℕ) (hn : 0 < n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2

/-- **Binary-digit formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count and let $s_1(m)$ be the number of ones in the binary expansion
of $m$. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$ and let $n_j$ be the binary
digit of $n$ at $2^j$. Then
$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2 \sum_{j=i}^{k} n_j + 4\Big),$$
and also
$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2\, s_1(\lfloor n / 2^i \rfloor) + 4\Big).$$

The printed inner sum $\sum_{j=i}^k n_i$ is read as $\sum_{j=i}^k n_j$.

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

/-- **Binary digit sum from consecutive D-node counts.** For every natural number $n > 0$, the
sum $s_1(n)$ of the binary digits of $n$ satisfies
$s_1(n) = (\delta(n) - \delta(n+1) + \lfloor \log_2 n \rfloor)/2 + 1$ in $\mathbb{Q}$, where
$\delta(m)$ denotes the number of D-nodes in the divide-and-conquer tree on $m$ leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 23 (`jis-2024-24.2.7-cor-23`). -/
public theorem_wanted hammingWeight_eq_dcDNodes_diff (n : ℕ) (hn : 0 < n) :
    ((Nat.digits 2 n).sum : ℚ) =
      ((dcDNodes n : ℚ) - dcDNodes (n + 1) + Nat.log 2 n) / 2 + 1

/-- **Midpoint recurrence for the Takagi function at dyadic rationals.** Let $k$ and $r$ be
natural numbers with $1 \le r < 2^k$. For a natural number $m$, write $\tau(m / 2^k)$ for the
Takagi value of the dyadic presentation $m / 2^k$, and let $\rho_1$ be the $2$-adic valuation of
$r$, the position (counted from $0$) of the lowest nonzero binary digit of $r$. Then
$\tau(r / 2^k) = (\tau((r - 1) / 2^k) + \tau((r + 1) / 2^k))/2 + (1 - \rho_1)/2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 24 (`jis-2024-24.2.7-thm-24`). -/
public theorem_wanted takagi_dyadic_eq_midpoint_add (k r : ℕ) (hr0 : 1 ≤ r) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
      (takagiNewdef (r - 1) ((k : ℤ) - 1) + takagiNewdef (r + 1) ((k : ℤ) - 1)) / 2 +
        (1 - (padicValNat 2 r : ℝ)) / 2 ^ k

/-- **Takagi values at dyadic rationals from level $D$-node counts.** Let $k$ and $r$ be
natural numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value
of the dyadic presentation $r/2^k$, write $n_i = \lfloor n/2^i \rfloor \bmod 2$ for the binary
digit of $n$ at position $i$, and let $\lambda_i(n)$ be the level-$i$ $D$-node count, which
equals $n \bmod 2^i$ if $n_i = 0$ and $2^i - (n \bmod 2^i)$ if $n_i = 1$. Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} \lambda_i(n)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} (n_i 2^i + (-1)^{n_i} (n \bmod 2^i)).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 25 (`jis-2024-24.2.7-thm-25`). -/
public theorem_wanted takagi_dyadic_eq_sum_dcLevelDNodes (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k, (dcLevelDNodes (2 ^ k + r) i : ℝ)) / 2 ^ k ∧
      takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          (((((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ)) * 2 ^ i +
            (-1) ^ ((2 ^ k + r) / 2 ^ i % 2) * (((2 ^ k + r) % 2 ^ i : ℕ) : ℝ))) / 2 ^ k

/-- **Consecutive Takagi values at dyadic rationals.** Let $k$ and $r$ be natural numbers with
$r < 2^k$ and put $n = 2^k + r$. Write $\tau(m, k-1)$ for the Takagi value of the dyadic
presentation $m/2^k$, and $s_1(n)$ for the number of ones in the binary expansion of $n$. Then
$\tau(r+1, k-1) = \tau(r, k-1) + (k - 2 s_1(n) + 2)/2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 26 (`jis-2024-24.2.7-thm-26`). -/
public theorem_wanted takagi_dyadic_succ (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef (r + 1) ((k : ℤ) - 1) =
      takagiNewdef r ((k : ℤ) - 1) +
        ((k : ℝ) - 2 * (Nat.digits 2 (2 ^ k + r)).sum + 2) / 2 ^ k

/-- **Takagi values at dyadic rationals from binary digits.** Let $k$ and $r$ be natural
numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value of the
dyadic presentation $r/2^k$, write $n_j = \lfloor n/2^j \rfloor \bmod 2$ for the binary digit of
$n$ at position $j$, and write $s_1(m)$ for the number of ones in the binary expansion of $m$.
Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 \sum_{j=i}^{k} n_j + 4)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 s_1(\lfloor n/2^i \rfloor) + 4).$$

The paper prints the inner sum as $\sum_{j=i}^{k} n_i$; it is read here as $\sum_{j=i}^{k} n_j$.

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

/-- **Binary digit sum from consecutive Takagi values.** Let $k$ and $r$ be natural numbers
with $r < 2^k$, let $n = 2^k + r$, and let $s_1(n)$ be the sum of the binary digits of $n$.
Writing $\tau(m, k - 1)$ for the Takagi value of the dyadic presentation $m / 2^k$, one has
$s_1(n) = 2^{k-1} \bigl(\tau(r, k - 1) - \tau(r + 1, k - 1)\bigr) + (k + 2)/2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 28 (`jis-2024-24.2.7-thm-28`). -/
public theorem_wanted hammingWeight_eq_takagi_diff (k r : ℕ) (hr : r < 2 ^ k) :
    ((Nat.digits 2 (2 ^ k + r)).sum : ℝ) =
      2 ^ k / 2 * (takagiNewdef r ((k : ℤ) - 1) - takagiNewdef (r + 1) ((k : ℤ) - 1)) +
        ((k : ℝ) + 2) / 2

/-- **Sum of binary digit sums below a power of two.** For a natural number $i$, let $s_1(i)$
denote the sum of the binary digits of $i$. Then for every natural number $m$,
$2 \sum_{i < 2^m} s_1(i) = 2^m m$; that is, the binary expansions of $0, 1, \dots, 2^m - 1$
contain $2^m m / 2$ ones in total.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 29 (`jis-2024-24.2.7-lem-29`). -/
public theorem_wanted two_mul_sum_hammingWeight_range_two_pow (m : ℕ) :
    2 * ∑ i ∈ range (2 ^ m), (Nat.digits 2 i).sum = 2 ^ m * m

/-- **Trollope's formula via the Takagi function.** For a natural number $m$, write $s_1(m)$ for
the sum of the binary digits of $m$ and $S_1(m) = \sum_{i=0}^{m-1} s_1(i)$. Let $k$ and $r$ be
natural numbers with $r < 2^k$, and put $n = 2^k + r$ and $x = r / 2^k$. Write $\tau(x)$ for
the Takagi value of the dyadic presentation $r / 2^k$. Then

$$S_1(n) = \frac{n \log_2 n}{2} + 2^{k-1} \left(2x - \tau(x) - (1 + x) \log_2 (1 + x)\right).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 30 (`jis-2024-24.2.7-cor-30`). -/
public theorem_wanted sum_hammingWeight_range_eq_trollope (k r : ℕ) (hr : r < 2 ^ k) :
    ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
      ((2 ^ k + r : ℕ) : ℝ) * Real.logb 2 ((2 ^ k + r : ℕ) : ℝ) / 2 +
        2 ^ k / 2 *
          (2 * ((r : ℝ) / 2 ^ k) - takagiNewdef r ((k : ℤ) - 1) -
            (1 + (r : ℝ) / 2 ^ k) * Real.logb 2 (1 + (r : ℝ) / 2 ^ k))

/-- **Cumulative binary digit sums via the Takagi function.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ and $S_1(m) = \sum_{i=0}^{m-1} s_1(i)$. Let
$k$ and $r$ be natural numbers with $r < 2^k$, and put $n = 2^k + r$ and $x = r / 2^k$. Write
$\tau(x)$ for the Takagi value of the dyadic presentation $r / 2^k$, and $\delta(n)$ for the
number of $D$-nodes of the divide-and-conquer tree on $n$ leaves, given by $\delta(1) = 0$,
$\delta(2m) = 2 \delta(m)$ and $\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$.
Then $S_1(n) = (nk + 2^k (2x - \tau(x)))/2$, $S_1(n) = (nk + 2r - 2^k \tau(x))/2$ and
$S_1(n) = (nk + 2r - \delta(n))/2$.

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
