/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Tree.Basic

/-!
# Dyadic normalization, D-node counts and binary digit sums

For `n = 2 ^ k + r` with `r < 2 ^ k`, the dyadic mantissa is the rational number `r / 2 ^ k`.
The even and odd recurrences for D-node counts determine the Hamming weight of a positive
integer from the counts at that integer and its successor.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Normalized form of $n = 2^k + r$.** Let $n$, $k$ and $r$ be natural numbers with $r < 2^k$
and $n = 2^k + r$, and let $x$ be a rational number with $n = 2^k (1 + x)$. Then $x = r / 2^k$
and $1 + x = n / 2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 2 (`jis-2024-24.2.7-lem-2`). -/
public theorem dyadic_mantissa_eq (n k r : ℕ) (x : ℚ) (hr : r < 2 ^ k)
    (hn : n = 2 ^ k + r) (hx : (n : ℚ) = 2 ^ k * (1 + x)) :
    x = r / 2 ^ k ∧ 1 + x = n / 2 ^ k := by
  have hpow : (2 : ℚ) ^ k ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hr).ne'
  have hn' : (n : ℚ) = 2 ^ k + r := by exact_mod_cast hn
  rw [mul_comm] at hx
  refine ⟨(eq_div_iff hpow).2 ?_, (eq_div_iff hpow).2 hx.symm⟩
  rw [hn', add_mul, one_mul] at hx
  exact (add_left_cancel hx).symm

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

/-- **Midpoint identity for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count. Let $k$ and $r$ be natural numbers with $0 < r < 2^k$, put
$n = 2^k + r$, and let $\nu_2(r)$ be the position of the lowest nonzero binary digit of $r$,
counted from $0$ (the exponent of the largest power of $2$ dividing $r$). Then
$\delta(n) = \frac{\delta(n-1) + \delta(n+1)}{2} + 1 - \nu_2(r)$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 10 (`jis-2024-24.2.7-cor-10`). -/
public theorem dcDNodes_eq_midpoint_add_one_sub_lowestBit (k r : ℕ) (hr0 : 0 < r)
    (hr : r < 2 ^ k) :
    (dcDNodes (2 ^ k + r) : ℚ) =
      ((dcDNodes (2 ^ k + r - 1) : ℚ) + dcDNodes (2 ^ k + r + 1)) / 2 + 1 - padicValNat 2 r := by
  induction k generalizing r with
  | zero => simp only [pow_zero] at hr; omega
  | succ k ih =>
    rw [pow_succ] at hr ⊢
    have hpow : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
    rcases Nat.mod_two_eq_zero_or_one r with heven | hodd
    · obtain ⟨d, rfl⟩ : ∃ d, r = 2 * d := ⟨r / 2, by omega⟩
      have hd0 : 0 < d := by omega
      have hmid := ih d hd0 (by omega)
      set m := 2 ^ k + d with hm
      have hm1 : 0 < m - 1 := by omega
      have hm0 : 0 < m := by omega
      have hval : padicValNat 2 (2 * d) = padicValNat 2 d + 1 := by
        simpa only [Nat.padicValNat_def] using
          (multiplicity_base_mul (p := 2) (by decide) hd0.ne')
      rw [show 2 ^ k * 2 + 2 * d = 2 * m by omega,
        show 2 * m - 1 = 2 * (m - 1) + 1 by omega, dcDNodes_two_mul hm0,
        dcDNodes_two_mul_add_one hm1, dcDNodes_two_mul_add_one hm0,
        show m - 1 + 1 = m by omega, hval]
      push_cast
      linarith only [hmid]
    · obtain ⟨d, rfl⟩ : ∃ d, r = 2 * d + 1 := ⟨r / 2, by omega⟩
      set m := 2 ^ k + d with hm
      have hm0 : 0 < m := by omega
      have hval : padicValNat 2 (2 * d + 1) = 0 := by
        rw [Nat.padicValNat_def]
        apply multiplicity_eq_zero_of_not_dvd
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      rw [show 2 ^ k * 2 + (2 * d + 1) = 2 * m + 1 by omega,
        show 2 * m + 1 - 1 = 2 * m by omega,
        show 2 * m + 1 + 1 = 2 * (m + 1) by omega, dcDNodes_two_mul_add_one hm0,
        dcDNodes_two_mul hm0, dcDNodes_two_mul (Nat.succ_pos m), hval]
      push_cast
      ring

/-- **Level counts of D-nodes.** For natural numbers $n$ and $i$, let $n_i$ be the binary digit
of $n$ at position $i$ (the coefficient of $2^i$ in the binary expansion of $n$). The value
$\lambda_i(n)$ is $n \bmod 2^i$ if $n_i = 0$, and $2^i - (n \bmod 2^i)$ if $n_i = 1$.

For $n > 0$ and $i < \lfloor \log_2 n \rfloor$, this formula counts the D-nodes on level $i$ of
the divide-and-conquer tree on $n$ leaves. Outside this range the same formula applies and can
give a nonzero value even when the level has no D-nodes.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public def dcLevelDNodes (n i : ℕ) : ℕ :=
  if n / 2 ^ i % 2 = 0 then n % 2 ^ i else 2 ^ i - n % 2 ^ i

/-- **Level count of D-nodes when the binary digit is zero.** Let $n$ and $i$ be natural numbers
such that the binary digit $n_i$ of $n$ (the coefficient of $2^i$ in the binary expansion of
$n$) equals $0$. Then $\lambda_i(n) = n \bmod 2^i$. For $n > 0$ and
$i < \lfloor \log_2 n \rfloor$, this is the number of D-nodes on level $i$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_zero {n i : ℕ} (h : n / 2 ^ i % 2 = 0) :
    dcLevelDNodes n i = n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- **Level count of D-nodes when the binary digit is one.** Let $n$ and $i$ be natural numbers
such that the binary digit $n_i$ of $n$ (the coefficient of $2^i$ in the binary expansion of
$n$) equals $1$. Then $\lambda_i(n) = 2^i - (n \bmod 2^i)$. For $n > 0$ and
$i < \lfloor \log_2 n \rfloor$, this is the number of D-nodes on level $i$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`). -/
public theorem dcLevelDNodes_of_digit_eq_one {n i : ℕ} (h : n / 2 ^ i % 2 = 1) :
    dcLevelDNodes n i = 2 ^ i - n % 2 ^ i := by
  simp [dcLevelDNodes, h]

/-- **Level count of D-nodes on level zero.** For every natural number $n$,
$\lambda_0(n) = n \bmod 2$. For $n \ge 2$, this counts the D-nodes at the root.

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

/-- **Binary digit sum from consecutive D-node counts.** For every natural number $n > 0$, the
sum $s_1(n)$ of the binary digits of $n$ satisfies
$s_1(n) = (\delta(n) - \delta(n+1) + \lfloor \log_2 n \rfloor)/2 + 1$ in $\mathbb{Q}$, where
$\delta(m)$ denotes the number of D-nodes in the divide-and-conquer tree on $m$ leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 23 (`jis-2024-24.2.7-cor-23`). -/
public theorem hammingWeight_eq_dcDNodes_diff (n : ℕ) (hn : 0 < n) :
    ((Nat.digits 2 n).sum : ℚ) =
      ((dcDNodes n : ℚ) - dcDNodes (n + 1) + Nat.log 2 n) / 2 + 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain rfl | hn₂ : n = 1 ∨ 2 ≤ n := by omega
    · norm_num [dcDNodes]
    set m := n / 2 with hm
    have hm_pos : 0 < m := by omega
    have hhalf := ih m (by omega) hm_pos
    rw [Nat.digits_def' one_lt_two hn, List.sum_cons, Nat.log_of_one_lt_of_le one_lt_two hn₂, ← hm]
    rcases Nat.mod_two_eq_zero_or_one n with hbit | hbit
    · rw [hbit, zero_add, show n = 2 * m by omega,
        dcDNodes_two_mul hm_pos, dcDNodes_two_mul_add_one hm_pos]
      push_cast
      linarith only [hhalf]
    · rw [hbit, show n = 2 * m + 1 by omega, dcDNodes_two_mul_add_one hm_pos,
        show 2 * m + 1 + 1 = 2 * (m + 1) by omega, dcDNodes_two_mul (Nat.succ_pos m)]
      push_cast
      linarith only [hhalf]

end

end MetaMathlibExt
