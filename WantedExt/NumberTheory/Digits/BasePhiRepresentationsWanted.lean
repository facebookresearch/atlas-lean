/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.LinearCombination
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Counting base phi representations

Statements from Michel Dekking and Ad van Loon, *Counting Base Phi
Representations*, Fibonacci Quarterly 62 (2024), no. 2, 112-124.

A finite base phi expansion with digits `0` and `1` is encoded by the finite set
`S : Finset ℤ` of positions of its digits `1`; it represents
`∑ i ∈ S, φ ^ i`. The word `B(N)` of the paper is the digit word of `S` read from
the highest to the lowest position, so a statement about `B(N)` alone is a
statement about `S` up to translation.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- **Value of a base phi expansion.** For a finite set $S$ of integers, the base phi value of
$S$ is the real number $\sum_{i \in S} \varphi^i$, where $\varphi = (1 + \sqrt 5)/2$ is the golden
ratio. It is the number represented by the base phi expansion with digit $1$ at each position in
$S$ and digit $0$ at every other position.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (definition of a base phi
representation). -/
noncomputable def basePhiValue (S : Finset ℤ) : ℝ :=
  ∑ i ∈ S, φ ^ i

/-- **Bergman expansions.** Encode a finite base phi expansion with digits $0$ and $1$ by the
finite set $S \subseteq \mathbb{Z}$ of positions of its digits $1$. The expansion is a Bergman
expansion when no two digits $1$ are adjacent, that is, $i + 1 \notin S$ for every $i \in S$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (Bergman representation). -/
def IsBergmanExpansion (S : Finset ℤ) : Prop :=
  ∀ i ∈ S, i + 1 ∉ S

/-- **Golden mean flips.** Encode a finite base phi expansion with digits $0$ and $1$ by the
finite set of positions of its digits $1$. An expansion $T$ arises from an expansion $S$ by a
golden mean flip $100 \to 011$ when there is a position $i \in S$ with $i - 1 \notin S$ and
$i - 2 \notin S$ such that $T = (S \setminus \{i\}) \cup \{i - 1, i - 2\}$: the digit $1$ at
position $i$ is replaced by digits $1$ at positions $i - 1$ and $i - 2$, which were $0$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Sections 1 and 2 (the map `T_i`). -/
def IsGoldenMeanFlip (S T : Finset ℤ) : Prop :=
  ∃ i ∈ S, i - 1 ∉ S ∧ i - 2 ∉ S ∧ T = insert (i - 1) (insert (i - 2) (S.erase i))

/-- **Knott's truncation rule.** Let $\varphi$ be the golden ratio. Encode a finite base $\varphi$
expansion with digits $0$ and $1$ by the finite set $S \subseteq \mathbb{Z}$ of the positions of
its digits $1$, and write $a_i$ for its digit at position $i$. The expansion satisfies Knott's
condition when it does not end in the digits $0, 1, 1$: if $S$ is nonempty with least element $R$,
then $a_{R+2} a_{R+1} a_R \ne 011$, that is, it is not the case that both $R + 1 \in S$ and
$R + 2 \notin S$. The empty expansion satisfies the condition.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
def SatisfiesKnottCondition (S : Finset ℤ) : Prop :=
  ∀ m ∈ S, (∀ j ∈ S, m ≤ j) → ¬ (m + 1 ∈ S ∧ m + 2 ∉ S)

/-- **Knott expansions.** Let $\varphi$ be the golden ratio and $N$ a natural number. Encode a
finite base phi expansion with digits $0$ and $1$ by the finite set $S \subseteq \mathbb{Z}$ of the
positions of its digits $1$. The Knott expansions of $N$ are the expansions of value $N$ that
satisfy Knott's truncation rule: the set of all such $S$ with $\sum_{i \in S} \varphi^i = N$ that
satisfy Knott's condition.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
def knottExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | basePhiValue S = N ∧ SatisfiesKnottCondition S}

/-- **Number of Knott expansions.** For a natural number $N$, $\mathrm{Tot}_\kappa(N)$ is the
number of Knott expansions of $N$ (OEIS A289749).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
noncomputable def knottExpansionCount (N : ℕ) : ℕ :=
  (knottExpansions N).ncard

/-- **Natural base phi expansions.** Let $\varphi$ be the golden ratio and $N$ a natural number.
Encode a finite base phi expansion with digits $0$ and $1$ by the finite set
$S \subseteq \mathbb{Z}$ of the positions of its digits $1$. The natural expansions of $N$ are the
Knott expansions $S$ of $N$ for which there is a Bergman expansion $T$ with
$\sum_{i \in T} \varphi^i = N$ whose lowest digit $1$ is at the same position as the lowest
digit $1$ of $S$, that is, $\min T = \min S$, where $S$ and $T$ both empty also counts as
equal.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
def naturalExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | S ∈ knottExpansions N ∧
    ∃ T : Finset ℤ, IsBergmanExpansion T ∧ basePhiValue T = N ∧ T.min = S.min}

/-- **Number of natural expansions.** For a natural number $N$, $\mathrm{Tot}_\nu(N)$ is the
number of natural base phi expansions of $N$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
noncomputable def naturalExpansionCount (N : ℕ) : ℕ :=
  (naturalExpansions N).ncard

/-- **Number of Fibonacci representations.** For a natural number $m$,
$\mathrm{Tot}_{\mathrm{FIB}}(m)$ is the number of finite sets $T$ of indices $i \ge 2$ with
$\sum_{i \in T} F_i = m$, where $F_i$ are the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$); that is,
the number of ways to write $m$ as a sum of Fibonacci numbers with distinct indices at least $2$
(OEIS A000119). Indices above $m + 1$ never occur because $F_{m+2} > m$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (base Fibonacci representations). -/
def fibonacciRepresentationCount (m : ℕ) : ℕ :=
  ((Finset.Icc 2 (m + 1)).powerset.filter fun T => ∑ i ∈ T, Nat.fib i = m).card

/-- **The empty base phi expansion has value zero.** The base phi value of the empty set of
positions is $0$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_empty : basePhiValue ∅ = 0 := by
  simp [basePhiValue]

/-- **The single digit $1$ at position $0$ has value one.** The base phi value of the set $\{0\}$
is $1$, that is, $\varphi^0 = 1$, where $\varphi$ is the golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_singleton_zero : basePhiValue {0} = 1 := by
  simp [basePhiValue]

/-- **The base phi expansion $10.01$ has value two.** The base phi value of the set $\{1, -2\}$
is $2$, that is, $\varphi + \varphi^{-2} = 2$, where $\varphi$ is the golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), proof of Proposition 3.1. -/
theorem basePhiValue_one_neg_two : basePhiValue {1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_pair (by decide), zpow_one, zpow_neg, zpow_ofNat, ← inv_pow,
    hinv]
  linear_combination Real.goldenRatio_sq

/-- **The base phi expansion $1.11$ has value two.** The base phi value of the set
$\{0, -1, -2\}$ is $2$, that is, $1 + \varphi^{-1} + \varphi^{-2} = 2$, where $\varphi$ is the
golden ratio.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem basePhiValue_zero_neg_one_neg_two : basePhiValue {0, -1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_pair (by decide), zpow_zero,
    zpow_neg, zpow_neg, zpow_one, zpow_ofNat, ← inv_pow, hinv]
  linear_combination Real.goldenRatio_sq

/-- **The expansion 10.01 is a Bergman expansion.** The base phi expansion $10.01$, with digits $1$
at positions $1$ and $-2$ and digits $0$ elsewhere, has no two adjacent digits $1$, so it is a
Bergman expansion.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem isBergmanExpansion_one_neg_two : IsBergmanExpansion {1, -2} := by
  unfold IsBergmanExpansion
  decide

/-- **A golden mean flip from 10.01 to 1.11.** Applying the golden mean flip $100 \to 011$ at the
leading digit of $10.01$ (the digit $1$ at position $1$, followed by digits $0$ at positions $0$
and $-1$) gives $1.11$, the expansion with digits $1$ at positions $0$, $-1$ and $-2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem isGoldenMeanFlip_one_neg_two : IsGoldenMeanFlip {1, -2} {0, -1, -2} :=
  ⟨1, by decide, by decide, by decide, by decide⟩

/-- **A Knott expansion of two.** Let $\varphi$ be the golden ratio. The base $\varphi$ expansion
$1.11$, whose digits $1$ sit at the positions $0$, $-1$ and $-2$, is a Knott expansion of $2$:
its value is $1 + \varphi^{-1} + \varphi^{-2} = 2$ and it satisfies Knott's truncation rule.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem zero_neg_one_neg_two_mem_knottExpansions : ({0, -1, -2} : Finset ℤ) ∈ knottExpansions 2 :=
  ⟨by rw [basePhiValue_zero_neg_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩

/-- **The expansion 0.11 violates Knott's truncation rule.** The finite base phi expansion
$0.11$, with digits $1$ at positions $-1$ and $-2$ and no others, ends in the digits $011$, so it
does not satisfy Knott's truncation rule.

It represents $1$, since $\varphi^{-1} + \varphi^{-2} = 1$ for the golden ratio $\varphi$, but
is not a Knott expansion of $1$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
theorem not_satisfiesKnottCondition_neg_one_neg_two :
    ¬ SatisfiesKnottCondition {-1, -2} := by
  unfold SatisfiesKnottCondition
  decide

/-- **The expansion 10.01 is a natural expansion of 2.** The finite base phi expansion $10.01$,
with digits $1$ exactly at positions $1$ and $-2$, is a natural base phi expansion of $2$.

It is the Bergman expansion of $2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
theorem one_neg_two_mem_naturalExpansions : ({1, -2} : Finset ℤ) ∈ naturalExpansions 2 :=
  ⟨⟨by rw [basePhiValue_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩,
    {1, -2}, isBergmanExpansion_one_neg_two, by rw [basePhiValue_one_neg_two]; norm_num, rfl⟩

/-- **Small values of the Fibonacci representation count.** Let $F_i$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$), and let $\mathrm{Tot}_{\mathrm{FIB}}(m)$ be the number of ways to write
$m$ as a sum of Fibonacci numbers $F_i$ with distinct indices $i \ge 2$. Then
$\mathrm{Tot}_{\mathrm{FIB}}(0), \dots, \mathrm{Tot}_{\mathrm{FIB}}(8)$ are
$1, 1, 1, 2, 1, 2, 2, 1, 3$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (the listed values of `Tot_FIB`). -/
theorem fibonacciRepresentationCount_small :
    (List.range 9).map fibonacciRepresentationCount = [1, 1, 1, 2, 1, 2, 2, 1, 3] := by
  decide

/-- **Golden mean flips connect all expansions to the Bergman expansion.** Let $N$ be a natural
number, let $S$ be a Bergman expansion of $N$ and let $T$ be any finite base phi expansion of
$N$ with digits $0$ and $1$. Then $T$ is obtained from $S$ by finitely many (possibly zero)
golden mean flips $100 \to 011$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.1
(`fq-2024-dekking11102023-thm-2.1`). -/
public theorem_wanted reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion (N : ℕ)
    {S T : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    (hTN : basePhiValue T = N) :
    Relation.ReflTransGen IsGoldenMeanFlip S T

/-- **Recursion for the number of Knott expansions.** Let $\varphi$ be the golden ratio, let
$N \ge 2$ and $n$ be natural numbers, and let $p_0, \dots, p_n$ be integers with
$p_{k+1} \ge p_k + 2$ for all $k < n$ and $\sum_{k=0}^{n} \varphi^{p_k} = N$. Thus $N$ has the
base phi expansion $10^{s_n} \cdots 10^{s_1} 1$ with digits $1$ at positions $p_0 < \dots < p_n$,
where $s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$; if $n \ge 1$, let $r_1 = s_1/2 + 1$ when $s_1$ is even and $r_1 = (s_1 + 1)/2 + 1$
when $s_1$ is odd; and for $2 \le k \le n$, let $r_k = (s_k/2 + 1)\, r_{k-1}$ when $s_k$ is even
and $r_k = ((s_k + 1)/2 + 1)\, r_{k-1} - r_{k-2}$ when $s_k$ is odd. Then the number of Knott
expansions of $N$ is $r_n$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.3
(`fq-2024-dekking11102023-thm-2.3`). -/
public theorem_wanted knottExpansionCount_eq_of_recursion (N : ℕ) (hN : 2 ≤ N) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 3))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (knottExpansionCount N : ℤ) = r n

/-- **Bergman expansions of the Fibonacci numbers.** Let $n \ge 1$ and write $F_m$ for the $m$-th
Fibonacci number, with $F_1 = F_2 = 1$. Let $S$ be a finite set of integers with no two
consecutive elements (a Bergman expansion). If the base phi value of $S$ is $F_{2n}$, then
$S = \{t + 4j : 0 \le j < n\}$ for some integer $t$. If the base phi value of $S$ is
$F_{2n+1}$, then $S = \{t\} \cup \{t + 3 + 4j : 0 \le j < n\}$ for some integer $t$.

Read from the highest to the lowest position, these are the digit words $(1000)^{n-1}1$ and
$(1000)^{n-1}1001$; the position of the radix point is not determined.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 3.1
(`fq-2024-dekking11102023-prop-3.1`). -/
public theorem_wanted bergmanWord_fib (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n) →
      ∃ t : ℤ, S = (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + t) ∧
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n + 1) →
      ∃ t : ℤ, S = insert t ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + t))

/-- **Knott expansions of Fibonacci numbers.** Let $F_n$ be the Fibonacci numbers ($F_0 = 0$,
$F_1 = 1$). For every $n \ge 1$, the number of Knott expansions of $F_n$ is $F_n$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.2
(`fq-2024-dekking11102023-thm-3.2`). -/
public theorem_wanted knottExpansionCount_fib (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (Nat.fib n) = Nat.fib n

/-- **Knott expansions of Lucas numbers.** For every $n \ge 1$, each of the Lucas numbers $L_{2n}$
and $L_{2n+1}$ (with $L_0 = 2$, $L_1 = 1$) has exactly $2n + 1$ Knott expansions.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.3
(`fq-2024-dekking11102023-thm-3.3`). -/
public theorem_wanted knottExpansionCount_lucasNumber (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (lucasNumber (2 * n)) = 2 * n + 1 ∧
      knottExpansionCount (lucasNumber (2 * n + 1)) = 2 * n + 1

/-- **Recursion for the number of natural expansions.** Let $N$ and $n$ be natural numbers and
let $p_0, \dots, p_n$ be integers with $p_k + 2 \le p_{k+1}$ for $k < n$ such that the base phi
expansion with digits $1$ at positions $p_0, \dots, p_n$ represents $N$. Put
$s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$ such that, if $n \ge 1$, $2 r_1 = s_1 + 2$ when $s_1$ is even and $2 r_1 = s_1 + 1$
when $s_1$ is odd, and for $2 \le k \le n$, $2 r_k = (s_k + 2) r_{k-1}$ when $s_k$ is even and
$2 r_k = (s_k + 3) r_{k-1} - 2 r_{k-2}$ when $s_k$ is odd. Then the number
$\mathrm{Tot}_\nu(N)$ of natural base phi expansions of $N$ equals $r_n$.

Compared with the recursion for the number of Knott expansions, only the value of $r_1$ for odd
$s_1$ differs, and $N \ge 2$ is not assumed.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.1
(`fq-2024-dekking11102023-thm-4.1`). -/
public theorem_wanted naturalExpansionCount_eq_of_recursion (N : ℕ) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 1))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (naturalExpansionCount N : ℤ) = r n

/-- **Fibonacci numbers in the Lucas intervals.** Let $F_k$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$) and $L_k$ the Lucas numbers ($L_0 = 2$, $L_1 = 1$). Call
$\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ the even Lucas interval and
$\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$ the odd Lucas interval. For every $n \ge 1$,
$F_{2n+2} \in \Lambda_{2n}$ and $F_{2n+3} \in \Lambda_{2n+1}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Lemma 4.2
(`fq-2024-dekking11102023-lem-4.2`). -/
public theorem_wanted fib_mem_lucasIntervals (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n + 2) ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) ∧
      Nat.fib (2 * n + 3) ∈
        Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1)

/-- **Natural expansions of Fibonacci numbers.** Write $\mathrm{Tot}_\nu(N)$ for the number of
natural base phi expansions of a natural number $N$ and $F_k$ for the $k$-th Fibonacci number.
Then for every $n \ge 0$, $\mathrm{Tot}_\nu(F_{2n+2}) = F_{2n+1}$ and
$\mathrm{Tot}_\nu(F_{2n+3}) = F_{2n+3}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.3
(`fq-2024-dekking11102023-thm-4.3`). -/
public theorem_wanted naturalExpansionCount_fib (n : ℕ) :
    naturalExpansionCount (Nat.fib (2 * n + 2)) = Nat.fib (2 * n + 1) ∧
      naturalExpansionCount (Nat.fib (2 * n + 3)) = Nat.fib (2 * n + 3)

/-- **Natural expansions are counted by Fibonacci representations.** Write $F_k$ for the $k$-th
Fibonacci number. Let $N > 3$ be a natural number, let $S$ be a Bergman expansion of $N$ and let
$R$ be the lowest position of a digit $1$ in $S$. Then the number $\mathrm{Tot}_\nu(N)$ of natural
base phi expansions of $N$ equals the number $\mathrm{Tot}_{\mathrm{FIB}}(F_{2-R} N)$ of
representations of $F_{2-R} N$ as a sum of Fibonacci numbers with distinct indices at least $2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.4
(`fq-2024-dekking11102023-thm-4.4`). -/
public theorem_wanted naturalExpansionCount_eq_fibonacciRepresentationCount (N : ℕ)
    (hN : 3 < N) {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    {R : ℤ} (hR : IsLeast (S : Set ℤ) R) :
    naturalExpansionCount N = fibonacciRepresentationCount (Nat.fib (2 - R).toNat * N)

/-- **Lucas interval of $N$ from the gap between its two lowest Bergman digits.** Let $N \ge 2$
be a natural number, let $S$ be a finite set of integers with no two consecutive elements (a
Bergman expansion) whose base phi value is $N$, and let $a$ be an integer and $s$ a natural number
such that the elements of $S$ that are at most $a + s + 1$ are exactly $a$ and $a + s + 1$ (so the
expansion ends in the digits $10^s1$). Write $L_m$ for the $m$-th Lucas number. Then
$L_{2n} \le N \le L_{2n+1}$ for some natural number $n$ if and only if $s$ is odd, and
$L_{2n+1} + 1 \le N \le L_{2n+2} - 1$ for some natural number $n$ if and only if $s$ is even.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(a)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem_wanted bergman_tail_parity_iff_lucasInterval (N : ℕ) (hN : 2 ≤ N)
    {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) (a : ℤ) (s : ℕ)
    (htail : S.filter (· ≤ a + s + 1) = {a, a + s + 1}) :
    ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1))) ↔ Odd s) ∧
      ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1)) ↔
        Even s)

/-- **Lowest Bergman digit of $N$ from its Lucas interval.** Let $N$ and $n$ be natural numbers,
let $S$ be a finite set of integers with no two consecutive elements (a Bergman expansion) whose
base phi value is $N$, and let $R$ be the least element of $S$. Write $L_m$ for the $m$-th Lucas
number. If $L_{2n} \le N \le L_{2n+1}$, then $-R = 2n$. If $L_{2n+1} + 1 \le N \le L_{2n+2} - 1$,
then $-R = 2n + 2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(b)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem_wanted bergman_lowest_position_lucasInterval (N n : ℕ) {S : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) {R : ℤ}
    (hR : IsLeast (S : Set ℤ) R) :
    (N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) → -R = 2 * n) ∧
      (N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1) →
        -R = 2 * n + 2)

/-- **Bergman expansion of $L_{2n} + k$.** Let $n \ge 1$ and let $k$ be a natural number with
$k \le L_{2n-1}$, where $L_m$ is the $m$-th Lucas number. Let $S$ and $T$ be finite sets of
integers, each with no two consecutive elements (Bergman expansions), whose base phi values are
$k$ and $L_{2n} + k$ respectively. Then $2n \notin S$, $-2n \notin S$, and
$T = S \cup \{2n, -2n\}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 I,
quoting F. M. Dekking, *How to add two numbers in base phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem_wanted bergman_lucas_even_add (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) {S T : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSk : basePhiValue S = k)
    (hT : IsBergmanExpansion T) (hTN : basePhiValue T = (lucasNumber (2 * n) + k : ℕ)) :
    (2 * n : ℤ) ∉ S ∧ -(2 * n : ℤ) ∉ S ∧ T = insert (2 * n : ℤ) (insert (-(2 * n : ℤ)) S)

/-- **Recursive structure of Bergman expansions, odd Lucas case.** Let $n \ge 2$, let $k$ be a
natural number, and write $L_m$ for the $m$-th Lucas number. Call a finite set of integers with no
two consecutive elements a Bergman expansion. Let $S$ and $T$ be Bergman expansions, let $a$ and
$t$ be the least and the greatest element of $S$, let $S' = S \setminus \{a, t\}$, and for an
integer $c$ write $S' + c = \{x + c : x \in S'\}$.

(i) If $1 \le k \le L_{2n-2} - 1$, the base phi value of $S$ is $L_{2n-1} + k$ and that of $T$
is $L_{2n+1} + k$, then there is an integer $b$ with
$T = \{b, b + 3, b + (t - a) + 4\} \cup (S' + (b - a + 2))$.

(ii) If $1 \le k \le L_{2n-2} - 1$, the base phi value of $S$ is $L_{2n-1} + k$ and that of $T$
is $L_{2n+1} + L_{2n-1} + k$, then there is an integer $b$ with
$T = \{b, b + (t - a) + 2, b + (t - a) + 4\} \cup (S' + (b - a + 2))$.

(iii) If $k \le L_{2n-3}$, the base phi value of $S$ is $L_{2n-2} + k$ and that of $T$ is
$L_{2n+1} + L_{2n-2} + k$, then there is an integer $b$ with
$T = \{b, b + 3, b + (t - a) + 4, b + (t - a) + 7\} \cup (S' + (b - a + 4))$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 II,
quoting F. M. Dekking, *How to add two numbers in base phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem_wanted bergman_lucas_odd_add (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + (t - a) + 2, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, k ≤ lucasNumber (2 * n - 3) →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 2) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 2) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4, b + (t - a) + 7} ∪
          ((S.erase a).erase t).image (· + (b - a + 4)))

end

end MetaMathlibExt
