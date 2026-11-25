/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.Enumerative.GijswijtProperPrefixes

/-!
# Further results on Gijswijt's sequence

Statements from Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer
Sequences 28 (2025), Article 25.4.6.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Van de Pol's tower formula for first occurrences.** For every $n \ge 4$ there is a real
number $\alpha$ with $n - 2 < \alpha < n - 1$ such that the first occurrence of $n$ in Gijswijt's
sequence is at position $2^{2^{3^{\cdot^{\cdot^{(n-2)^{\alpha}}}}}}$, a power tower whose bases
are $2, 2, 3, \ldots, n-2$ from the bottom up and whose top exponent is $\alpha$; for $n = 4$ it
is $2^{2^{\alpha}}$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Theorem 1 (`jis-2025-25.4.6-thm-1`). -/
public theorem_wanted gijswijtFirstOccurrence_tower {n : ℕ} (hn : 4 ≤ n) :
    ∃ α : ℝ, α ∈ Set.Ioo ((n : ℝ) - 2) ((n : ℝ) - 1) ∧
      (gijswijtFirstOccurrence 1 n : ℝ) =
        2 ^ (List.range' 2 (n - 3)).foldr (fun b x => (b : ℝ) ^ x) α

/-- **Concatenated glue strings occur in a block only at its end.** Let $m \ge 1$ and $t \ge 2$.
The element $m$ followed by the concatenated glue string $T^{(m)}_t$ is a suffix of the block
$B^{(m)}_t$, and whenever $B^{(m)}_t = X\,T^{(m)}_t\,Y$ for strings $X$ and $Y$, the string $Y$ is
empty; that is, $T^{(m)}_t$ occurs in $B^{(m)}_t$ only as a suffix.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 4 (`jis-2025-25.4.6-lem-4`). -/
public theorem_wanted gijswijtGlueConcat_suffix_block {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    m :: gijswijtGlueConcat m t <:+ gijswijtBlock m t ∧
      ∀ X Y : List ℕ, gijswijtBlock m t = X ++ gijswijtGlueConcat m t ++ Y → Y = []

/-- **Concatenated glue strings are the next-order prefixes with small curling number.** Let
$m \ge 1$. A finite string $P$ of natural numbers is a prefix of the $(m+1)$th order Gijswijt
sequence $A^{(m+1)}$ with curling number $\mathcal{C}(P) \le m$ if and only if $P = T^{(m)}_t$ for
some $t \ge 1$, where $T^{(m)}_t$ is the concatenated glue string.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 5 (`jis-2025-25.4.6-lem-5`). -/
public theorem_wanted gijswijtGlueConcat_iff_prefix {m : ℕ} (hm : 1 ≤ m) (P : List ℕ) :
    (P = gijswijtPrefix (m + 1) P.length ∧ curlingNumber P ≤ m) ↔
      ∃ t, 1 ≤ t ∧ P = gijswijtGlueConcat m t

/-- **Runs of the smallest term in a block.** Let $m \ge 1$ and $t \ge 2$, and consider the block
$B_t^{(m)}$ of the $m$th order Gijswijt sequence. Every maximal run of consecutive terms equal to
$m$ in $B_t^{(m)}$ has length exactly $m + 1$, and the term right after the run exists and equals
$m + 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 6 (`jis-2025-25.4.6-lem-6`). -/
public theorem_wanted gijswijtBlock_runs {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) (j r : ℕ)
    (hr : 0 < r) (hrun : ∀ i, j ≤ i → i < j + r → (gijswijtBlock m t)[i]? = some m)
    (hleft : j = 0 ∨ (gijswijtBlock m t)[j - 1]? ≠ some m)
    (hright : (gijswijtBlock m t)[j + r]? ≠ some m) :
    r = m + 1 ∧ (gijswijtBlock m t)[j + r]? = some (m + 1)

/-- **First occurrences end blocks.** Let $1 \le m \le n$, and write $\beta^{(m)}(t)$ for the
length of the block $B_t^{(m)}$ of the $m$th order Gijswijt sequence $A^{(m)}$. Then there is a
$t \ge 1$ such that $A^{(m)}(\beta^{(m)}(t)) = n$ and $\beta^{(m)}(t)$ is the position of the
first occurrence of $n$ in $A^{(m)}$; that is, the first $n$ in $A^{(m)}$ is the last term of the
block $B_t^{(m)}$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 7 (`jis-2025-25.4.6-lem-7`). -/
public theorem_wanted gijswijtFirstOccurrence_eq_blockLength {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ∃ t, 1 ≤ t ∧ gijswijtTerm m (gijswijtBlockLength m t) = n ∧
      gijswijtBlockLength m t = gijswijtFirstOccurrence m n

/-- **Concatenated glue strings at first occurrences are blocks of the next order.** Let $m \ge 1$
and $n \ge m + 1$. For $j \ge 1$ let $t(j, n)$ be the least $t \ge 1$ such that the block
$B^{(j)}_t$ of the $j$th order Gijswijt sequence has length equal to the position of the first
occurrence of $n$ in that sequence (this position is taken to be $0$ if $n$ does not occur), and
$t(j, n) = 0$ if there is no such $t$. Then the concatenated glue string $T^{(m)}_{t(m,n)}$
equals the block $B^{(m+1)}_{t(m+1,n)}$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 9 (`jis-2025-25.4.6-lem-9`). -/
public theorem_wanted gijswijtGlueConcat_blockIndex {m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    gijswijtGlueConcat m (gijswijtBlockIndex m n) =
      gijswijtBlock (m + 1) (gijswijtBlockIndex (m + 1) n)

/-- **Curling number of block words with a maximal exponent.** Let $m \ge 1$ and $u \ge 1$, and
let $a_1, \dots, a_{u-1} \in \{0, \dots, m+1\}$ with $a_i = m + 1$ for some $1 \le i \le u - 1$.
Writing $B_t = B_t^{(m+1)}$ for the blocks of the $(m+1)$th order Gijswijt sequence $A^{(m+1)}$,
the string $P = B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$ has curling number
$\mathcal{C}(P) = m + 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 12 (`jis-2025-25.4.6-lem-12`). -/
public theorem_wanted curlingNumber_blockWord_of_max {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ i → i < u → a i ≤ m + 1)
    (hmax : ∃ i, 1 ≤ i ∧ i < u ∧ a i = m + 1) :
    curlingNumber (gijswijtBlockWord (m + 1) u a) = m + 1

/-- **Curling number of block words with small exponents.** Let $m \ge 1$ and $u \ge 2$, and let
$a_1, \dots, a_{u-1} \in \{0, \dots, m\}$ with $a_1 \ne 0$. Writing $B_t = B_t^{(m+1)}$ for the
blocks of the $(m+1)$th order Gijswijt sequence $A^{(m+1)}$, the string
$P = B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$ has curling number $\mathcal{C}(P) \le m$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 13 (`jis-2025-25.4.6-lem-13`). -/
public theorem_wanted curlingNumber_blockWord_le {m u : ℕ} (hm : 1 ≤ m) (hu : 2 ≤ u)
    (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ i → i < u → a i ≤ m) (ha1 : a 1 ≠ 0) :
    curlingNumber (gijswijtBlockWord (m + 1) u a) ≤ m

/-- **Concatenated glue strings inside a block of the next order.** Let $m \ge 1$ and $u \ge 2$,
and for exponents $a_1, \ldots, a_{u-1}$ let
$W(a) = (B^{(m+1)}_{u-1})^{a_{u-1}} \cdots (B^{(m+1)}_1)^{a_1}$ be the word in the blocks of the
$(m+1)$th order Gijswijt sequence. (a) If $t \ge 1$ and the concatenated glue string $T^{(m)}_t$
is a proper prefix of $B^{(m+1)}_u$, then $T^{(m)}_t = W(a)$ for some
$a_1, \ldots, a_{u-1} \in \{0, \ldots, m\}$. (b) For all $a_1, \ldots, a_{u-1} \in \{0, \ldots, m\}$
with $a_1 \ne 0$, there is $t \ge 1$ such that $T^{(m)}_t$ is a proper prefix of $B^{(m+1)}_u$ and
$W(a) = T^{(m)}_t$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 16 (`jis-2025-25.4.6-lem-16`). -/
public theorem_wanted gijswijtGlueConcat_blockWord {m u : ℕ} (hm : 1 ≤ m) (hu : 2 ≤ u) :
    (∀ t, 1 ≤ t → gijswijtGlueConcat m t <+: gijswijtBlock (m + 1) u →
        (gijswijtGlueConcat m t).length < (gijswijtBlock (m + 1) u).length →
        ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ m) ∧
          gijswijtGlueConcat m t = gijswijtBlockWord (m + 1) u a) ∧
    (∀ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ m) → a 1 ≠ 0 →
      ∃ t, 1 ≤ t ∧ gijswijtGlueConcat m t <+: gijswijtBlock (m + 1) u ∧
        (gijswijtGlueConcat m t).length < (gijswijtBlock (m + 1) u).length ∧
        gijswijtBlockWord (m + 1) u a = gijswijtGlueConcat m t)

/-- **Bounds on the block lengths of order $m+1$.** Let $m \ge 1$ and $u \ge 2$. Write
$\beta^{(m+1)}(u)$ for the length of the block $B_u^{(m+1)}$ of the $(m+1)$th order Gijswijt
sequence, and $\tau^{(m)}(t)$ for the length of $T_t^{(m)} = S_1^{(m)} \cdots S_{t-1}^{(m)}$, the
concatenation of the first $t - 1$ glue strings of order $m$. Then
$\tau^{(m)}(m (m+1)^{u-2}) \le \beta^{(m+1)}(u) \le \tau^{(m)}((m+1)^{u-1} + 1)$, and the second
inequality is strict when $u = m + 3$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 17 (`jis-2025-25.4.6-lem-17`). -/
public theorem_wanted gijswijtBlockLength_estimates {m u : ℕ} (hm : 1 ≤ m) (hu : 2 ≤ u) :
    (gijswijtGlueConcat m (m * (m + 1) ^ (u - 2))).length ≤ gijswijtBlockLength (m + 1) u ∧
      gijswijtBlockLength (m + 1) u ≤ (gijswijtGlueConcat m ((m + 1) ^ (u - 1) + 1)).length ∧
      (u = m + 3 →
        gijswijtBlockLength (m + 1) u < (gijswijtGlueConcat m ((m + 1) ^ (u - 1) + 1)).length)

/-- **Length estimates for concatenated glue strings.** Let $m \ge 1$ and $t \ge 2$, write
$\tau^{(m)}(t)$ for the length of the concatenated glue string $T^{(m)}_t$ and $\beta^{(m+1)}$ for
the block lengths of the $(m+1)$th order Gijswijt sequence, and let $c$ be the least natural
number with $t \le (m+1)^c$, that is, $c = \lceil \log_{m+1} t \rceil$. Then
$\beta^{(m+1)}(c) \le \tau^{(m)}(t) \le \beta^{(m+1)}(c + 2)$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Proposition 18 (`jis-2025-25.4.6-prop-18`). -/
public theorem_wanted gijswijtGlueConcat_length_estimates {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    gijswijtBlockLength (m + 1) (Nat.clog (m + 1) t) ≤ (gijswijtGlueConcat m t).length ∧
      (gijswijtGlueConcat m t).length ≤ gijswijtBlockLength (m + 1) (Nat.clog (m + 1) t + 2)

/-- **Recursive estimate for the block index.** Let $m \ge 1$ and $n \ge m + 3$, and for $k \ge 1$
let $t(k, n)$ be the index $t$ such that the first occurrence of $n$ in the $k$th order Gijswijt
sequence $A^{(k)}$ is the last element of the block $B_t^{(k)}$ of $A^{(k)}$. Then
$m (m+1)^{t(m+1,n) - 2} \le t(m, n) \le (m+1)^{t(m+1,n) - 1} + 1$, and the second inequality is
strict when $n = m + 3$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Proposition 19 (`jis-2025-25.4.6-prop-19`). -/
public theorem_wanted gijswijtBlockIndex_estimates {m n : ℕ} (hm : 1 ≤ m) (hn : m + 3 ≤ n) :
    m * (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 2) ≤ gijswijtBlockIndex m n ∧
      gijswijtBlockIndex m n ≤ (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 1) + 1 ∧
      (n = m + 3 → gijswijtBlockIndex m n < (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 1) + 1)

/-- **Upper bound on block lengths.** Let $M_7 = 4$ and $M_{k+1} = M_k (1 + 9 (k+1)^{1.59} / 2^k)$
for $k \ge 7$. Then for all $m \ge 1$ and $u \ge 7$, the block lengths $\beta^{(m)}(u)$ of the
$m$th order Gijswijt sequence $A^{(m)}$ satisfy $\beta^{(m)}(u) / (m+1)^{u-1} < M_u$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 20 (`jis-2025-25.4.6-lem-20`). -/
public theorem_wanted gijswijtBlockLength_div_lt (M : ℕ → ℝ) (hM7 : M 7 = 4)
    (hM : ∀ k, 7 ≤ k → M (k + 1) = M k * (1 + 9 * ((k : ℝ) + 1) ^ (1.59 : ℝ) / 2 ^ k))
    {m u : ℕ} (hm : 1 ≤ m) (hu : 7 ≤ u) :
    (gijswijtBlockLength m u : ℝ) / ((m : ℝ) + 1) ^ (u - 1) < M u

end

end MetaMathlibExt
