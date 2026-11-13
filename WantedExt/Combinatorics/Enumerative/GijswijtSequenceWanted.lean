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

/-!
# The growth rate of Gijswijt's sequence

Statements from Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer
Sequences 28 (2025), Article 25.4.6. Definitions follow the paper (arXiv:2209.04657v3).

Strings are `List ℕ`. The curling number `𝒞(S)` is the largest `k` with `S = X Y^k`, `Y`
nonempty, and `𝒞(ε) = 1`. The `m`th order sequence is `A^{(m)}(1) = m`,
`A^{(m)}(n+1) = max(m, 𝒞(A^{(m)}(1) ⋯ A^{(m)}(n)))`; since `𝒞(ε) = 1`, the first term is also
`max(m, 𝒞(ε))` for `m ≥ 1`, so `gijswijtPrefix m n` builds the first `n` terms by one rule.

The paper takes the blocks `B_t^{(m)}` and glue strings `S_t^{(m)}` from the recursive structure
of van de Bult, Gijswijt, Linderman, Sloane and Wilks: `B_1 = m`, `B_{t+1} = (B_t)^{m+1} S_t`,
every `B_t` is a prefix of `A^{(m)}`, and `S_t` is nonempty with all elements at least `m + 1`.
Since `B_{t+2}` starts with two copies of `B_{t+1}`, the element after `B_{t+1}` is `m`, so these
relations determine `S_t` as the run of elements of `A^{(m)}` after position `(m+1) β(t)` up to
the next `m`. This is the definition of the block lengths `β^{(m)}(t)` used below; the blocks
are the corresponding prefixes, `T_t^{(m)} = S_1^{(m)} ⋯ S_{t-1}^{(m)}`, and `τ^{(m)}(t)` is the
length of `T_t^{(m)}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Curling number.** The curling number $\mathcal{C}(S)$ of a finite string $S$ of natural
numbers is the largest integer $k$ such that $S = X Y^k$ for some strings $X$ and $Y$ with $Y$
nonempty; for the empty string $\varepsilon$ it is $\mathcal{C}(\varepsilon) = 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number) and Section 1.2 (`𝒞(ε) := 1`). -/
public def curlingNumber (S : List ℕ) : ℕ :=
  ((Finset.range (S.length + 1)).filter fun k => ∃ l < S.length + 1, 1 ≤ l ∧
      k * l ≤ S.length ∧
        S.drop (S.length - k * l) = (List.replicate k (S.drop (S.length - l))).flatten).sup id ⊔ 1

/-- **Curling number of $112112223$.** The string $112112223$ has curling number
$\mathcal{C}(112112223) = 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number examples). -/
public theorem curlingNumber_example_one : curlingNumber [1, 1, 2, 1, 1, 2, 2, 2, 3] = 1 := by
  decide

/-- **Curling number of $222322232223$.** The string $222322232223$ has curling number
$\mathcal{C}(222322232223) = 3$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number examples). -/
public theorem curlingNumber_example_three :
    curlingNumber [2, 2, 2, 3, 2, 2, 2, 3, 2, 2, 2, 3] = 3 := by
  decide

/-- **Curling number of the empty string.** The empty string $\varepsilon$ has curling number
$\mathcal{C}(\varepsilon) = 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1.2 (`𝒞(ε) := 1`). -/
public theorem curlingNumber_nil : curlingNumber [] = 1 := by
  decide

/-- **Prefixes of the $m$th order Gijswijt sequence.** Let $m$ and $n$ be natural numbers. The
list of the first $n$ terms of the $m$th order sequence $A^{(m)}$ is defined by recursion on $n$:
for $n = 0$ it is the empty list, and the list for $n + 1$ is the list $P$ for $n$ followed by
the term $\max(m, \mathcal{C}(P))$, where $\mathcal{C}(P)$ is the curling number of $P$ (the
largest $k$ with $P = XY^k$ for strings $X$, $Y$ with $Y$ nonempty, and $1$ for the empty string).
For $m \ge 1$ the first term is therefore $A^{(m)}(1) = m$; the case $m = 1$ is Gijswijt's
sequence.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (definition of `A^{(m)}`). -/
public def gijswijtPrefix (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => gijswijtPrefix m n ++ [max m (curlingNumber (gijswijtPrefix m n))]

/-- **Terms of the $m$th order Gijswijt sequence.** For $k \ge 1$, $A^{(m)}(k)$ is the $k$th
term of the $m$th order sequence $A^{(m)}$, that is, the last entry of the list of its first $k$
terms. For $k = 0$ the value is $0$ by convention.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (definition of `A^{(m)}`). -/
public def gijswijtTerm (m k : ℕ) : ℕ :=
  (gijswijtPrefix m k).getLastD 0

/-- **First terms of Gijswijt's sequence.** The first nine terms of Gijswijt's sequence $A^{(1)}$
are $1, 1, 2, 1, 1, 2, 2, 2, 3$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (initial terms of `A`). -/
public theorem gijswijtPrefix_one_nine :
    gijswijtPrefix 1 9 = [1, 1, 2, 1, 1, 2, 2, 2, 3] := by
  decide

/-- **Initial terms of the second-order Gijswijt sequence.** The first eight terms of the
second-order sequence $A^{(2)}$ are $2, 2, 2, 3, 2, 2, 2, 3$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (initial terms of `A^{(2)}`). -/
public theorem gijswijtPrefix_two_eight :
    gijswijtPrefix 2 8 = [2, 2, 2, 3, 2, 2, 2, 3] := by
  decide

/-- **First occurrence of a value in a Gijswijt sequence.** For natural numbers $m$ and $n$, the
first occurrence of $n$ in the $m$th order Gijswijt sequence $A^{(m)}$ is the least position
$k \ge 1$ with $A^{(m)}(k) = n$, and it is $0$ if $n$ does not occur in $A^{(m)}$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (first occurrence) and Section 3 (definition of
`t(m, n)`). -/
public noncomputable def gijswijtFirstOccurrence (m n : ℕ) : ℕ :=
  sInf {k | 1 ≤ k ∧ gijswijtTerm m k = n}

/-- **Block lengths of the higher-order Gijswijt sequences.** For a natural number $m$, write
$A^{(m)}(k)$ for the $k$th term of the $m$th order sequence. The block lengths $\beta^{(m)}(t)$
are defined by $\beta^{(m)}(0) = 0$, $\beta^{(m)}(1) = 1$ and, for $t \ge 1$, $\beta^{(m)}(t+1)$
is the least $k > (m+1)\,\beta^{(m)}(t)$ with $A^{(m)}(k+1) = m$, or $0$ if there is no such $k$.

This matches the paper's recursion $B_{t+1} = (B_t)^{m+1} S_t$ for the blocks $B_t$: the glue
string $S_t$ is the run of terms after position $(m+1)\,\beta^{(m)}(t)$ up to the next $m$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (blocks `B_t^{(m)}`, glue strings `S_t^{(m)}`, and their
lengths `β^{(m)}(t)`). -/
public noncomputable def gijswijtBlockLength (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | t + 2 => sInf {k | (m + 1) * gijswijtBlockLength m (t + 1) < k ∧ gijswijtTerm m (k + 1) = m}

/-- **Gijswijt blocks.** For natural numbers $m$ and $t$, the block $B_t^{(m)}$ is the prefix of
length $\beta^{(m)}(t)$ of the $m$th order Gijswijt sequence $A^{(m)}$, where $\beta^{(m)}(t)$ is
the $t$th block length.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (blocks `B_t^{(m)}`). -/
public noncomputable def gijswijtBlock (m t : ℕ) : List ℕ :=
  gijswijtPrefix m (gijswijtBlockLength m t)

/-- **Glue strings of a Gijswijt sequence.** For natural numbers $m$ and $t$, the glue string
$S^{(m)}_t$ is the block $B^{(m)}_{t+1}$ of the $m$th order Gijswijt sequence with its first
$(m+1)\,\beta^{(m)}(t)$ elements removed, where $\beta^{(m)}(t)$ is the length of the block
$B^{(m)}_t$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (glue strings `S_t^{(m)}`). -/
public noncomputable def gijswijtGlue (m t : ℕ) : List ℕ :=
  (gijswijtBlock m (t + 1)).drop ((m + 1) * gijswijtBlockLength m t)

/-- **Concatenated glue strings of a Gijswijt sequence.** For natural numbers $m$ and $t$, the
string $T^{(m)}_t$ is the concatenation $S^{(m)}_1 S^{(m)}_2 \cdots S^{(m)}_{t-1}$ of the glue
strings of the $m$th order Gijswijt sequence; it is empty when $t \le 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (strings `T_t^{(m)}`). -/
public noncomputable def gijswijtGlueConcat (m t : ℕ) : List ℕ :=
  ((List.range (t - 1)).map fun i => gijswijtGlue m (i + 1)).flatten

/-- **Block index of the first occurrence.** For natural numbers $m$ and $n$, let $p$ be the
position of the first occurrence of $n$ in the $m$th order Gijswijt sequence $A^{(m)}$, with
$p = 0$ if $n$ does not occur. Then $t(m, n)$ is the least $t \ge 1$ such that the block length
$\beta^{(m)}(t)$ equals $p$, so that when $n$ occurs, this first $n$ is the last element of the
block $B_t^{(m)}$; if there is no such $t$, then $t(m, n) = 0$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 3 (definition of `t(m, n)`). -/
public noncomputable def gijswijtBlockIndex (m n : ℕ) : ℕ :=
  sInf {t | 1 ≤ t ∧ gijswijtBlockLength m t = gijswijtFirstOccurrence m n}

/-- **Block words.** For natural numbers $m$ and $u$ and exponents $a_1, a_2, \ldots$, the block
word of order $m$ is the concatenation $B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$, where
$B_i = B_i^{(m)}$ is the $i$th block of the $m$th order Gijswijt sequence and $B_i^{a_i}$ is
$a_i$ copies of $B_i$ in a row. Only $a_1, \ldots, a_{u-1}$ are used, and the word is empty when
$u \le 1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 4, Expression (1) in Lemma 11. -/
public noncomputable def gijswijtBlockWord (m u : ℕ) (a : ℕ → ℕ) : List ℕ :=
  ((List.range (u - 1)).reverse.map fun i =>
    (List.replicate (a (i + 1)) (gijswijtBlock m (i + 1))).flatten).flatten

/-- **The first block has length one.** For every natural number $m$, the first block length
$\beta^{(m)}(1)$ of the $m$th order Gijswijt sequence equals $1$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (`B_1^{(m)} = m`). -/
public theorem gijswijtBlockLength_one (m : ℕ) : gijswijtBlockLength m 1 = 1 := rfl

/-- **The first block.** For every $m \ge 1$, the first block $B_1^{(m)}$ of the $m$th order
Gijswijt sequence is the one-term string $m$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (`B_1^{(m)} = m`, Table 1). -/
public theorem gijswijtBlock_one {m : ℕ} (hm : 1 ≤ m) : gijswijtBlock m 1 = [m] := by
  simp [gijswijtBlock, gijswijtBlockLength_one, gijswijtPrefix, curlingNumber_nil,
    Nat.max_eq_left hm]

/-- **The first concatenated glue string is empty.** For every natural number $m$, the
concatenated glue string $T^{(m)}_1$ is the empty string.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (Table 1). -/
public theorem gijswijtGlueConcat_one (m : ℕ) : gijswijtGlueConcat m 1 = [] := by
  simp [gijswijtGlueConcat]

/-- **The empty block word.** For every natural number $m$ and every sequence of exponents
$a_1, a_2, \ldots$, the block word $B_{u-1}^{a_{u-1}} \cdots B_1^{a_1}$ of order $m$ with $u = 1$,
where $B_i$ is the $i$th block of the $m$th order Gijswijt sequence, is a product of no blocks
and hence the empty string.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, proof of Lemma 11 (case `u = 1`). -/
public theorem gijswijtBlockWord_one (m : ℕ) (a : ℕ → ℕ) : gijswijtBlockWord m 1 a = [] := by
  simp [gijswijtBlockWord]

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

/-- **The curling number is monotone under suffixes.** For strings $S$ and $T$ of natural numbers,
if $T$ is a suffix of $S$, then $\mathcal{C}(T) \le \mathcal{C}(S)$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 3 (`jis-2025-25.4.6-lem-3`). -/
public theorem_wanted curlingNumber_le_of_suffix {S T : List ℕ} (h : T <:+ S) :
    curlingNumber T ≤ curlingNumber S

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

/-- **Proper prefixes of a block with curling number at most $m + 1$.** Let $m \ge 1$ and
$u \ge 1$, and write $B_t$ for the block $B_t^{(m+1)}$ of the $(m+1)$th order Gijswijt sequence.
A string $P$ is a proper prefix of $B_u$ (a prefix strictly shorter than $B_u$) with curling
number $\mathcal{C}(P) \le m + 1$ if and only if $P = B_{u-1}^{a_{u-1}} \cdots B_2^{a_2} B_1^{a_1}$
for some natural numbers $a_1, \dots, a_{u-1} \le m + 1$, where $B_t^{a}$ denotes $a$ copies of
$B_t$ concatenated.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 11 (`jis-2025-25.4.6-lem-11`). -/
public theorem_wanted gijswijtProperPrefix_curling_iff {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (P : List ℕ) :
    (P <+: gijswijtBlock (m + 1) u ∧ P.length < (gijswijtBlock (m + 1) u).length ∧
        curlingNumber P ≤ m + 1) ↔
      ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ m + 1) ∧ P = gijswijtBlockWord (m + 1) u a

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
