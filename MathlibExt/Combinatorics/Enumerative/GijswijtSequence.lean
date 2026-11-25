/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.Order.Lattice.Nat

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

/-- **The curling number is monotone under suffixes.** For strings $S$ and $T$ of natural numbers,
if $T$ is a suffix of $S$, then $\mathcal{C}(T) \le \mathcal{C}(S)$.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 3 (`jis-2025-25.4.6-lem-3`). -/
public theorem curlingNumber_le_of_suffix {S T : List ℕ} (h : T <:+ S) :
    curlingNumber T ≤ curlingNumber S := by
  obtain ⟨P, rfl⟩ := h
  have hdrop (n : ℕ) (hn : n ≤ T.length) :
      (P ++ T).drop ((P ++ T).length - n) = T.drop (T.length - n) := by
    rw [List.length_append, Nat.add_sub_assoc hn, List.drop_length_add_append]
  unfold curlingNumber
  apply sup_le_sup_right
  apply Finset.sup_mono
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  obtain ⟨hk, l, hl, hlpos, hkl, hrep⟩ := hk
  have hlen : T.length ≤ (P ++ T).length := by simp
  refine ⟨by omega, l, by omega, hlpos, hkl.trans hlen, ?_⟩
  rwa [hdrop _ hkl, hdrop _ (by omega)]

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

end

end MetaMathlibExt
