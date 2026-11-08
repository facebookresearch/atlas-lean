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

/-- The curling number `𝒞(S)`: the largest `k` such that `S = X Y^k` for strings `X`, `Y` with
`Y` nonempty, with `𝒞(ε) = 1`. Here `Y` is the suffix of `S` of length `l`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number) and Section 1.2 (`𝒞(ε) := 1`). -/
public def curlingNumber (S : List ℕ) : ℕ :=
  ((Finset.range (S.length + 1)).filter fun k => ∃ l < S.length + 1, 1 ≤ l ∧
      k * l ≤ S.length ∧
        S.drop (S.length - k * l) = (List.replicate k (S.drop (S.length - l))).flatten).sup id ⊔ 1

/-- `𝒞(112112223) = 1` (example in Section 1).

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number examples). -/
public theorem curlingNumber_example_one : curlingNumber [1, 1, 2, 1, 1, 2, 2, 2, 3] = 1 := by
  decide

/-- `𝒞(222322232223) = 3` (example in Section 1).

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (curling number examples). -/
public theorem curlingNumber_example_three :
    curlingNumber [2, 2, 2, 3, 2, 2, 2, 3, 2, 2, 2, 3] = 3 := by
  decide

/-- `𝒞(ε) = 1`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1.2 (`𝒞(ε) := 1`). -/
public theorem curlingNumber_nil : curlingNumber [] = 1 := by
  decide

/-- The first `n` terms of the `m`th order sequence `A^{(m)}`: each new term is
`max(m, 𝒞(current prefix))` (for `m ≥ 1` this gives `A^{(m)}(1) = m`); `m = 1` is Gijswijt's
sequence.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (definition of `A^{(m)}`). -/
public def gijswijtPrefix (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => gijswijtPrefix m n ++ [max m (curlingNumber (gijswijtPrefix m n))]

/-- `A^{(m)}(k)`, the `k`th term (`k ≥ 1`) of the `m`th order sequence.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (definition of `A^{(m)}`). -/
public def gijswijtTerm (m k : ℕ) : ℕ :=
  (gijswijtPrefix m k).getLastD 0

/-- Gijswijt's sequence starts `1, 1, 2, 1, 1, 2, 2, 2, 3`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (initial terms of `A`). -/
public theorem gijswijtPrefix_one_nine :
    gijswijtPrefix 1 9 = [1, 1, 2, 1, 1, 2, 2, 2, 3] := by
  decide

/-- `A^{(2)}` starts `2, 2, 2, 3, 2, 2, 2, 3`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (initial terms of `A^{(2)}`). -/
public theorem gijswijtPrefix_two_eight :
    gijswijtPrefix 2 8 = [2, 2, 2, 3, 2, 2, 2, 3] := by
  decide

/-- The position of the first occurrence of `n` in `A^{(m)}` (`0` if `n` does not occur).

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 1 (first occurrence) and Section 3 (definition of
`t(m, n)`). -/
public noncomputable def gijswijtFirstOccurrence (m n : ℕ) : ℕ :=
  sInf {k | 1 ≤ k ∧ gijswijtTerm m k = n}

/-- The block lengths `β^{(m)}(t)`: `β(1) = 1`, and `β(t+1)` is the least `k > (m+1) β(t)` with
`A^{(m)}(k+1) = m`, so that `B_{t+1} = (B_t)^{m+1} S_t` with `S_t` the run before the next `m`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (blocks `B_t^{(m)}`, glue strings `S_t^{(m)}`, and their
lengths `β^{(m)}(t)`). -/
public noncomputable def gijswijtBlockLength (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | t + 2 => sInf {k | (m + 1) * gijswijtBlockLength m (t + 1) < k ∧ gijswijtTerm m (k + 1) = m}

/-- The block `B_t^{(m)}`, the prefix of `A^{(m)}` of length `β^{(m)}(t)`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (blocks `B_t^{(m)}`). -/
public noncomputable def gijswijtBlock (m t : ℕ) : List ℕ :=
  gijswijtPrefix m (gijswijtBlockLength m t)

/-- The glue string `S_t^{(m)}`: `B_{t+1}^{(m)}` with its first `(m+1) β^{(m)}(t)` elements removed.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (glue strings `S_t^{(m)}`). -/
public noncomputable def gijswijtGlue (m t : ℕ) : List ℕ :=
  (gijswijtBlock m (t + 1)).drop ((m + 1) * gijswijtBlockLength m t)

/-- `T_t^{(m)} = S_1^{(m)} S_2^{(m)} ⋯ S_{t-1}^{(m)}`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (strings `T_t^{(m)}`). -/
public noncomputable def gijswijtGlueConcat (m t : ℕ) : List ℕ :=
  ((List.range (t - 1)).map fun i => gijswijtGlue m (i + 1)).flatten

/-- `t(m, n)`: the index `t` such that the first `n` in `A^{(m)}` is the last element of
`B_t^{(m)}`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 3 (definition of `t(m, n)`). -/
public noncomputable def gijswijtBlockIndex (m n : ℕ) : ℕ :=
  sInf {t | 1 ≤ t ∧ gijswijtBlockLength m t = gijswijtFirstOccurrence m n}

/-- `B_{u-1}^{a_{u-1}} ⋯ B_2^{a_2} B_1^{a_1}` for exponents `a_1, …, a_{u-1}` (only `a i` with
`1 ≤ i < u` are used).

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 4, Expression (1) in Lemma 11. -/
public noncomputable def gijswijtBlockWord (m u : ℕ) (a : ℕ → ℕ) : List ℕ :=
  ((List.range (u - 1)).reverse.map fun i =>
    (List.replicate (a (i + 1)) (gijswijtBlock m (i + 1))).flatten).flatten

/-- `β^{(m)}(1) = 1`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (`B_1^{(m)} = m`). -/
public theorem gijswijtBlockLength_one (m : ℕ) : gijswijtBlockLength m 1 = 1 := rfl

/-- `B_1^{(m)} = m`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (`B_1^{(m)} = m`, Table 1). -/
public theorem gijswijtBlock_one {m : ℕ} (hm : 1 ≤ m) : gijswijtBlock m 1 = [m] := by
  simp [gijswijtBlock, gijswijtBlockLength_one, gijswijtPrefix, curlingNumber_nil,
    Nat.max_eq_left hm]

/-- `T_1^{(m)} = ε`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Section 2 (Table 1). -/
public theorem gijswijtGlueConcat_one (m : ℕ) : gijswijtGlueConcat m 1 = [] := by
  simp [gijswijtGlueConcat]

/-- The empty exponent word: `gijswijtBlockWord m 1 a = ε`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, proof of Lemma 11 (case `u = 1`). -/
public theorem gijswijtBlockWord_one (m : ℕ) (a : ℕ → ℕ) : gijswijtBlockWord m 1 a = [] := by
  simp [gijswijtBlockWord]

/-- For all `n ≥ 4`, the first occurrence of `n` in Gijswijt's sequence is at position
`2^{2^{3^{4^{⋰^{(n-2)^α}}}}}` for some real `α ∈ (n-2, n-1)`: the tower has bases
`2, 2, 3, …, n-2`, written as `2 ^ (foldr (b ↦ x ↦ b^x) α [2, …, n-2])`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Theorem 1 (`jis-2025-25.4.6-thm-1`). -/
public theorem_wanted gijswijtFirstOccurrence_tower {n : ℕ} (hn : 4 ≤ n) :
    ∃ α : ℝ, α ∈ Set.Ioo ((n : ℝ) - 2) ((n : ℝ) - 1) ∧
      (gijswijtFirstOccurrence 1 n : ℝ) =
        2 ^ (List.range' 2 (n - 3)).foldr (fun b x => (b : ℝ) ^ x) α

/-- If `T` is a suffix of `S`, then `𝒞(S) ≥ 𝒞(T)`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 3 (`jis-2025-25.4.6-lem-3`). -/
public theorem_wanted curlingNumber_le_of_suffix {S T : List ℕ} (h : T <:+ S) :
    curlingNumber T ≤ curlingNumber S

/-- For `m ≥ 1` and `t ≥ 2`, `m T_t^{(m)}` is a suffix of `B_t^{(m)}`, and this is the only
occurrence of `T_t^{(m)}` as a substring of `B_t^{(m)}`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 4 (`jis-2025-25.4.6-lem-4`). -/
public theorem_wanted gijswijtGlueConcat_suffix_block {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    m :: gijswijtGlueConcat m t <:+ gijswijtBlock m t ∧
      ∀ X Y : List ℕ, gijswijtBlock m t = X ++ gijswijtGlueConcat m t ++ Y → Y = []

/-- For `m ≥ 1`, the strings `T_t^{(m)}` (`t ≥ 1`) are exactly the prefixes of `A^{(m+1)}` with
curling number at most `m`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 5 (`jis-2025-25.4.6-lem-5`). -/
public theorem_wanted gijswijtGlueConcat_iff_prefix {m : ℕ} (hm : 1 ≤ m) (P : List ℕ) :
    (P = gijswijtPrefix (m + 1) P.length ∧ curlingNumber P ≤ m) ↔
      ∃ t, 1 ≤ t ∧ P = gijswijtGlueConcat m t

/-- For `m ≥ 1` and `t ≥ 2`, the elements `m` of `B_t^{(m)}` occur in maximal runs of exactly
`m + 1` consecutive `m`'s, each followed by an element `m + 1`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 6 (`jis-2025-25.4.6-lem-6`). -/
public theorem_wanted gijswijtBlock_runs {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) (j r : ℕ)
    (hr : 0 < r) (hrun : ∀ i, j ≤ i → i < j + r → (gijswijtBlock m t)[i]? = some m)
    (hleft : j = 0 ∨ (gijswijtBlock m t)[j - 1]? ≠ some m)
    (hright : (gijswijtBlock m t)[j + r]? ≠ some m) :
    r = m + 1 ∧ (gijswijtBlock m t)[j + r]? = some (m + 1)

/-- For `n ≥ m ≥ 1`, the first occurrence of `n` in `A^{(m)}` is the last element of a prefix
block `B_t^{(m)}` for some `t ≥ 1`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 7 (`jis-2025-25.4.6-lem-7`). -/
public theorem_wanted gijswijtFirstOccurrence_eq_blockLength {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ∃ t, 1 ≤ t ∧ gijswijtTerm m (gijswijtBlockLength m t) = n ∧
      gijswijtBlockLength m t = gijswijtFirstOccurrence m n

/-- For `m ≥ 1` and `n ≥ m + 1`, `T^{(m)}_{t(m,n)} = B^{(m+1)}_{t(m+1,n)}`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 9 (`jis-2025-25.4.6-lem-9`). -/
public theorem_wanted gijswijtGlueConcat_blockIndex {m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    gijswijtGlueConcat m (gijswijtBlockIndex m n) =
      gijswijtBlock (m + 1) (gijswijtBlockIndex (m + 1) n)

/-- For `m, u ≥ 1`, the proper prefixes `P` of `B_u^{(m+1)}` with `𝒞(P) ≤ m + 1` are exactly
the strings `B_{u-1}^{a_{u-1}} ⋯ B_1^{a_1}` (blocks of order `m + 1`) with
`a_1, …, a_{u-1} ∈ {0, …, m+1}`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 11 (`jis-2025-25.4.6-lem-11`). -/
public theorem_wanted gijswijtProperPrefix_curling_iff {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (P : List ℕ) :
    (P <+: gijswijtBlock (m + 1) u ∧ P.length < (gijswijtBlock (m + 1) u).length ∧
        curlingNumber P ≤ m + 1) ↔
      ∃ a : ℕ → ℕ, (∀ i, 1 ≤ i → i < u → a i ≤ m + 1) ∧ P = gijswijtBlockWord (m + 1) u a

/-- For `m, u ≥ 1` and `a_1, …, a_{u-1} ∈ {0, …, m+1}` with some `a_i = m + 1`, the prefix
`P = B_{u-1}^{a_{u-1}} ⋯ B_1^{a_1}` of `B_u^{(m+1)}` has `𝒞(P) = m + 1`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 12 (`jis-2025-25.4.6-lem-12`). -/
public theorem_wanted curlingNumber_blockWord_of_max {m u : ℕ} (hm : 1 ≤ m) (hu : 1 ≤ u)
    (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ i → i < u → a i ≤ m + 1)
    (hmax : ∃ i, 1 ≤ i ∧ i < u ∧ a i = m + 1) :
    curlingNumber (gijswijtBlockWord (m + 1) u a) = m + 1

/-- For `m ≥ 1`, `u ≥ 2`, and `a_1, …, a_{u-1} ∈ {0, …, m}` with `a_1 ≠ 0`, the prefix
`P = B_{u-1}^{a_{u-1}} ⋯ B_1^{a_1}` of `B_u^{(m+1)}` has `𝒞(P) ≤ m`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 13 (`jis-2025-25.4.6-lem-13`). -/
public theorem_wanted curlingNumber_blockWord_le {m u : ℕ} (hm : 1 ≤ m) (hu : 2 ≤ u)
    (a : ℕ → ℕ) (ha : ∀ i, 1 ≤ i → i < u → a i ≤ m) (ha1 : a 1 ≠ 0) :
    curlingNumber (gijswijtBlockWord (m + 1) u a) ≤ m

/-- Let `m ≥ 1` and `u ≥ 2`. (a) Each proper prefix `T_t^{(m)}` of `B_u^{(m+1)}` equals
`B_{u-1}^{a_{u-1}} ⋯ B_1^{a_1}` for some `a_1, …, a_{u-1} ∈ {0, …, m}`. (b) For all
`a_1, …, a_{u-1} ∈ {0, …, m}` with `a_1 ≠ 0`, `B_{u-1}^{a_{u-1}} ⋯ B_1^{a_1} = T_t^{(m)}` for some
proper prefix `T_t^{(m)}` of `B_u^{(m+1)}`.

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

/-- For `m ≥ 1` and `u ≥ 2`,
`τ^{(m)}(m (m+1)^{u-2}) ≤ β^{(m+1)}(u) ≤ τ^{(m)}((m+1)^{u-1} + 1)`, and the second inequality
is strict when `u = m + 3`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 17 (`jis-2025-25.4.6-lem-17`). -/
public theorem_wanted gijswijtBlockLength_estimates {m u : ℕ} (hm : 1 ≤ m) (hu : 2 ≤ u) :
    (gijswijtGlueConcat m (m * (m + 1) ^ (u - 2))).length ≤ gijswijtBlockLength (m + 1) u ∧
      gijswijtBlockLength (m + 1) u ≤ (gijswijtGlueConcat m ((m + 1) ^ (u - 1) + 1)).length ∧
      (u = m + 3 →
        gijswijtBlockLength (m + 1) u < (gijswijtGlueConcat m ((m + 1) ^ (u - 1) + 1)).length)

/-- For `m ≥ 1` and `t ≥ 2`,
`β^{(m+1)}(⌈log_{m+1} t⌉) ≤ τ^{(m)}(t) ≤ β^{(m+1)}(⌈log_{m+1} t⌉ + 2)`, with
`⌈log_{m+1} t⌉ = Nat.clog (m + 1) t`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Proposition 18 (`jis-2025-25.4.6-prop-18`). -/
public theorem_wanted gijswijtGlueConcat_length_estimates {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    gijswijtBlockLength (m + 1) (Nat.clog (m + 1) t) ≤ (gijswijtGlueConcat m t).length ∧
      (gijswijtGlueConcat m t).length ≤ gijswijtBlockLength (m + 1) (Nat.clog (m + 1) t + 2)

/-- For `m ≥ 1` and `n ≥ m + 3`,
`m (m+1)^{t(m+1,n) - 2} ≤ t(m, n) ≤ (m+1)^{t(m+1,n) - 1} + 1`, and the second inequality is
strict when `n = m + 3`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Proposition 19 (`jis-2025-25.4.6-prop-19`). -/
public theorem_wanted gijswijtBlockIndex_estimates {m n : ℕ} (hm : 1 ≤ m) (hn : m + 3 ≤ n) :
    m * (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 2) ≤ gijswijtBlockIndex m n ∧
      gijswijtBlockIndex m n ≤ (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 1) + 1 ∧
      (n = m + 3 → gijswijtBlockIndex m n < (m + 1) ^ (gijswijtBlockIndex (m + 1) n - 1) + 1)

/-- With `M_7 = 4` and `M_{k+1} = M_k (1 + 9 (k+1)^{1.59} / 2^k)` for `k ≥ 7`,
`β^{(m)}(u) / (m+1)^{u-1} < M_u` for all `m ≥ 1` and `u ≥ 7`.

Source: Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences
28 (2025), Article 25.4.6, Lemma 20 (`jis-2025-25.4.6-lem-20`). -/
public theorem_wanted gijswijtBlockLength_div_lt (M : ℕ → ℝ) (hM7 : M 7 = 4)
    (hM : ∀ k, 7 ≤ k → M (k + 1) = M k * (1 + 9 * ((k : ℝ) + 1) ^ (1.59 : ℝ) / 2 ^ k))
    {m u : ℕ} (hm : 1 ≤ m) (hu : 7 ≤ u) :
    (gijswijtBlockLength m u : ℝ) / ((m : ℝ) + 1) ^ (u - 1) < M u

end

end MetaMathlibExt
