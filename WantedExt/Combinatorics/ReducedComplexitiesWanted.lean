/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reduced complexities for sequences over finite alphabets

Statements from John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", *INTEGERS* 26 (2026), Article A34
(<https://math.colgate.edu/~integers/aa34/aa34.pdf>,
DOI 10.5281/zenodo.18714474).

Words are `List Bool` (`false` for `0`, `true` for `1`). The
reduction `red(w)` collapses each run to one letter
(`redWord`); `alternations w` counts occurrences of `01`/`10`.
The Thue-Morse sequence is MathlibExt's
`MetaMathlibExt.thueMorse` (zero-indexed) and `μ` is its
`thueMorseSubstitution` extended to words (`muWord`). The
(regular) paperfolding sequence is `paperfoldingSeq`, via the
paper's definition: writing `i + 1 = m · 2^k` with `m` odd,
the value is `0` iff `m ≡ 1 (mod 4)`. Factors are `InfiniteWord.factorSet`, `ρ^red` counts distinct reductions of
length-`n` factors and `ρ^{ab,red}` counts them up to
rearrangement, i.e. by `(length, number of 0s)` of the
reduction (`rhoRed`, `rhoAbRed` via `Set.ncard`). The paper's
`m_n`/`M_n` are `minAlt`/`maxAlt`, the extrema of alternation
counts over length-`n` factors of `t`.

Theorem 2 (the mod-8 evaluation of `ρ^red_f`) is stated for
`2 ≤ n`: at `n = 1` the value is `2`, not `4`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.InfiniteWord.Factor
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open MetaMathlibExt

/-- The paper's reduction: collapse each run of `w` to a
single letter. -/
def redWord : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      if x = y then redWord (y :: xs) else x :: redWord (y :: xs)

/-- The paper's number of alternations: occurrences of `01`
and `10`, i.e. adjacent unequal pairs. -/
def alternations (w : List Bool) : ℕ :=
  (w.zip w.tail).countP (fun p => decide (p.1 ≠ p.2))

/-- The morphism `μ` (`0 ↦ 01`, `1 ↦ 10`) extended to words. -/
def muWord (w : List Bool) : List Bool :=
  w.flatMap thueMorseSubstitution

/-- The regular paperfolding sequence (zero-indexed): with
`i + 1 = m · 2^k`, `m` odd, the value is `0` iff
`m ≡ 1 (mod 4)`. -/
def paperfoldingSeq (i : ℕ) : Bool :=
  decide ((i + 1) / 2 ^ (Nat.factorization (i + 1) 2) % 4 ≠ 1)

/-- The paper's reduced factor complexity `ρ^red_x(n)`, on
the canonical `InfiniteWord.factorSet` (factors as
`Fin n → Bool`, turned into lists by `List.ofFn`). -/
noncomputable def rhoRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((fun v => redWord (List.ofFn v)) ''
    InfiniteWord.factorSet x n)

/-- The paper's reduced abelian complexity `ρ^{ab,red}_x(n)`:
reductions counted up to rearrangement, i.e. by length and
number of `0`s. -/
noncomputable def rhoAbRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard
    ((fun v => ((redWord (List.ofFn v)).length,
      (redWord (List.ofFn v)).count false)) ''
    InfiniteWord.factorSet x n)

/-- The paper's `m_n`: minimum alternations over length-`n`
factors of the Thue-Morse word. -/
noncomputable def minAlt (n : ℕ) : ℕ :=
  sInf ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

/-- The paper's `M_n`: maximum alternations over length-`n`
factors of the Thue-Morse word. -/
noncomputable def maxAlt (n : ℕ) : ℕ :=
  sSup ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

/-- **Lemma 1**: if the nonempty word `w` contains `α`
alternations, then `μ(w)` contains `2|w| - 1 - α`
alternations.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 1. -/
theorem_wanted alternations_muWord (w : List Bool) (hw : w ≠ []) :
    (alternations (muWord w) : ℤ) =
      2 * (w.length : ℤ) - 1 - (alternations w : ℤ)

/-- **Lemma 2**: for `n ≥ 2`,
`m_{2n} = 2n - 1 - M_{n+1}`, `M_{2n} = 2n - 1 - m_n`,
`m_{2n+1} = 2n - M_{n+1}`, and `M_{2n+1} = 2n - m_{n+1}`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 2. -/
theorem_wanted minAlt_maxAlt_two_mul (n : ℕ) (hn : 2 ≤ n) :
    (minAlt (2 * n) : ℤ) = 2 * n - 1 - maxAlt (n + 1) ∧
      (maxAlt (2 * n) : ℤ) = 2 * n - 1 - minAlt n ∧
      (minAlt (2 * n + 1) : ℤ) = 2 * n - maxAlt (n + 1) ∧
      (maxAlt (2 * n + 1) : ℤ) = 2 * n - minAlt (n + 1)

/-- **Lemma 3**: for `n ≥ 1`,
`m_{4n} = 2n - 1 + m_{n+1}`, `M_{4n} = 2n + M_{n+1}`,
`m_{4n+2} = 2n + m_{n+1}`, and `M_{4n+2} = 2n + 1 + M_{n+1}`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 3. -/
theorem_wanted minAlt_maxAlt_four_mul (n : ℕ) (hn : 1 ≤ n) :
    (minAlt (4 * n) : ℤ) = 2 * n - 1 + minAlt (n + 1) ∧
      (maxAlt (4 * n) : ℤ) = 2 * n + maxAlt (n + 1) ∧
      (minAlt (4 * n + 2) : ℤ) = 2 * n + minAlt (n + 1) ∧
      (maxAlt (4 * n + 2) : ℤ) = 2 * n + 1 + maxAlt (n + 1)

/-- **Theorem 1**, odd case: for odd `n`,
`ρ^red_t(n) = ρ^red_t((n+1)/2)`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
theorem_wanted rhoRed_thueMorse_odd (n : ℕ) (hn : Odd n) :
    rhoRed thueMorse n = rhoRed thueMorse ((n + 1) / 2)

/-- **Theorem 1**, even cases: for `n = 4m` (`m ≥ 1`) or
`n = 4m + 2`, `ρ^red_t(n) = ρ^red_t(m+1) + 2`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
theorem_wanted rhoRed_thueMorse_even (m : ℕ) :
    rhoRed thueMorse (4 * (m + 1)) = rhoRed thueMorse (m + 2) + 2 ∧
      rhoRed thueMorse (4 * m + 2) = rhoRed thueMorse (m + 1) + 2

/-- **Lemma 4**: any binary word of length `2n+1` whose even
positions alternate (`a?b?a?b? ⋯` or `b?a?b?a? ⋯`, the `?`
arbitrary) has `n + 1` runs; the paper applies this to
factors of the paperfolding word.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 4. -/
theorem_wanted redWord_length_alternating_even (n : ℕ)
    (w : Fin (2 * n + 1) → Bool)
    (h : ∀ i : Fin n,
      w ⟨2 * i.val, by omega⟩ ≠ w ⟨2 * (i.val + 1), by omega⟩) :
    (redWord (List.ofFn w)).length = n + 1

/-- **Lemma 5**: `ρ^red_f(2n) = 4` for positive `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 5. -/
theorem_wanted rhoRed_paperfolding_two_mul (n : ℕ) (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (2 * n) = 4

/-- **Lemma 6**: `ρ^red_f(8n+1) = 4` for positive `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 6. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_one (n : ℕ)
    (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (8 * n + 1) = 4

/-- **Lemma 7**: `ρ^red_f(8n+3) = 6` for nonnegative `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 7. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_three (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 3) = 6

/-- **Lemma 8**: `ρ^red_f(8n+5) = 6` for nonnegative `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 8. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_five (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 5) = 6

/-- **Lemma 9**: `ρ^red_f(8n+7) = 6` for nonnegative `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 9. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_seven (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 7) = 6

/-- **Theorem 2**: for `n ≥ 2` (at `n = 1` the value is `2`),
`ρ^red_f(n) = 4` if `n ≡ 0, 1, 2, 4, 6 (mod 8)` and `6` if
`n ≡ 3, 5, 7 (mod 8)`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 2. -/
theorem_wanted rhoRed_paperfolding_mod_eight (n : ℕ) (hn : 2 ≤ n) :
    (n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 →
      rhoRed paperfoldingSeq n = 4) ∧
    (n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 →
      rhoRed paperfoldingSeq n = 6)

/-- **Theorem 3**, even case: `ρ^{ab,red}_f(n) = 3` for even
positive `n`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_even (n : ℕ) (hn : 0 < n)
    (he : Even n) :
    rhoAbRed paperfoldingSeq n = 3

/-- **Theorem 3**, case `n ≡ 1 (mod 4)`: `ρ^{ab,red}_f(n) = 4`
for `n > 1`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_mod_four_one (n : ℕ)
    (hn : 1 < n) (h : n % 4 = 1) :
    rhoAbRed paperfoldingSeq n = 4

/-- **Theorem 3**, case `n ≡ 3 (mod 4)`: `ρ^{ab,red}_f(n) = 5`.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_mod_four_three (n : ℕ)
    (h : n % 4 = 3) :
    rhoAbRed paperfoldingSeq n = 5

end MathlibExt.Combinatorics.ReducedComplexitiesWanted
