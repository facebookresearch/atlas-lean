/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence

/-!
# The folding lemma for finite continued fractions

Lemma 13 of Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued
Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6. A finite continued
fraction `[a₀; a₁, …, aₜ]` with arbitrary integer entries is `finiteContFrac`.

Theorem 14, Corollary 15 and Theorem 17 of the same paper: the simple continued fraction of
`S = ∑ sₖ` with `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ`, `x₀ = 2`, `xₖ ≥ 2` interleaves Cloitre's
self-describing sequence (`cloitreApprox`, OEIS A157196) with the terms `xₖ - 1` in ruler order,
and the digit `1` has density `2/3` in the Cloitre stages.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The value `[a₀; a₁, …, aₜ] = a₀ + 1/(a₁ + 1/(⋯ + 1/aₜ))` of a finite continued fraction
with arbitrary (possibly zero or negative) integer entries, as a rational number. The empty
list has value `0`, so `[a] = a + 0⁻¹ = a`; a vanishing intermediate denominator evaluates
through Lean's `0⁻¹ = 0`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public def finiteContFrac (l : List ℤ) : ℚ :=
  l.foldr (fun (a : ℤ) (x : ℚ) => (a : ℚ) + x⁻¹) 0

/-- `[a₀; a₁, …] = a₀ + 1/[a₁; …]`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_cons (a : ℤ) (l : List ℤ) :
    finiteContFrac (a :: l) = a + (finiteContFrac l)⁻¹ := rfl

/-- `[a] = a`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_singleton (a : ℤ) : finiteContFrac [a] = a := by
  simp [finiteContFrac]

/-- `[1; 2, 2] = 7/5`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_one_two_two : finiteContFrac [1, 2, 2] = 7 / 5 := by
  norm_num [finiteContFrac]

/-- The folding lemma: if `p/q = [a₀; a₁, …, aₜ]` with `a₀ ∈ ℤ`, positive partial quotients
`a₁, …, aₜ` and `t` even, then for every positive integer `x`,
`p/q + 1/(x q²) = [a₀; a₁, …, aₜ, x, -aₜ, …, -a₁]`. Here `q` is the reduced denominator
(`Rat.den`), which is the continuant `qₜ` for positive partial quotients.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:fold`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_add_inv_mul_den_sq (a₀ : ℤ) (a : List ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ht : Even a.length) (x : ℕ) (hx : 1 ≤ x) :
    finiteContFrac (a₀ :: a) + 1 / (x * ((finiteContFrac (a₀ :: a)).den : ℚ) ^ 2) =
      finiteContFrac (a₀ :: a ++ (x : ℤ) :: (a.map (fun b => -b)).reverse)

/-- A zero partial quotient merges its neighbours: `[…, a, 0, b, …] = […, a + b, …]`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normzero`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_zero_merge (l s : List ℤ) (a b : ℤ) :
    finiteContFrac (l ++ a :: 0 :: b :: s) = finiteContFrac (l ++ (a + b) :: s)

/-- Normalizing a negated block: for positive integers `a₁, …, aₜ` with `t ≥ 2`,
`[…, x, -aₜ, -aₜ₋₁, …, -a₁] = […, x - 1, 1, aₜ - 1, aₜ₋₁, …, a₁]`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normnegblock`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_neg_block (l : List ℤ) (x : ℕ) (a : List ℤ) (aₜ : ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ha_ne : a ≠ []) (haₜ : 1 ≤ aₜ) :
    finiteContFrac (l ++ (x : ℤ) :: -aₜ :: (a.map (fun b => -b)).reverse) =
      finiteContFrac (l ++ ((x : ℤ) - 1) :: 1 :: (aₜ - 1) :: a.reverse)

/-- The terms `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ` of the sums `S = ∑ sₖ` in equation (`eq:sumform`).

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public noncomputable def paperfoldingSumTerm (x : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => paperfoldingSumTerm x k ^ 2 / x k

/-- `s₀ = 1`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_zero (x : ℕ → ℕ) : paperfoldingSumTerm x 0 = 1 := rfl

/-- `sₖ₊₁ = sₖ² / xₖ`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_succ (x : ℕ → ℕ) (k : ℕ) :
    paperfoldingSumTerm x (k + 1) = paperfoldingSumTerm x k ^ 2 / x k := rfl

/-- With `x₀ = 2`, `s₁ = 1/2`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_one (x : ℕ → ℕ) (hx0 : x 0 = 2) :
    paperfoldingSumTerm x 1 = 1 / 2 := by
  simp [paperfoldingSumTerm, hx0]

/-- Insert crease values into a word over the alphabet `([1, 1], [2])`: after the `j`-th letter
(counting from the start value `j`) insert `c j`. A digit that starts neither letter is copied
without a crease; that branch is unreachable on Cloitre words (`cloitreApprox k`).

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14 (Cloitre's sequence occurs
one `[1, 1]` or `[2]` at a time, interleaved with crease terms). -/
public def cloitreCreaseInterleave (c : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | j, 2 :: l => 2 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, 1 :: 1 :: l => 1 :: 1 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, a :: l => a :: cloitreCreaseInterleave c j l

/-- The first four letters `[1, 1], [2], [1, 1], [1, 1]` of Cloitre's sequence, each followed
by its crease.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14. -/
public theorem cloitreCreaseInterleave_cloitreApprox_two (c : ℕ → ℕ) :
    cloitreCreaseInterleave c 1 (cloitreApprox 2) =
      [1, 1, c 1, 2, c 2, 1, 1, c 3, 1, 1, c 4] := rfl

/-- The continued-fraction words of Corollary 15: `A₀ = [1, 1]` and
`Aₖ₊₁ = Aₖ (xₖ₊₁ - 1) Aₖ^r`, where `A^r` (`cloitreMirror`) is the mirror image with its first
letter flipped in the alphabet `([1, 1], [2])`. The mirror image of `Aₖ` starts with the last
letter of `Aₖ`, which is always a letter `[1, 1]` or `[2]`, never a crease.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public def paperfoldingContFracWord (x : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [1, 1]
  | k + 1 => paperfoldingContFracWord x k ++
      (x (k + 1) - 1) :: cloitreMirror (paperfoldingContFracWord x k)

/-- `A₁ = [1, 1, x₁ - 1, 2]`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public theorem paperfoldingContFracWord_one (x : ℕ → ℕ) :
    paperfoldingContFracWord x 1 = [1, 1, x 1 - 1, 2] := rfl

/-- For the constant creases `xₖ = 6`, `A₂ = [1, 1, 5, 2, 5, 1, 1, 5, 1, 1]`, the start of the
paper's expansion of `6 ∑ 12^(-2^k)`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15 and Section 6. -/
public theorem paperfoldingContFracWord_const_six_two :
    paperfoldingContFracWord (fun _ => 6) 2 = [1, 1, 5, 2, 5, 1, 1, 5, 1, 1] := rfl

/-- Theorem 14: for `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ` with integers `x₀ = 2` and `xₖ ≥ 2`, the simple
continued fraction of `S = ∑ sₖ` is `[1; L₁, c₁, L₂, c₂, …]`, where `L₁, L₂, …` are the letters
`[1, 1]`, `[2]` of Cloitre's self-describing sequence, one at a time, and the creases
`cⱼ = x_{ν₂(j)+1} - 1` follow the ruler order (`ν₂(j) + 1` is the ruler function A001511).
Stated as: `⌊S⌋ = 1`, and for every `k` the first partial denominators of `S` (`partDens`,
indexed from `0` for `a₁`) are the first `2ᵏ` letters of `cloitreApprox k`, each followed by
its crease.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14
(`jis-2026-26.3.6-thm-14`). -/
public theorem_wanted paperfoldingSum_contFrac_cloitre_ruler (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (cloitreCreaseInterleave (fun j => x (padicValNat 2 j + 1) - 1) 1
          (cloitreApprox k)).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((cloitreCreaseInterleave (fun j => x (padicValNat 2 j + 1) - 1) 1
            (cloitreApprox k))[i] : ℝ)

/-- Corollary 15: under the hypotheses of Theorem 14, `⌊S⌋ = 1` and the partial denominators
of `S` begin with the word `Aₖ` of the recursion `A₀ = [1, 1]`, `Aₖ₊₁ = Aₖ (xₖ₊₁ - 1) Aₖ^r`,
for every `k`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15
(`jis-2026-26.3.6-cor-15`). -/
public theorem_wanted paperfoldingSum_contFrac_recursion (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (paperfoldingContFracWord x k).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((paperfoldingContFracWord x k)[i] : ℝ)

/-- Theorem 17: in the stage words `Aₖ` (`cloitreApprox k`) of Cloitre's sequence, the
proportion of digits equal to `1` tends to `2/3` and the proportion equal to `2` tends to
`1/3`; here `L(k)` is the number of digits of `Aₖ`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17
(`jis-2026-26.3.6-thm-17`). -/
public theorem_wanted tendsto_cloitreApprox_count_div_length :
    Filter.Tendsto (fun k => ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (2 / 3)) ∧
      Filter.Tendsto (fun k => ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (1 / 3))

end

end MetaMathlibExt
