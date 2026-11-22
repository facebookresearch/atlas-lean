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

/-- **Value of a finite continued fraction.** For a finite list $a_0, a_1, \dots, a_t$ of integers
(possibly zero or negative), the value $[a_0; a_1, \dots, a_t]$ is the rational number
$a_0 + 1/(a_1 + 1/(\cdots + 1/a_t))$, computed from the right: the empty list has value $0$, and
the list $a_0, a_1, \dots, a_t$ has value $a_0 + v^{-1}$, where $v$ is the value of the list
$a_1, \dots, a_t$. In particular $[a] = a + 0^{-1} = a$; here and at any vanishing intermediate
denominator, $0^{-1}$ is taken to be $0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public def finiteContFrac (l : List ℤ) : ℚ :=
  l.foldr (fun (a : ℤ) (x : ℚ) => (a : ℚ) + x⁻¹) 0

/-- **Recursion for finite continued fractions.** For every integer $a$ and all integers
$l_1, \dots, l_n$ with $n \ge 0$, $[a; l_1, \dots, l_n] = a + [l_1; l_2, \dots, l_n]^{-1}$, where
the empty continued fraction (the case $n = 0$) has value $0$ and $0^{-1}$ is taken to be $0$
whenever $[l_1; l_2, \dots, l_n] = 0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_cons (a : ℤ) (l : List ℤ) :
    finiteContFrac (a :: l) = a + (finiteContFrac l)⁻¹ := rfl

/-- **Continued fraction of length one.** For every integer $a$, the finite continued fraction
$[a]$ has value $a$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_singleton (a : ℤ) : finiteContFrac [a] = a := by
  simp [finiteContFrac]

/-- **The continued fraction $[1; 2, 2]$.** The finite continued fraction $[1; 2, 2]$ has value
$7/5$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_one_two_two : finiteContFrac [1, 2, 2] = 7 / 5 := by
  norm_num [finiteContFrac]

/-- **Folding lemma for finite continued fractions.** Let $a_0$ be an integer, let $t$ be even
and let $a_1, \dots, a_t$ be integers with $a_i \ge 1$ for every $i$, and let $q$ be the
denominator in lowest terms of the value $[a_0; a_1, \dots, a_t]$ of the finite continued
fraction. Then for every integer $x \ge 1$,
$[a_0; a_1, \dots, a_t] + 1/(x q^2) = [a_0; a_1, \dots, a_t, x, -a_t, \dots, -a_1]$.

For positive partial quotients, $q$ is the continuant $q_t$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:fold`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_add_inv_mul_den_sq (a₀ : ℤ) (a : List ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ht : Even a.length) (x : ℕ) (hx : 1 ≤ x) :
    finiteContFrac (a₀ :: a) + 1 / (x * ((finiteContFrac (a₀ :: a)).den : ℚ) ^ 2) =
      finiteContFrac (a₀ :: a ++ (x : ℤ) :: (a.map (fun b => -b)).reverse)

/-- **A zero partial quotient merges its neighbours.** For all integers $a$ and $b$ and all finite
lists of integers $u_1, \dots, u_m$ and $v_1, \dots, v_n$ ($m, n \ge 0$), the finite continued
fractions satisfy $[u_1, \dots, u_m, a, 0, b, v_1, \dots, v_n] =
[u_1, \dots, u_m, a + b, v_1, \dots, v_n]$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normzero`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_zero_merge (l s : List ℤ) (a b : ℤ) :
    finiteContFrac (l ++ a :: 0 :: b :: s) = finiteContFrac (l ++ (a + b) :: s)

/-- **Normalizing a negated block.** Let $x \ge 0$ be an integer, let $t \ge 2$ and let
$a_1, \dots, a_t$ be integers with $a_i \ge 1$ for every $i$. Then for every finite list of
integers $b_1, \dots, b_m$ ($m \ge 0$), the finite continued fractions satisfy
$[b_1, \dots, b_m, x, -a_t, -a_{t-1}, \dots, -a_1] =
[b_1, \dots, b_m, x - 1, 1, a_t - 1, a_{t-1}, \dots, a_1]$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normnegblock`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_neg_block (l : List ℤ) (x : ℕ) (a : List ℤ) (aₜ : ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ha_ne : a ≠ []) (haₜ : 1 ≤ aₜ) :
    finiteContFrac (l ++ (x : ℤ) :: -aₜ :: (a.map (fun b => -b)).reverse) =
      finiteContFrac (l ++ ((x : ℤ) - 1) :: 1 :: (aₜ - 1) :: a.reverse)

/-- **Terms of the paperfolding sums.** For a sequence $x = (x_k)_{k \ge 0}$ of natural numbers,
the real numbers $s_k$ are defined by $s_0 = 1$ and $s_{k+1} = s_k^2 / x_k$, where the quotient is
read as $0$ when $x_k = 0$. They are the terms of the sums $S = \sum_k s_k$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public noncomputable def paperfoldingSumTerm (x : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => paperfoldingSumTerm x k ^ 2 / x k

/-- **First term of the paperfolding sums.** For every sequence $x$ of natural numbers, the term
$s_0$ of the paperfolding sum terms defined by $x$ equals $1$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_zero (x : ℕ → ℕ) : paperfoldingSumTerm x 0 = 1 := rfl

/-- **Recursion for the paperfolding sum terms.** For every sequence $x$ of natural numbers and
every $k \in \mathbb{N}$, the paperfolding sum terms defined by $x$ satisfy
$s_{k+1} = s_k^2 / x_k$, where the quotient is read as $0$ when $x_k = 0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_succ (x : ℕ → ℕ) (k : ℕ) :
    paperfoldingSumTerm x (k + 1) = paperfoldingSumTerm x k ^ 2 / x k := rfl

/-- **Second term of the paperfolding sums.** For every sequence $x$ of natural numbers with
$x_0 = 2$, the term $s_1$ of the paperfolding sum terms defined by $x$ equals $1/2$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Section 5, equation (`eq:sumform`). -/
public theorem paperfoldingSumTerm_one (x : ℕ → ℕ) (hx0 : x 0 = 2) :
    paperfoldingSumTerm x 1 = 1 / 2 := by
  simp [paperfoldingSumTerm, hx0]

/-- **Interleaving creases into a Cloitre word.** Given a sequence $c : \mathbb{N} \to \mathbb{N}$
and a start index $j$, the crease interleaving of a finite word $w$ of natural numbers reads $w$
from left to right as letters $(2)$ and $(1, 1)$ and inserts $c_j, c_{j+1}, c_{j+2}, \dots$ after
the successive letters. Precisely, the empty word gives the empty word; a word $2, w'$ gives
$2, c_j$ followed by the interleaving of $w'$ from index $j + 1$; a word $1, 1, w'$ gives
$1, 1, c_j$ followed by the interleaving of $w'$ from index $j + 1$; and any other nonempty word
$a, w'$ gives $a$ followed by the interleaving of $w'$ from the same index $j$.

The last case is unreachable on the approximants $A_k$ of Cloitre's sequence.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14 (Cloitre's sequence occurs
one `[1, 1]` or `[2]` at a time, interleaved with crease terms). -/
public def cloitreCreaseInterleave (c : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | j, 2 :: l => 2 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, 1 :: 1 :: l => 1 :: 1 :: c j :: cloitreCreaseInterleave c (j + 1) l
  | j, a :: l => a :: cloitreCreaseInterleave c j l

/-- **Crease interleaving of the Cloitre approximant $A_2$.** For every sequence
$c : \mathbb{N} \to \mathbb{N}$, the crease interleaving by $c$, from start index $1$, of the
approximant $A_2 = (1, 1, 2, 1, 1, 1, 1)$ of Cloitre's sequence is
$(1, 1, c_1, 2, c_2, 1, 1, c_3, 1, 1, c_4)$: each of the four letters $(1, 1)$, $(2)$, $(1, 1)$,
$(1, 1)$ of $A_2$ is followed by its crease $c_1$, $c_2$, $c_3$, $c_4$ in turn.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14. -/
public theorem cloitreCreaseInterleave_cloitreApprox_two (c : ℕ → ℕ) :
    cloitreCreaseInterleave c 1 (cloitreApprox 2) =
      [1, 1, c 1, 2, c 2, 1, 1, c 3, 1, 1, c 4] := rfl

/-- **Continued-fraction words of the paperfolding sums.** For a sequence $x = (x_k)_{k \ge 0}$ of
natural numbers, the finite words $A_k$ of natural numbers are defined by $A_0 = (1, 1)$ and
$A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$: the concatenation of $A_k$, the single letter
$\max(x_{k+1} - 1, 0)$ and the mirror image $A_k^r$ of $A_k$. The mirror image of a word reverses
it and then replaces a leading $2$ by $1, 1$, or two leading letters $1, 1$ by $2$, leaving any
other word unchanged.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public def paperfoldingContFracWord (x : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [1, 1]
  | k + 1 => paperfoldingContFracWord x k ++
      (x (k + 1) - 1) :: cloitreMirror (paperfoldingContFracWord x k)

/-- **The second paperfolding continued-fraction word.** For every sequence $x$ of natural numbers,
the continued-fraction word $A_1$ defined by $x$ is $(1, 1, \max(x_1 - 1, 0), 2)$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15. -/
public theorem paperfoldingContFracWord_one (x : ℕ → ℕ) :
    paperfoldingContFracWord x 1 = [1, 1, x 1 - 1, 2] := rfl

/-- **The paperfolding continued-fraction word $A_2$ for constant $x_k = 6$.** Let $x_k = 6$
for every $k$, and let $A_0 = (1, 1)$ and $A_{k+1} = A_k\,(x_{k+1} - 1)\,A_k^r$, where the
mirror image $A^r$ of a word $A$ is obtained by reversing $A$ and then replacing a leading $2$
by $1, 1$, or two leading letters $1, 1$ by $2$, leaving any other word unchanged. Then
$A_2 = (1, 1, 5, 2, 5, 1, 1, 5, 1, 1)$.

This is the start of the paper's expansion of $6 \sum_{k \ge 0} 12^{-2^k}$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15 and Section 6. -/
public theorem paperfoldingContFracWord_const_six_two :
    paperfoldingContFracWord (fun _ => 6) 2 = [1, 1, 5, 2, 5, 1, 1, 5, 1, 1] := rfl

/-- **Continued fraction of a paperfolding sum in Cloitre and ruler order.** Let
$x = (x_k)_{k \ge 0}$ be natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be
the paperfolding sum terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued
fraction expansion $[a_0; a_1, a_2, \ldots]$. For $j \ge 1$ let $c_j = x_{\nu_2(j) + 1} - 1$, where
$\nu_2(j)$ is the exponent of $2$ in $j$. Then $a_0 = 1$, and for every $k$ the partial quotients
$a_1, a_2, \ldots$ begin with the word obtained from the $k$-th approximant $A_k$ of Cloitre's
sequence by splitting $A_k$ from the left into letters $1, 1$ and $2$ and inserting $c_j$ after
its $j$-th letter, for every $j$.

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

/-- **Continued fraction of a paperfolding sum via the words $A_k$.** Let $x = (x_k)_{k \ge 0}$ be
natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be the paperfolding sum
terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued fraction expansion
$[a_0; a_1, a_2, \ldots]$. Let $A_k$ be the continued-fraction words defined by $x$, so that
$A_0 = (1, 1)$ and $A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$, where the mirror image $A^r$ of a
word $A$ is obtained by reversing $A$ and then replacing a leading $2$ by $1, 1$, or two leading
letters $1, 1$ by $2$, leaving any other word unchanged. Then $a_0 = 1$, and for every $k$ the
partial quotients $a_1, a_2, \ldots$ begin with the word $A_k$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15
(`jis-2026-26.3.6-cor-15`). -/
public theorem_wanted paperfoldingSum_contFrac_recursion (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (paperfoldingContFracWord x k).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((paperfoldingContFracWord x k)[i] : ℝ)

/-- **Digit frequencies in Cloitre's approximants.** Let $A_k$ be the $k$-th approximant of
Cloitre's sequence. As $k \to \infty$, the proportion of entries of $A_k$ equal to $1$ tends to
$2/3$, and the proportion of entries equal to $2$ tends to $1/3$.

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
