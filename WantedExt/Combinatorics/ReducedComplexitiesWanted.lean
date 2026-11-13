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

/-- **Reduction of a binary word.** The reduction $\operatorname{red}(w)$ of a binary word $w$ is
the word obtained by collapsing each maximal run of equal consecutive letters of $w$ to a single
letter; for example $\operatorname{red}(0011101) = 0101$. -/
def redWord : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      if x = y then redWord (y :: xs) else x :: redWord (y :: xs)

/-- **Alternations of a binary word.** The number of alternations of a binary word $w$ is the
number of occurrences of the factors $01$ and $10$ in $w$, that is, the number of positions $i$
with $w_i \ne w_{i+1}$. -/
def alternations (w : List Bool) : ℕ :=
  (w.zip w.tail).countP (fun p => decide (p.1 ≠ p.2))

/-- **Extension of the Thue–Morse substitution to binary words.** The morphism $\mu$ sends each
letter to a word of length two, $\mu(0) = 01$ and $\mu(1) = 10$, and a binary word
$w_1 w_2 \cdots w_k$ to the concatenation $\mu(w_1) \mu(w_2) \cdots \mu(w_k)$. -/
def muWord (w : List Bool) : List Bool :=
  w.flatMap thueMorseSubstitution

/-- **Regular paperfolding sequence.** The regular paperfolding sequence $f = f_0 f_1 f_2 \cdots$
over $\{0, 1\}$ is indexed from $0$: for each $i$, write $i + 1 = m \cdot 2^k$ with $m$ odd; then
$f_i = 0$ if $m \equiv 1 \pmod 4$ and $f_i = 1$ if $m \equiv 3 \pmod 4$. -/
def paperfoldingSeq (i : ℕ) : Bool :=
  decide ((i + 1) / 2 ^ (Nat.factorization (i + 1) 2) % 4 ≠ 1)

/-- **Reduced factor complexity.** For a finite binary word $w$, let $\mathrm{red}(w)$ be the
word obtained from $w$ by collapsing each run of equal letters to a single letter. For an
infinite binary word $x = x_0 x_1 x_2 \cdots$ and a natural number $n$, the reduced factor
complexity $\rho^{\mathrm{red}}_x(n)$ is the number of distinct words $\mathrm{red}(w)$ as $w$
ranges over the length-$n$ factors of $x$. -/
noncomputable def rhoRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((fun v => redWord (List.ofFn v)) ''
    InfiniteWord.factorSet x n)

/-- **Reduced abelian complexity.** For a binary sequence $x = x_0 x_1 x_2 \cdots$ and
$n \in \mathbb{N}$, the reduced abelian complexity $\rho^{\mathrm{ab,red}}_x(n)$ is the number of
distinct pairs $(|\mathrm{red}(v)|, |\mathrm{red}(v)|_0)$, where $v$ ranges over the length-$n$
factors of $x$, $\mathrm{red}(v)$ is the reduction of $v$ (each run of equal letters collapsed to
a single letter) and $|w|_0$ is the number of letters $0$ in $w$. Equivalently, it counts the
reductions of length-$n$ factors of $x$ up to rearrangement of their letters. -/
noncomputable def rhoAbRed (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard
    ((fun v => ((redWord (List.ofFn v)).length,
      (redWord (List.ofFn v)).count false)) ''
    InfiniteWord.factorSet x n)

/-- **Minimum number of alternations in Thue–Morse factors.** For a natural number $n$, $m_n$ is
the least number of alternations (positions where two adjacent letters differ) among the
length-$n$ factors of the Thue–Morse sequence. -/
noncomputable def minAlt (n : ℕ) : ℕ :=
  sInf ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

/-- **Maximum number of alternations in Thue–Morse factors.** For a natural number $n$, $M_n$ is
the largest number of alternations (positions where two adjacent letters differ) among the
length-$n$ factors of the Thue–Morse sequence. -/
noncomputable def maxAlt (n : ℕ) : ℕ :=
  sSup ((fun v => alternations (List.ofFn v)) ''
    InfiniteWord.factorSet thueMorse n)

/-- **Alternations of the Thue–Morse image of a word.** Let $\mu$ be the morphism on binary words
with $\mu(0) = 01$ and $\mu(1) = 10$. If $w$ is a nonempty binary word of length $|w|$ with
$\alpha$ alternations (positions where two adjacent letters differ), then $\mu(w)$ has exactly
$2|w| - 1 - \alpha$ alternations.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 1. -/
theorem_wanted alternations_muWord (w : List Bool) (hw : w ≠ []) :
    (alternations (muWord w) : ℤ) =
      2 * (w.length : ℤ) - 1 - (alternations w : ℤ)

/-- **Doubling recurrences for Thue–Morse alternation extrema.** For a natural number $k$, let
$m_k$ and $M_k$ be the least and the largest number of alternations (positions where two adjacent
letters differ) among the length-$k$ factors of the Thue–Morse sequence. Then for every $n \ge 2$,
$m_{2n} = 2n - 1 - M_{n+1}$, $M_{2n} = 2n - 1 - m_n$, $m_{2n+1} = 2n - M_{n+1}$ and
$M_{2n+1} = 2n - m_{n+1}$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 2. -/
theorem_wanted minAlt_maxAlt_two_mul (n : ℕ) (hn : 2 ≤ n) :
    (minAlt (2 * n) : ℤ) = 2 * n - 1 - maxAlt (n + 1) ∧
      (maxAlt (2 * n) : ℤ) = 2 * n - 1 - minAlt n ∧
      (minAlt (2 * n + 1) : ℤ) = 2 * n - maxAlt (n + 1) ∧
      (maxAlt (2 * n + 1) : ℤ) = 2 * n - minAlt (n + 1)

/-- **Quadrupling recurrences for Thue–Morse alternation extrema.** For a natural number $k$, let
$m_k$ and $M_k$ be the least and the largest number of alternations (positions where two adjacent
letters differ) among the length-$k$ factors of the Thue–Morse sequence. Then for every $n \ge 1$,
$m_{4n} = 2n - 1 + m_{n+1}$, $M_{4n} = 2n + M_{n+1}$, $m_{4n+2} = 2n + m_{n+1}$ and
$M_{4n+2} = 2n + 1 + M_{n+1}$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 3. -/
theorem_wanted minAlt_maxAlt_four_mul (n : ℕ) (hn : 1 ≤ n) :
    (minAlt (4 * n) : ℤ) = 2 * n - 1 + minAlt (n + 1) ∧
      (maxAlt (4 * n) : ℤ) = 2 * n + maxAlt (n + 1) ∧
      (minAlt (4 * n + 2) : ℤ) = 2 * n + minAlt (n + 1) ∧
      (maxAlt (4 * n + 2) : ℤ) = 2 * n + 1 + maxAlt (n + 1)

/-- **Reduced complexity of the Thue–Morse word at odd lengths.** Let $t$ be the Thue–Morse
sequence and $\rho^{\mathrm{red}}_t$ its reduced factor complexity. For every odd natural
number $n$, $\rho^{\mathrm{red}}_t(n) = \rho^{\mathrm{red}}_t((n+1)/2)$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
theorem_wanted rhoRed_thueMorse_odd (n : ℕ) (hn : Odd n) :
    rhoRed thueMorse n = rhoRed thueMorse ((n + 1) / 2)

/-- **Reduced complexity of the Thue–Morse word at even lengths.** Let $t$ be the Thue–Morse
sequence and $\rho^{\mathrm{red}}_t$ its reduced factor complexity. For every natural number
$m \ge 1$, $\rho^{\mathrm{red}}_t(4m) = \rho^{\mathrm{red}}_t(m+1) + 2$, and for every natural
number $m \ge 0$, $\rho^{\mathrm{red}}_t(4m+2) = \rho^{\mathrm{red}}_t(m+1) + 2$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
theorem_wanted rhoRed_thueMorse_even (m : ℕ) :
    rhoRed thueMorse (4 * (m + 1)) = rhoRed thueMorse (m + 2) + 2 ∧
      rhoRed thueMorse (4 * m + 2) = rhoRed thueMorse (m + 1) + 2

/-- **Runs in a word whose even-position letters alternate.** Let $n$ be a natural number and let
$w = w_0 w_1 \cdots w_{2n}$ be a binary word of length $2n + 1$ with $w_{2i} \ne w_{2i+2}$ for
every $i < n$, so that its even positions read $abab\cdots$ with $a \ne b$ and its odd positions
are arbitrary. Then the reduction of $w$, the word obtained by collapsing each maximal run of
equal letters of $w$ to a single letter, has length $n + 1$; that is, $w$ has exactly $n + 1$ runs.

The paper applies this to factors of the paperfolding word.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 4. -/
theorem_wanted redWord_length_alternating_even (n : ℕ)
    (w : Fin (2 * n + 1) → Bool)
    (h : ∀ i : Fin n,
      w ⟨2 * i.val, by omega⟩ ≠ w ⟨2 * (i.val + 1), by omega⟩) :
    (redWord (List.ofFn w)).length = n + 1

/-- **Reduced complexity of the paperfolding word at even lengths.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every $n \ge 1$, $\rho^{\mathrm{red}}_f(2n) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 5. -/
theorem_wanted rhoRed_paperfolding_two_mul (n : ℕ) (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (2 * n) = 4

/-- **Reduced complexity of the paperfolding word at lengths 8n + 1.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every $n \ge 1$, $\rho^{\mathrm{red}}_f(8n+1) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 6. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_one (n : ℕ)
    (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (8 * n + 1) = 4

/-- **Reduced complexity of the paperfolding word at lengths 8n + 3.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every natural number $n$, $\rho^{\mathrm{red}}_f(8n+3) = 6$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 7. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_three (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 3) = 6

/-- **Reduced complexity of the paperfolding word at lengths 8n + 5.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every natural number $n$, $\rho^{\mathrm{red}}_f(8n+5) = 6$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 8. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_five (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 5) = 6

/-- **Reduced complexity of the paperfolding word at lengths 8n + 7.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every natural number $n$, $\rho^{\mathrm{red}}_f(8n+7) = 6$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 9. -/
theorem_wanted rhoRed_paperfolding_eight_mul_add_seven (n : ℕ) :
    rhoRed paperfoldingSeq (8 * n + 7) = 6

/-- **Reduced complexity of the paperfolding word.** Let $f$ be the regular paperfolding
sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of length-$n$
factors of $f$. For every $n \ge 2$, $\rho^{\mathrm{red}}_f(n) = 4$ if $n \equiv 0, 1, 2, 4$ or
$6 \pmod 8$, and $\rho^{\mathrm{red}}_f(n) = 6$ if $n \equiv 3, 5$ or $7 \pmod 8$.

The bound $n \ge 2$ is needed: $\rho^{\mathrm{red}}_f(1) = 2$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 2. -/
theorem_wanted rhoRed_paperfolding_mod_eight (n : ℕ) (hn : 2 ≤ n) :
    (n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 →
      rhoRed paperfoldingSeq n = 4) ∧
    (n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 →
      rhoRed paperfoldingSeq n = 6)

/-- **Reduced abelian complexity of the paperfolding word at even lengths.** Let $f$ be the
regular paperfolding sequence and let $\rho^{\mathrm{ab,red}}_f(n)$ be the number of reductions
of length-$n$ factors of $f$, counted up to rearrangement of their letters. For every even
$n > 0$, $\rho^{\mathrm{ab,red}}_f(n) = 3$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_even (n : ℕ) (hn : 0 < n)
    (he : Even n) :
    rhoAbRed paperfoldingSeq n = 3

/-- **Reduced abelian complexity of the paperfolding word at lengths 1 mod 4.** Let $f$ be the
regular paperfolding sequence and let $\rho^{\mathrm{ab,red}}_f(n)$ be the number of reductions
of length-$n$ factors of $f$, counted up to rearrangement of their letters. For every $n > 1$
with $n \equiv 1 \pmod 4$, $\rho^{\mathrm{ab,red}}_f(n) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_mod_four_one (n : ℕ)
    (hn : 1 < n) (h : n % 4 = 1) :
    rhoAbRed paperfoldingSeq n = 4

/-- **Reduced abelian complexity of the paperfolding word at lengths 3 mod 4.** Let $f$ be the
regular paperfolding sequence and let $\rho^{\mathrm{ab,red}}_f(n)$ be the number of reductions
of length-$n$ factors of $f$, counted up to rearrangement of their letters. For every natural
number $n \equiv 3 \pmod 4$, $\rho^{\mathrm{ab,red}}_f(n) = 5$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
theorem_wanted rhoAbRed_paperfolding_mod_four_three (n : ℕ)
    (h : n % 4 = 3) :
    rhoAbRed paperfoldingSeq n = 5

end MathlibExt.Combinatorics.ReducedComplexitiesWanted
