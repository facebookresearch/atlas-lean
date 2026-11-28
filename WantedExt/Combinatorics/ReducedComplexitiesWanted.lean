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
the value is `0` iff `m ≡ 1 (mod 4)`. Factors are `InfiniteWord.factorSet`,
`ρ^red` counts distinct reductions of length-`n` factors and `ρ^{ab,red}` counts them up to
rearrangement, i.e. by `(length, number of 0s)` of the
reduction (`rhoRed`, `rhoAbRed` via `Set.ncard`). The paper's
`m_n`/`M_n` are `minAlt`/`maxAlt`, the extrema of alternation
counts over length-`n` factors of `t`.

Theorem 2 (the mod-8 evaluation of `ρ^red_f`) is stated for
`2 ≤ n`: at `n = 1` the value is `2`, not `4`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.PaperfoldingReducedComplexity
public import MathlibExt.Combinatorics.ThueMorseReducedComplexity

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open MetaMathlibExt

/-- **Reduced complexity of the Thue–Morse word at odd lengths.** Let $t$ be the Thue–Morse
sequence and $\rho^{\mathrm{red}}_t$ its reduced factor complexity. For every odd natural
number $n$, $\rho^{\mathrm{red}}_t(n) = \rho^{\mathrm{red}}_t((n+1)/2)$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 1. -/
theorem_wanted rhoRed_thueMorse_odd (n : ℕ) (hn : Odd n) :
    rhoRed thueMorse n = rhoRed thueMorse ((n + 1) / 2)

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
