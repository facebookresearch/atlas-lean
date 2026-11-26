/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to Szüsz and Volkmann's construction of normal numbers

Statements from John M. Campbell, *A Counterexample to a Purported Construction of Normal
Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4.

The paper builds an integer sequence `h₂` (OEIS A380904) whose terms grow quadratically but carry
many trailing zeros, and a differentiable increasing interpolation `f` with `⌊f(n)⌋ = h₂(n)`,
`η(f) = 2` and `η(f') = 1`, where `η(h) = lim_{x → ∞} log h(x) / log x`. Szüsz and Volkmann's
Theorem 2 would make `0.h₂(1)h₂(2)…` normal; the paper shows it is not. Normality uses
`MetaMathlibExt.NormalNumber.IsNormalInBase`.

The definitions and the other proved statements are in
`MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample`, which this module imports;
`MetaMathlibExt.tendsto_log_campbellF_div_log` is proved in
`MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexampleTendstoLogCampbellFDivLog`, which this
module also imports.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample
public import MathlibExt.NumberTheory.NormalNumber
public import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexampleTendstoLogCampbellFDivLog

namespace MetaMathlibExt

@[expose] public section

/-- **Sums of $h_1$ and the jumps of $h_2$ at powers of ten.** Let $h_1$ be Campbell's auxiliary
sequence and $h_2$ Campbell's sequence. For every integer $\ell \ge 1$,
$\sum_{i=1}^{10^{\ell+1}-1} h_1(i) = \sum_{j=0}^{\ell-1} 900 \cdot 100^j$, the number written
$9090\cdots900$ ($\ell$ blocks $90$, then $0$). Moreover, writing $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$, for every integer $\ell \ge 2$ we have
$(y_2(\ell) - y_1(\ell)) / (9 \cdot 10^{\ell-1} - 1) = 10^{\ell-1}$ and
$y_1(\ell + 1) - y_2(\ell) = 10^{2\lfloor \ell/2 \rfloor}$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2
(`jis-2026-26.3.4-lem-2`). -/
public theorem_wanted campbellH1_sum_and_y_relations :
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ i ∈ Finset.Icc 1 (10 ^ (ℓ + 1) - 1), campbellH1 i = ∑ j ∈ Finset.range ℓ, 900 * 100 ^ j) ∧
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      ((campbellH2 (10 ^ ℓ - 1) : ℚ) - campbellH2 (10 ^ (ℓ - 1))) / (9 * 10 ^ (ℓ - 1) - 1) =
          10 ^ (ℓ - 1) ∧
        (campbellH2 (10 ^ ℓ) : ℤ) - campbellH2 (10 ^ ℓ - 1) = 10 ^ (2 * (ℓ / 2))

/-- **Growth exponent of the derivative of Campbell's interpolation.** For Campbell's
interpolation $f$, $\log f'(x) / \log x \to 1$ as $x \to \infty$ over the reals; that is,
$\eta(f') = 1$, where $\eta(h) = \lim_{x \to \infty} \log h(x) / \log x$. Here $f'(x)$ is taken
to be $0$ at any point where $f$ is not differentiable, and $\log 0 = 0$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 7
(`jis-2026-26.3.4-lem-7`). -/
public theorem_wanted tendsto_log_deriv_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (deriv campbellF x) / Real.log x) Filter.atTop (nhds 1)

/-- **Campbell's concatenation of $h_2$ is not normal in base $10$.** Let $h_2$ be Campbell's
sequence and let $c_0, c_1, c_2, \ldots$ be the base-$10$ digits of $h_2(1), h_2(2), \ldots$,
each number written most significant digit first and the numbers written one after another (with
$h_2(n) = 0$ written as the single digit $0$). The real number
$\sum_{j \ge 0} c_j 10^{-(j+1)} = 0.c_0c_1c_2\ldots$ is not normal in base $10$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8
(`jis-2026-26.3.4-thm-8`). -/
public theorem_wanted not_isNormalInBase_campbellConstant :
    ¬ NormalNumber.IsNormalInBase 10 campbellConstant

end

end MetaMathlibExt
