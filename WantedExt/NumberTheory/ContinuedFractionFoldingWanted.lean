/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import MathlibExt.NumberTheory.ContinuedFractions.Folding
public import MathlibExt.NumberTheory.ContinuedFractions.Paperfolding
public import MathlibExt.NumberTheory.ContinuedFractionFolding

/-!
# The folding lemma for finite continued fractions

Lemma 13 of Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued
Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6. A finite continued
fraction `[a₀; a₁, …, aₜ]` with arbitrary integer entries is `finiteContFrac`.

Theorem 14, Corollary 15 and Theorem 17 of the same paper: the simple continued fraction of
`S = ∑ sₖ` with `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ`, `x₀ = 2`, `xₖ ≥ 2` interleaves Cloitre's
self-describing sequence (`cloitreApprox`, OEIS A157196) with the terms `xₖ - 1` in ruler order,
and the digit `1` has density `2/3` in the Cloitre stages (Theorem 14 and Corollary 15 are
proved in `MathlibExt.NumberTheory.ContinuedFractions.Paperfolding`, Theorem 17 in
`MathlibExt.NumberTheory.ContinuedFractionFolding`).
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
