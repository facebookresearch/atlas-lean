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
Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6, is in
`MathlibExt.NumberTheory.ContinuedFractionFolding`. A finite continued
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

end

end MetaMathlibExt
