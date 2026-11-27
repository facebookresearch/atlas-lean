/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A balanced three or more-term generalization of Nicomachus' identity

Statements from Seon-Hong Kim and Kenneth B. Stolarsky,
"A Balanced Three or More-term Generalization of Nicomachus'
Identity", *INTEGERS* 26 (2026), Article A98
(<https://math.colgate.edu/~integers/aa98/aa98.pdf>).

Here `Tₘ = m(m+1)/2` is the `m`-th triangular number.  Theorem 1
gives two polynomial identities (7) and (8).  In (7) the summand of
`P_{m,o}` is `(4j + 1 + jx)·((j+1)(j-2) + j²x)`; this grouping,
ambiguous in plain-text extraction of the paper, is the one
satisfying (7) (verified by exact rational computation).
`P_{m,e}` in (8) is defined in the paper by substituting `-m - 1`
for `m` in the polynomial expansion of `P_{m,o}`; the expansion
used here is the Faulhaber expansion
`P_{m,o}(x) = Σ_p c_p(x) S_p(m)` with
`(c₀, c₁, c₂, c₃) = (-2, -9 - 2x, -3, 4 + 5x + x²)` and
`S_p(m) = Σ_{j=0}^m j^p`, which agrees with the defining sum for
natural `m` (again verified by exact rational computation).

The numbers `α_k` of Equation (12) are the continued-fraction
convergents `[1; 6, 3, …, 6, 3]` with `2k - 2` partial quotients
after the semicolon, so `α₁ = 1`; they are defined here by the
equivalent recurrence (13) from the paper,
`α_{k+1} = (15 + 7α_k)/(13 + 6α_k)`.

The integers `u_k` are the coefficients in Proposition 1: `u_k` is
the coefficient of `x^{k-1}` in
`(1 + 502x + x²)/((1 - x)(1 - 398x + x²))`, defined directly as a
formal power series coefficient over `ℚ` in
`MathlibExt.NumberTheory.NicomachusGeneralization`, together with
its closed form and its recurrence.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.NicomachusConvergents
public import MathlibExt.NumberTheory.NicomachusCubeSums

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
