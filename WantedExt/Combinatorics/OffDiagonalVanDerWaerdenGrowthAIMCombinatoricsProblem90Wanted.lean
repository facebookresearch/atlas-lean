/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The van der Waerden numbers W(3, k) are not polynomial (AIM Graph Ramsey theory, Problem 43)

AIM workshop Graph Ramsey theory, Problem 43 (section 'van der Waerden numbers'): `W(n, m)` is the
least `N` such that every red/blue colouring of `{1, …, N}` has a red `n`-term or a blue `m`-term
arithmetic progression. Under 'Off diagonal van der Waerden numbers `W(k, 3)`', with the known
bounds `k^{2-o(1)} < W(k) < e^{O(k log⁵ k)}`, the list asks: does `W(k)` grow polynomially in `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.OffDiagonalVanDerWaerdenGrowthAIMCombinatoricsProblem90Wanted

/-!
Source: AIM workshop Graph Ramsey theory, problem list, https://www.overleaf.com/read/mnvcscjjysvg,
Problem 43 (same text: AimPL, Graph Ramsey Theory, section 25, http://aimpl.org/graphramsey/1/).
UnsolvedMath record UM-20000965 (`AIM-COMBINATORICS-0090`), dataset ulamai/UnsolvedMath v1.8.0.

In that paragraph `W(k)` is the off-diagonal `W(k, 3)`: the bounds it quotes are those of `W(k, 3)`,
while the diagonal `W(k) = W(k, k)` defined earlier in the section is at least `n 2ⁿ` at `k = n + 1`
for primes `n` (Berlekamp, recorded in the same section). Swapping the colours, `W(k, 3) = W(3, k)`.
Progressions `a, a + d, …` have `a ≥ 1` and `d ≥ 1` and lie in `{1, …, N}`; red is `true`, blue is
`false`. Since containing such a progression persists when `N` grows, `W(3, k) ≤ C k^A` says exactly
that every colouring of `{1, …, C k^A}` has a red 3-term or a blue `k`-term progression, and
polynomial growth is this for some constants `C, A ∈ ℕ` and all `k ≥ 1`.
-/

/-- The colouring `c` has an arithmetic progression `a, a + d, …, a + (l - 1) d` with `a ≥ 1`,
`d ≥ 1` inside `{1, …, N}` all of whose terms have colour `b`. -/
def HasMonochromaticAP (c : ℕ → Bool) (b : Bool) (l N : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (l - 1) * d ≤ N ∧ ∀ j < l, c (a + j * d) = b

/-- The AIM question (Graph Ramsey theory, Problem 43) as a claim: the van der Waerden number
`W(3, k)` (the least `n` such that every red/blue colouring of `{1, …, n}` has a red 3-term or a
blue `k`-term arithmetic progression) grows polynomially in `k`, i.e. `W(3, k) ≤ C k^A`. -/
def offDiagonalVanDerWaerdenPolynomial : Prop :=
  ∃ C A : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ c : ℕ → Bool,
    HasMonochromaticAP c true 3 (C * k ^ A) ∨ HasMonochromaticAP c false k (C * k ^ A)

/--
Resolved false: Green proved `w(3, k) ≥ k^{b(k)}` with `b(k) = c (log k / log log k)^{1/3}`, which
tends to infinity, so `W(3, k)` is not bounded by any `C k^A` (the colours of his colouring are
swapped relative to this statement, which is symmetric). Source: AIM workshop Graph Ramsey theory,
problem list, https://www.overleaf.com/read/mnvcscjjysvg, Problem 43 (same text: AimPL, Graph Ramsey
Theory, section 25, http://aimpl.org/graphramsey/1/); resolution: B. Green, New lower bounds for van
der Waerden numbers, Forum Math. Pi 10 (2022), e18, arXiv:2102.01543, abstract and main theorem:
there is a red-blue colouring of [N] with no blue 3-term progression and no red progression of
length e^{C (log N)^{3/4} (log log N)^{1/4}}, so w(3, k) ≥ k^{b(k)} with b(k) = c (log k / log log
k)^{1/3} → ∞; Z. Hunter (arXiv:2111.01099) improved this to w(3, k) ≥ k^{c log k / log log k},
https://doi.org/10.1017/fmp.2022.12.
-/
public theorem_wanted offDiagonalVanDerWaerdenPolynomial_refuted :
    ¬ offDiagonalVanDerWaerdenPolynomial

end MathlibExt.Combinatorics.OffDiagonalVanDerWaerdenGrowthAIMCombinatoricsProblem90Wanted
