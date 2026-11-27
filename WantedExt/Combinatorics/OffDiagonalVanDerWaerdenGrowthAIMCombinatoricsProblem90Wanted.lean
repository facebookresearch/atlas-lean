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

/-- **Monochromatic arithmetic progression.** Let $c$ be a colouring of the natural numbers with
the two colours true and false, let $b$ be a colour and let $l, N$ be natural numbers. Then $c$
has a monochromatic progression of colour $b$ and length $l$ in $\{1, \dots, N\}$ when there are
natural numbers $a \ge 1$ and $d \ge 1$ with $a + (l - 1) d \le N$, where $l - 1$ is read as $0$
when $l = 0$, such that $c(a + j d) = b$ for every $j < l$. -/
def HasMonochromaticAP (c : ℕ → Bool) (b : Bool) (l N : ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (l - 1) * d ≤ N ∧ ∀ j < l, c (a + j * d) = b

/-- **Polynomial growth of the off-diagonal van der Waerden numbers (claim).** There are natural
numbers $C$ and $A$ such that for every $k \ge 1$, every colouring of the natural numbers in red
and blue has a red $3$-term or a blue $k$-term arithmetic progression $a, a + d, \dots$ with
$a \ge 1$, $d \ge 1$ and all terms in $\{1, \dots, C k^A\}$. Equivalently, the van der Waerden
number $W(3, k)$, the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a red
$3$-term or a blue $k$-term arithmetic progression, satisfies $W(3, k) \le C k^A$ for every
$k \ge 1$.

This is the AIM question (Graph Ramsey theory, Problem 43) stated as a claim. -/
def offDiagonalVanDerWaerdenPolynomial : Prop :=
  ∃ C A : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ c : ℕ → Bool,
    HasMonochromaticAP c true 3 (C * k ^ A) ∨ HasMonochromaticAP c false k (C * k ^ A)

/-- **The off-diagonal van der Waerden numbers are not polynomially bounded.** There are no
natural numbers $C$ and $A$ such that for every $k \ge 1$, every colouring of the natural numbers
in red and blue has a red $3$-term or a blue $k$-term arithmetic progression $a, a + d, \dots$
with $a \ge 1$, $d \ge 1$ and all terms in $\{1, \dots, C k^A\}$.

Equivalently, the van der Waerden number $W(3, k)$, the least $n$ such that every red/blue
colouring of $\{1, \dots, n\}$ has a red $3$-term or a blue $k$-term arithmetic progression, is
not bounded by $C k^A$ for any constants $C$ and $A$. Green proved that for some constant $c > 0$
and all sufficiently large $k$, $W(3, k) \ge k^{b(k)}$ with
$b(k) = c (\log k / \log \log k)^{1/3}$, which tends to infinity (the colours of his colouring are
swapped relative to this statement, which is symmetric).

Source: AIM workshop Graph Ramsey theory,
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
