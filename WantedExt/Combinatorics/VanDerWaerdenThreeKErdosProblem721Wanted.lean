/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounds for the van der Waerden numbers `W(3, k)` (Erdős Problem 721)

Erdős Problem 721: let `W(3, k)` be the van der Waerden number defined as the minimum `n` such that
in any red/blue colouring of `{1, …, n}` there exists either a red `3`-term arithmetic progression
or a blue `k`-term arithmetic progression. Give reasonable bounds for `W(3, k)`. In particular, give
any non-trivial lower bounds for `W(3, k)` and prove that `W(3, k) < exp(k^c)` for some constant `c
< 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.VanDerWaerdenThreeKErdosProblem721Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #721, https://www.erdosproblems.com/721 (status
SOLVED). UnsolvedMath record UM-30006993 (`EP-721`), dataset ulamai/UnsolvedMath v1.8.0.

Colourings are `c : ℕ → Bool` (`true` red) restricted to `{1, …, N}`; progressions have common
difference `d > 0`. Bounds on `W(3, k)` are stated through `ForcesThreeK N k` (every colouring of
`{1, …, N}` has a red `3`-term or blue `k`-term progression), which is monotone in `N`: `W(3, k) <
X` is 'some `N < X` forces' and `W(3, k) ≥ X` is 'no `N < X` forces'. The two specific challenges
are formalized (Schoen's upper bound, Green's superpolynomial lower bound); the open-ended
'reasonable bounds' is not.
-/

/-- **Monochromatic arithmetic progressions in an initial interval.** Let $c$ be a red/blue
colouring of the natural numbers, given as a map to the Booleans ($\mathrm{true}$ is red,
$\mathrm{false}$ is blue), let $b$ be a colour and let $\ell$ and $N$ be natural numbers. Then $c$
has an $\ell$-term arithmetic progression of colour $b$ inside $\{1, \dots, N\}$ if there are
natural numbers $a$ and $d > 0$ such that for every $i < \ell$ we have $1 \le a + id \le N$ and
$c(a + id) = b$. -/
def HasMonoAP (c : ℕ → Bool) (b : Bool) (ℓ N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < ℓ, 1 ≤ a + i * d ∧ a + i * d ≤ N ∧ c (a + i * d) = b

/-- **Intervals forcing the van der Waerden number $W(3, k)$.** For natural numbers $N$ and $k$,
the interval $\{1, \dots, N\}$ forces $W(3, k)$ if every red/blue colouring of the natural numbers
has, inside $\{1, \dots, N\}$, a red $3$-term arithmetic progression or a blue $k$-term arithmetic
progression (progressions have common difference $d > 0$). Equivalently $W(3, k) \le N$, where the
van der Waerden number $W(3, k)$ is the least $n$ such that every red/blue colouring of
$\{1, \dots, n\}$ has a red $3$-term or a blue $k$-term arithmetic progression. -/
def ForcesThreeK (N k : ℕ) : Prop :=
  ∀ c : ℕ → Bool, HasMonoAP c true 3 N ∨ HasMonoAP c false k N

/-- **Subexponential upper bound for $W(3, k)$ (statement).** Write $W(3, k)$ for the van der
Waerden number: the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a red
$3$-term or a blue $k$-term arithmetic progression (progressions have common difference
$d > 0$). Say that $N$ forces $W(3, k)$ if every red/blue colouring of $\{1, \dots, N\}$ has a red
$3$-term or a blue $k$-term arithmetic progression. This is the proposition that there is a real
constant $c < 1$ such that for all sufficiently large natural numbers $k$ some natural number
$N < \exp(k^c)$ forces $W(3, k)$. Equivalently, $W(3, k) < \exp(k^c)$ for all large $k$. -/
def vanDerWaerdenThreeSubexponential : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ᶠ k : ℕ in Filter.atTop,
    ∃ N : ℕ, (N : ℝ) < Real.exp ((k : ℝ) ^ c) ∧ ForcesThreeK N k

/-- **Green's superpolynomial lower bound for $W(3, k)$ (statement).** Write $W(3, k)$ for the van
der Waerden number: the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a
red $3$-term or a blue $k$-term arithmetic progression (progressions have common difference
$d > 0$). Say that $N$ forces $W(3, k)$ if every red/blue colouring of $\{1, \dots, N\}$ has a red
$3$-term or a blue $k$-term arithmetic progression. This is the proposition that there is a real
constant $c > 0$ such that for all sufficiently large natural numbers $k$, no natural number
$N < \exp\bigl(c (\log k)^{4/3} / (\log \log k)^{1/3}\bigr)$ forces $W(3, k)$. Equivalently,
$W(3, k) \ge \exp\bigl(c (\log k)^{4/3} / (\log \log k)^{1/3}\bigr)$ for all large $k$. -/
def vanDerWaerdenThreeSuperpolynomial : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop, ∀ N : ℕ,
    (N : ℝ) < Real.exp (c * Real.log k ^ ((4 : ℝ) / 3) / Real.log (Real.log k) ^ ((1 : ℝ) / 3)) →
      ¬ ForcesThreeK N k

/--
**Schoen's subexponential upper bound for $W(3, k)$.** Write $W(3, k)$ for the van der Waerden
number: the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a red $3$-term
or a blue $k$-term arithmetic progression (progressions have common difference $d > 0$). Say that
$N$ forces $W(3, k)$ if every red/blue colouring of $\{1, \dots, N\}$ has a red $3$-term or a
blue $k$-term arithmetic progression. There is a real constant $c < 1$ such that for all
sufficiently large natural numbers $k$ some natural number $N < \exp(k^c)$ forces $W(3, k)$.
Equivalently, $W(3, k) < \exp(k^c)$ for all large $k$.

Schoen proved $W(3, k) \le \exp(O(k^{1-\delta}))$ for an absolute constant $\delta > 0$, which gives
this statement; erdosproblems.com/721 records Schoen as the first to show it. The best known bound
is now $\exp(O((\log k)^9))$, via Bloom and Sisask.

Source: T.
F. Bloom, Erdős Problems, Problem #721, https://www.erdosproblems.com/721 (status SOLVED);
resolution: T. Schoen, A subexponential upper bound for van der Waerden numbers W(3, k), Electron.
J. Combin. 28 (2021), Paper 2.34; B. Green, New lower bounds for van der Waerden numbers, Forum
Math. Pi 10 (2022), e18, Schoen's abstract: N ≤ exp(O(k^{1-c})) for an absolute c > 0 whenever {1,
…, N} splits into a 3-AP-free part and a k-AP-free part; abstract of arXiv:2102.01543 (Green): w(3,
k) ≥ k^{b(k)} with b(k) = c (log k / log log k)^{1/3}; erdosproblems.com/721: both specific
challenges of Erdős have been met,
https://www.combinatorics.org/ojs/index.php/eljc/article/view/v28i2p34.
-/
public theorem_wanted vanDerWaerdenThreeSubexponential_holds : vanDerWaerdenThreeSubexponential

/--
**Green's superpolynomial lower bound for $W(3, k)$.** Write $W(3, k)$ for the van der Waerden
number: the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a red $3$-term
or a blue $k$-term arithmetic progression (progressions have common difference $d > 0$). Say that
$N$ forces $W(3, k)$ if every red/blue colouring of $\{1, \dots, N\}$ has a red $3$-term or a
blue $k$-term arithmetic progression. There is a real constant $c > 0$ such that for all
sufficiently large natural numbers $k$, no natural number
$N < \exp\bigl(c (\log k)^{4/3} / (\log \log k)^{1/3}\bigr)$ forces $W(3, k)$. Equivalently,
$W(3, k) \ge \exp\bigl(c (\log k)^{4/3} / (\log \log k)^{1/3}\bigr)$ for all large $k$.

Green's colouring has no $3$-term progression in one colour and no long progression in the other;
it disproves Graham's guess $W(3, k) \ll k^2$. Hunter improved the bound to
$\exp(c (\log k)^2 / \log \log k)$ (erdosproblems.com/721).

Source: T. F. Bloom, Erdős Problems, Problem #721,
https://www.erdosproblems.com/721 (status SOLVED); resolution: T. Schoen, A subexponential upper
bound for van der Waerden numbers W(3, k), Electron. J. Combin. 28 (2021), Paper 2.34; B. Green, New
lower bounds for van der Waerden numbers, Forum Math. Pi 10 (2022), e18, Schoen's abstract: N ≤
exp(O(k^{1-c})) for an absolute c > 0 whenever {1, …, N} splits into a 3-AP-free part and a
k-AP-free part; abstract of arXiv:2102.01543 (Green): w(3, k) ≥ k^{b(k)} with b(k) = c (log k / log
log k)^{1/3}; erdosproblems.com/721: both specific challenges of Erdős have been met,
https://www.combinatorics.org/ojs/index.php/eljc/article/view/v28i2p34.
-/
public theorem_wanted vanDerWaerdenThreeSuperpolynomial_holds : vanDerWaerdenThreeSuperpolynomial

end MathlibExt.Combinatorics.VanDerWaerdenThreeKErdosProblem721Wanted
