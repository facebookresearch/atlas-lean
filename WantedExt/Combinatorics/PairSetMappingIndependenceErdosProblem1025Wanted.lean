/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent sets of set mappings on pairs (Erdős Problem 1025)

Erdős Problem 1025 (Erdős and Hajnal): for `f` from the pairs of `{1, …, n}` to `{1, …, n}` with
`f(x, y) ∉ {x, y}`, call `X` independent if `f(x, y) ∉ X` for all `x, y ∈ X`. Let `g(n)` be such
that every such `f` has an independent set of size at least `g(n)`. Estimate `g(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Sym.Sym2

@[expose] public section

namespace MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1025, https://www.erdosproblems.com/1025 (status
SOLVED (LEAN)). UnsolvedMath record UM-30007132 (`EP-1025`), dataset ulamai/UnsolvedMath v1.8.0.

Pairs are unordered pairs of distinct elements (`Sym2`, diagonal values unused); `g(n)` is the
largest guaranteed size. For `n = 2` no admissible mapping exists, so every `k` qualifies and `sSup`
returns the junk value `0`; `IsTheta` at `atTop` ignores it. The estimate is stated as
`g(n) ≍ n^{1/2}` (`Asymptotics.IsTheta`): Spencer's Turán bound for `3`-graphs gives the lower
bound, and Conlon, Fox and Sudakov (Section 2, Theorem 2.1 with `k = 2`, `l = 1`) give the upper
bound. The UnsolvedMath triage note proposed `(n log n)^{1/2}`, which is only the upper bound of
Erdős and Hajnal. Compared with the formal-conjectures statement `ErdosProblems/1025.lean`
(equivalent; no code imported).
-/

/-- **Independent set of a set mapping on pairs.** Let $n$ be a natural number and let $f$ assign
to each unordered pair $\{x, y\}$ of elements of $\{0, \dots, n-1\}$ (possibly with $x = y$) an
element of $\{0, \dots, n-1\}$. A finite set $X \subseteq \{0, \dots, n-1\}$ is independent for $f$
if $f(\{x, y\}) \notin X$ for all distinct $x, y \in X$.
-/
def IsIndependentFor {n : ℕ} (f : Sym2 (Fin n) → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f s(x, y) ∉ X

/-- **Independence number of set mappings on pairs.** For a natural number $n$, $g(n)$ is the
largest $k$ such that every map $f$ from the unordered pairs $\{x, y\}$ of elements of
$\{0, \dots, n-1\}$ (possibly with $x = y$) to $\{0, \dots, n-1\}$ with
$f(\{x, y\}) \notin \{x, y\}$ for all distinct $x, y$ has an independent set of at least $k$
elements, that is, a set $X \subseteq \{0, \dots, n-1\}$ with $|X| \ge k$ and
$f(\{x, y\}) \notin X$ for all distinct $x, y \in X$. If no largest such $k$ exists, $g(n) = 0$;
this happens for $n = 2$, where no such $f$ exists. -/
noncomputable def setMappingIndependence (n : ℕ) : ℕ :=
  sSup {k | ∀ f : Sym2 (Fin n) → Fin n, (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
    ∃ X : Finset (Fin n), IsIndependentFor f X ∧ k ≤ X.card}

/-- **Statement of Erdős Problem 1025.** For a natural number $n$, let $g(n)$ be the largest $k$
such that every map $f$ from the unordered pairs of elements of $\{0, \dots, n-1\}$ to
$\{0, \dots, n-1\}$ with $f(\{x, y\}) \notin \{x, y\}$ for all distinct $x, y$ admits a set $X$
of at least $k$ elements with $f(\{x, y\}) \notin X$ for all distinct $x, y \in X$ (and
$g(n) = 0$ if no largest such $k$ exists). This is the proposition that $g(n) \asymp \sqrt{n}$ as
$n \to \infty$, that is, that there are constants $c, C > 0$ with
$c \sqrt{n} \le g(n) \le C \sqrt{n}$ for all sufficiently large $n$.

Spencer proved the lower bound and Conlon, Fox and Sudakov the upper bound. -/
def setMappingIndependenceAsymp : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (setMappingIndependence n : ℝ))
    (fun n : ℕ => Real.sqrt n)

/-- **Erdős Problem 1025 (Spencer; Conlon, Fox and Sudakov).** For a natural number $n$, let $g(n)$
be the largest $k$ such that every map $f$ from the unordered pairs of elements of
$\{0, \dots, n-1\}$ to $\{0, \dots, n-1\}$ with $f(\{x, y\}) \notin \{x, y\}$ for all distinct
$x, y$ admits a set $X$ of at least $k$ elements with $f(\{x, y\}) \notin X$ for all distinct
$x, y \in X$ (and $g(n) = 0$ if no largest such $k$ exists). Then there are constants $c, C > 0$
such that $c \sqrt{n} \le g(n) \le C \sqrt{n}$ for all sufficiently large $n$, that is,
$g(n) \asymp \sqrt{n}$ as $n \to \infty$.

Source: T. F. Bloom, Erdős Problems, Problem #1025,
https://www.erdosproblems.com/1025 (status SOLVED (LEAN)); resolution: J. Spencer, Turán's theorem
for k-graphs, Discrete Math. (1972), 183-186; D. Conlon, J. Fox and B. Sudakov, Short proofs of some
extremal results II, J. Combin. Theory Ser. B (2016), 173-196, Spencer: g(n) ≫ n^{1/2};
Conlon-Fox-Sudakov: g(n) ≪ n^{1/2} (erdosproblems.com/1025),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1025.lean#L829.
-/
public theorem_wanted setMappingIndependenceAsymp_holds : setMappingIndependenceAsymp

end MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted
