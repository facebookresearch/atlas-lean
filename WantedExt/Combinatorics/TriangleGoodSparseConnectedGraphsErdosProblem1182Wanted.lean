/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sparse connected graphs with triangle Ramsey number 2n - 1 (Erdős Problem 1182)

Erdős Problem 1182: let `f(n)` be maximal such that there is a connected graph `G` with `n`
vertices and `f(n)` edges such that `R(K₃, G) = 2n - 1`. Let `F(n)` be maximal such that every
connected graph `G` with `n` vertices and `≤ F(n)` edges has `R(K₃, G) = 2n - 1`. Estimate `f(n)`
and `F(n)`. In particular, is it true that `F(n) / n → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1182, https://www.erdosproblems.com/1182 (status
OPEN). UnsolvedMath record UM-30007223 (`EP-1182`), dataset ulamai/UnsolvedMath v1.8.0.

`R(K₃, G)` is the MathlibExt pair Ramsey number `SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin
3)) G` (least `N` such that every graph on `N` vertices contains a triangle or its complement
contains a copy of `G`). The property 'every connected `G` with `n` vertices and at most `m` edges
has `R(K₃, G) = 2n - 1`' is downward closed in `m`, so `F(n) / n → ∞` says that for every `C`, for
all large `n`, every connected graph on `n` vertices with at most `C n` edges has `R(K₃, G) = 2n -
1`; the target is stated in that form, which avoids a junk value of `F`. Only the final question
is stated: the requests to estimate `f(n)` and `F(n)` are open-ended (the page records bounds and
Brandt's expectation `2n < F(n) < 6n` for large `n`, none of them a resolved statement).
formal-conjectures has no statement of this problem.
-/

open Filter

/-- **Superlinear threshold for triangle-good graphs (Erdős Problem 1182).** The statement that for
every real number $C$, for all sufficiently large natural numbers $n$, every connected graph $G$ on
the vertex set $\{0, \dots, n - 1\}$ with at most $Cn$ edges has $R(K_3, G) = 2n - 1$. Here
$R(K_3, G)$ is the Ramsey number of the pair: the least $N$ such that every graph on $N$ vertices
contains a triangle or has a complement containing a copy of $G$.

This is the last question of Erdős Problem 1182, whether $F(n) / n \to \infty$, where $F(n)$ is the
largest $m$ such that every connected graph $G$ on $n$ vertices with at most $m$ edges has
$R(K_3, G) = 2n - 1$; since this property is downward closed in $m$, the two forms agree. -/
def triangleGoodnessSuperlinearThreshold : Prop :=
  ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.Connected →
    (G.edgeSet.ncard : ℝ) ≤ C * n →
    SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin 3)) G = 2 * n - 1

/-- **No superlinear threshold for triangle-good graphs (Erdős Problem 1182).** It is not true
that for every real number $C$, for all sufficiently large natural numbers $n$, every connected
graph $G$ on the vertex set $\{0, \dots, n - 1\}$ with at most $Cn$ edges has
$R(K_3, G) = 2n - 1$. Equivalently, there is a real number $C$ such that for infinitely many $n$
some connected graph $G$ on $\{0, \dots, n - 1\}$ with at most $Cn$ edges has
$R(K_3, G) \ne 2n - 1$. Here $R(K_3, G)$ is the Ramsey number of the pair: the least $N$ such
that every graph on $N$ vertices contains a triangle or has a complement containing a copy of
$G$, and $0$ if there is no such $N$.

Brandt proved $F(n) \le 84n$, where $F(n)$ is the largest $m$ such that every connected graph on
$n$ vertices with at most $m$ edges has $R(K_3, G) = 2n - 1$. So for all large $n$ some connected
graph on $n$ vertices with at most $84n + 1$ edges has $R(K_3, G) \ne 2n - 1$, and the statement
fails for $C = 85$. Brandt's 1996 preprint is unrefereed; erdosproblems.com/1182 accepts it.

Source: T. F. Bloom, Erdős Problems, Problem #1182,
https://www.erdosproblems.com/1182 (status OPEN); resolution: S. Brandt, Expanding graphs and
Ramsey numbers, preprint, Serie A Mathematik, Freie Universität Berlin, 1996 (unrefereed; accepted
on erdosproblems.com/1182), F(n) ≤ 84n, as recorded on erdosproblems.com/1182: 'The upper bound
was improved to F(n) ≤ 84n by Brandt ... (This resolves the final question in the negative.)',
https://ftp.math.fu-berlin.de/pub/math/publ/pre/1996/pr-a-96-24.ps.
-/
public theorem_wanted triangleGoodnessSuperlinearThreshold_refuted :
    ¬ triangleGoodnessSuperlinearThreshold

end MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182Wanted
