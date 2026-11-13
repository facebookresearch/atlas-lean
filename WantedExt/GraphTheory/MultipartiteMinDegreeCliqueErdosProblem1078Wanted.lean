/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cliques in balanced multipartite graphs of large minimum degree (Erdős Problem 1078)

Erdős Problem 1078 (Bollobás, Erdős and Szemerédi): let `G` be an `r`-partite graph with `n`
vertices in each part. If `G` has minimum degree `≥ (r - 3/2 - o(1)) n` then `G` must contain a
`K_r`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.MultipartiteMinDegreeCliqueErdosProblem1078Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1078, https://www.erdosproblems.com/1078 (status
PROVED). UnsolvedMath record UM-30007155 (`EP-1078`), dataset ulamai/UnsolvedMath v1.8.0.

The vertex set is `Fin r × Fin n` with no edges inside a part, `r ≥ 2` and `n ≥ 1` (for `n = 0` the
hypothesis is vacuous and there is no clique). Partial scope: the `o(1)` slack is taken to be `0`,
which is Haxell's theorem, the resolution recorded on the page. A positive slack tending to `0`, as
given by the sharp threshold `(r - 1) n - ⌈s n / (2s - 1)⌉`, `s = ⌊r / 2⌋`, of Haxell and Szabó, is
not formalized.
-/

/-- Erdős Problem 1078 (Bollobás, Erdős and Szemerédi), in the form proved by Haxell: an `r`-partite
graph with `n ≥ 1` vertices in each part (vertex set `Fin r × Fin n`, no edges inside a part) and
minimum degree at least `(r - 3/2) n` contains a `K_r`. -/
def multipartiteMinDegreeClique : Prop :=
  ∀ r n : ℕ, 2 ≤ r → 0 < n → ∀ G : SimpleGraph (Fin r × Fin n),
    (∀ x y, G.Adj x y → x.1 ≠ y.1) →
    (∀ v, ((r : ℝ) - 3 / 2) * n ≤ (G.neighborSet v).ncard) →
    ¬ G.CliqueFree r

/--
Resolved true: erdosproblems.com/1078 records Haxell's proof. Haxell's theorem gives an independent
transversal in any graph whose vertex classes have size at least twice its maximum degree; the
`r`-partite complement of `G` has maximum degree at most `n / 2`, and an independent transversal of
it is a `K_r` of `G`. Source: T. F. Bloom, Erdős Problems, Problem #1078,
https://www.erdosproblems.com/1078 (status PROVED); resolution: P. E. Haxell, A note on vertex list
colouring, Combin. Probab. Comput. (2001), 345-347, every graph of maximum degree Δ whose vertex set
is partitioned into classes of size ≥ 2Δ has an independent transversal; applied to the r-partite
complement of G, whose degrees are at most n/2 (erdosproblems.com/1078),
https://www.erdosproblems.com/1078.
-/
public theorem_wanted multipartiteMinDegreeClique_holds : multipartiteMinDegreeClique

end MathlibExt.GraphTheory.MultipartiteMinDegreeCliqueErdosProblem1078Wanted
