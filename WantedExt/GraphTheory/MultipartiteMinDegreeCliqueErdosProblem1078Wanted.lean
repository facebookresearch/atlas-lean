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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.MultipartiteMinDegreeCliqueErdosProblem1078Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1078, https://www.erdosproblems.com/1078 (status
PROVED). UnsolvedMath record UM-30007155 (`EP-1078`), dataset ulamai/UnsolvedMath v1.8.0.

The vertex set is `Fin r × Fin n` with no edges inside a part, `r ≥ 2` and `n ≥ 1` (for `n = 0` the
hypothesis is vacuous and there is no clique). The page records that Bollobás, Erdős and Szemerédi
proved `r - 3/2` best possible, so the `o(1)` slack tends to `0` as `r → ∞`.
`multipartiteMinDegreeCliqueWithSlack` states the problem with a positive slack `ε r → 0` below
`(r - 3/2) n`; `multipartiteMinDegreeClique` is its slack-free case, Haxell's theorem.
-/

/-- Haxell's theorem, the slack-free case of Erdős Problem 1078 (Bollobás, Erdős and Szemerédi): an
`r`-partite graph with `n ≥ 1` vertices in each part (vertex set `Fin r × Fin n`, no edges inside a
part) and minimum degree at least `(r - 3/2) n` contains a `K_r`. -/
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

/-- Erdős Problem 1078 with its `o(1)` slack (Bollobás, Erdős and Szemerédi): for some positive
`ε r` tending to `0` as `r → ∞`, every `r`-partite graph with `n ≥ 1` vertices in each part (vertex
set `Fin r × Fin n`, no edges inside a part) and minimum degree at least `(r - 3/2 - ε r) n`
contains a `K_r`. -/
def multipartiteMinDegreeCliqueWithSlack : Prop :=
  ∃ ε : ℕ → ℝ, (∀ r, 0 < ε r) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ r n : ℕ, 2 ≤ r → 0 < n → ∀ G : SimpleGraph (Fin r × Fin n),
      (∀ x y, G.Adj x y → x.1 ≠ y.1) →
      (∀ v, ((r : ℝ) - 3 / 2 - ε r) * n ≤ (G.neighborSet v).ncard) →
      ¬ G.CliqueFree r

/--
Resolved true: Haxell and Szabó determined the sharp threshold `(r - 1) n - ⌈s n / (2s - 1)⌉`,
`s = ⌊r / 2⌋`, for the minimum degree (erdosproblems.com/1078): a larger minimum degree forces a
`K_r`. Since `⌈s n / (2s - 1)⌉ ≥ n / 2 + n / (2 (2s - 1))`, the slack `ε r = 1 / (4 (2s - 1))` (for
`r ≥ 2`) works: a minimum degree of at least `(r - 3/2 - ε r) n` exceeds the threshold by at least
`n / (4 (2s - 1)) > 0`, and `ε r → 0`. Source: T. F. Bloom, Erdős Problems, Problem #1078,
https://www.erdosproblems.com/1078 (status PROVED; records the sharp threshold); resolution: P. E.
Haxell and T. Szabó, Odd independent transversals are odd, Combin. Probab. Comput. 15 (2006).
-/
public theorem_wanted multipartiteMinDegreeCliqueWithSlack_holds :
    multipartiteMinDegreeCliqueWithSlack

end MathlibExt.GraphTheory.MultipartiteMinDegreeCliqueErdosProblem1078Wanted
