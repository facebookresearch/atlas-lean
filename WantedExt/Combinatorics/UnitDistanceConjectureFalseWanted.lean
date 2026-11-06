/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős's unit-distance conjecture is false

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.UnitDistanceConjectureFalse` — erdos_unit_distance_conjecture_false (manifest `manifests/problems/erdos_unit_distance_conjecture_false.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.UnitDistanceConjectureFalseWanted` namespace. Mathematical
statements are unchanged. Source: OpenAI, *Planar Point Sets with Many Unit Distances*, 2026. https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf . Original conjecture: P. Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53 (1946), 248-250. k-equidistant variant: P. Erdős, K. Falconer, *Some problems in combinatorial geometry*, 1997.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Combinatorics.UnitDistanceConjectureFalseWanted
namespace Combinatorics

/-!
# The Erdős unit-distance problem in the plane

For a finite set `P ⊆ ℝ²` write
`ν(P) := #{ {x, y} ⊆ P : ‖x − y‖ = 1 }` for the number of unordered
unit-distance pairs in `P`, and put `ν(n) := max_{|P| = n} ν(P)`.
Erdős's 1946 paper introduced this quantity along with the dual
distinct-distances problem.

This module sets up `unitDist P = ν(P)`. The two theorems live in
companion files:

* [`UnitDistanceUpperBound`](UnitDistanceUpperBound.lean) — the best
  known upper bound, Spencer–Szemerédi–Trotter (1984), `ν(n) = O(n^{4/3})`.

* [`UnitDistanceConjectureFalse`](UnitDistanceConjectureFalse.lean) —
  OpenAI's 2026 refutation of Erdős's conjectured upper bound
  `ν(n) ≤ n^{1 + C / log log n}`.

Neither result is in mathlib; the unit-distance problem is one of the
oldest open problems in combinatorial geometry, with the elementary
incidence bound `O(n^{4/3})` having stood since 1984 with only
constant-factor improvements.
-/

open scoped Classical

/-- **Unit distance count of a planar point set.** For a finite set $P$ of points in the Euclidean
plane $\mathbb{R}^2$, the unit distance count of $P$ is the number of unordered pairs of points of
$P$ at distance exactly $1$.

The distance is the Euclidean one, $\sqrt{(x_1 - y_1)^2 + (x_2 - y_2)^2}$ for $x = (x_1, x_2)$ and
$y = (y_1, y_2)$, not the largest coordinate difference used by the product metric on
$\mathbb{R} \times \mathbb{R}$. -/
noncomputable abbrev unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ := unitDistNum P

end Combinatorics

namespace Combinatorics

/-!
# Erdős's unit-distance conjecture is false

OpenAI, *Planar Point Sets with Many Unit Distances* (2026),
<https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf>.

In 1946 Erdős conjectured that
`ν(n) ≤ n^{1 + C / log log n}` for some absolute constant `C` and all
sufficiently large `n`. OpenAI's construction refutes this: there is an
absolute `δ > 0` and infinitely many `n` with `ν(n) ≥ n^{1+δ}`. In
particular no pair `(C, N)` of constants can make Erdős's inequality
hold for every `n ≥ N`.

## Construction sketch

The argument is a high-dimensional analogue of Erdős's classical
square-grid lower bound (which used Gaussian integers `ℤ[i]`). Replace
`ℚ(i)` by `K = L(i)` for `L` a totally real number field of growing
degree, in an infinite unramified pro-`3` tower in which a fixed set of
rational primes `q₁, …, q_t` (each `≡ 1 mod 4`) splits completely.

* **Arithmetic part.** Many split prime ideals give many norm-one
  elements `u ∈ K^×` via a class-group pigeonhole. Under every complex
  embedding `σ : K ↪ ℂ`, `σ(u)` has absolute value `1`, so `u` acts as
  a candidate unit translation in the Minkowski lattice.

* **Tower.** The Hajir–Maire class-field-theoretic construction
  (specialised to the unramified, `T`-split case) produces the
  required pro-`3` tower over a cyclic cubic base field, with Chebotarev
  choosing the split primes so that their Frobenius elements lie in the
  Frattini subgroup; Golod–Shafarevich keeps the tower infinite.

* **Geometric part.** Embedding `K` via its Minkowski map produces a
  high-dimensional lattice; cutting by a product of complex discs and
  projecting to the first complex coordinate yields a planar point set
  in which every translation by `Q^{-2} u` (with `u ∈ U`) contributes a
  unit-distance pair. A packing estimate bounds the cardinality
  uniformly in the field degree, giving `ν(P_j) ≥ |P_j|^{1+δ}` along an
  infinite subsequence.

The crucial quantitative input is that bounded root discriminants give
class numbers at most exponential in the field degree.
-/

/- **OpenAI (2026), Theorem 1.1: Erdős's unit-distance conjecture is
false.**

There is an absolute `δ > 0` and infinitely many positive integers `n`
for which some `n`-point set `P ⊆ ℝ²` has at least `n^{1+δ}`
unit-distance pairs. Concretely: for every threshold `N` there exist
`n ≥ N` and a finite `P ⊆ ℝ²` with `|P| = n` and
`n^{1+δ} ≤ unitDist P`. -/
/-- **Erdős's unit distance conjecture is false.** There is a real number $\delta > 0$ such that for
every natural number $N$ there are an integer $n \ge N$ and a set $P$ of exactly $n$ points in the
Euclidean plane $\mathbb{R}^2$ with at least $n^{1+\delta}$ unordered pairs of points of $P$ at
distance exactly $1$.

Because $C / \log \log n \to 0$ for every constant $C$, this contradicts Erdős's conjecture that
$n$ points in the plane determine at most $n^{1 + C / \log \log n}$ unit distances for some
constant $C$ and all large $n$.

Source: OpenAI, *Planar Point Sets with Many Unit Distances*, 2026. https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf . Original conjecture: P. Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53 (1946), 248-250. k-equidistant variant: P. Erdős, K. Falconer, *Some problems in combinatorial geometry*, 1997. Via leanprover/lean-eval@38361be, problem `erdos_unit_distance_conjecture_false`. -/
public theorem_wanted erdos_unit_distance_conjecture_false :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧ (n : ℝ) ^ (1 + δ) ≤ (unitDist P : ℝ)

end Combinatorics

end MathlibExt.Combinatorics.UnitDistanceConjectureFalseWanted
