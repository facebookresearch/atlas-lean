/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Spencer-Szemerédi-Trotter unit-distance upper bound

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.UnitDistanceUpperBound` — unit_distance_upper_bound (manifest `manifests/problems/unit_distance_upper_bound.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.UnitDistanceUpperBoundWanted` namespace. Mathematical
statements are unchanged. Source: J. Spencer, E. Szemerédi, W. T. Trotter Jr., *Unit distances in the Euclidean plane*, in Graph Theory and Combinatorics (Cambridge 1983), Academic Press, 1984. Short crossing-number proof: L. A. Székely, *Crossing numbers and hard Erdős problems in discrete geometry*, Combin. Probab. Comput. 6 (1997). Best constant: P. Ágoston, D. Pálvölgyi, *An improved constant factor for the unit distance problem*, Studia Sci. Math. Hungar. 59 (2022).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Combinatorics.UnitDistanceUpperBoundWanted
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

/-- For a finite planar set `P ⊆ ℝ²`, `unitDist P` is the number of
unordered pairs `{x, y} ⊆ P` at Euclidean distance exactly `1`.

Points are modelled as `EuclideanSpace ℝ (Fin 2)` rather than `ℝ × ℝ`
so that `dist x y = √((x₀ - y₀)² + (x₁ - y₁)²)`; the product space
`ℝ × ℝ` carries the sup-norm and would give the wrong notion of
unit-distance pair. -/
noncomputable abbrev unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ := unitDistNum P

end Combinatorics

namespace Combinatorics

/-!
# Spencer–Szemerédi–Trotter: the unit-distance graph has `O(n^{4/3})` edges

J. Spencer, E. Szemerédi, W. T. Trotter Jr., *Unit distances in the
Euclidean plane*, in Graph Theory and Combinatorics (Cambridge 1983),
Academic Press, 1984.

The naive bound `O(n^{3/2})` comes from observing that the unit-distance
graph is `K_{2,3}`-free (two unit circles meet in at most two points) and
applying Kővári–Sós–Turán. Spencer–Szemerédi–Trotter sharpened the
exponent to `4/3` by reducing to their incidence bound for points and
lines; Székely (1997) later gave a short crossing-number proof of the
same exponent. The exponent has stood since 1984 with only
constant-factor improvements (Ágoston–Pálvölgyi, 2022).
-/

open scoped Classical

/- **Spencer–Szemerédi–Trotter (1984).** The number of unit-distance
pairs in any finite planar set is `O(n^{4/3})`: there is an absolute
constant `C > 0` such that every finite `P ⊆ ℝ²` satisfies

  `unitDist P ≤ C · |P|^{4/3}`. -/
/-- Source: J. Spencer, E. Szemerédi, W. T. Trotter Jr., *Unit distances in the Euclidean plane*, in Graph Theory and Combinatorics (Cambridge 1983), Academic Press, 1984. Short crossing-number proof: L. A. Székely, *Crossing numbers and hard Erdős problems in discrete geometry*, Combin. Probab. Comput. 6 (1997). Best constant: P. Ágoston, D. Pálvölgyi, *An improved constant factor for the unit distance problem*, Studia Sci. Math. Hungar. 59 (2022). Via leanprover/lean-eval@38361be, problem `unit_distance_upper_bound`. -/
public theorem_wanted unit_distance_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        (unitDist P : ℝ) ≤ C * (P.card : ℝ) ^ ((4 : ℝ) / 3)

end Combinatorics

end MathlibExt.Combinatorics.UnitDistanceUpperBoundWanted
