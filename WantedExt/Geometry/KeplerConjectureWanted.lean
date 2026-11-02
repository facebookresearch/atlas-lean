/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kepler conjecture (optimal sphere packing in ℝ³)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.KeplerConjecture` — kepler_conjecture (manifest `manifests/problems/kepler_conjecture.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.KeplerConjectureWanted` namespace. Mathematical
statements are unchanged. Source: Kepler conjecture 1611 (J. Kepler, *Strena seu de Nive Sexangula*); proof T. Hales, 'A proof of the Kepler conjecture', Ann. of Math. (2) 162 (2005) 1065–1185; formal verification in HOL Light + Isabelle by the Flyspeck project (T. Hales et al., completed August 2014), Forum Math. Pi 5 (2017) e2. Wiedijk-1000 #209; listed as §96 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.KeplerConjectureWanted
namespace Geometry
namespace KeplerConjectureProblem

/-!
# Kepler conjecture (optimal sphere packing density in ℝ³)

The optimal sphere-packing density in three dimensions is `π / √18`,
achieved by the face-centred-cubic packing. Conjectured by Johannes
Kepler (1611); announced by Thomas Hales in 1998 and published as
Hales 2005; formally verified in HOL Light + Isabelle by the
*Flyspeck* project, completed August 2014.
Wiedijk-1000 #209; §96 in Knill's *Some Fundamental Theorems in
Mathematics*.

The definitions take a `Set` (rather than e.g. `Submodule ℤ`) for the
centre set because Kepler's optimal density is the supremum over *all*
unit-sphere packings, not just lattice packings.
-/

open scoped ENNReal
open MeasureTheory Filter

/-- **Euclidean space for sphere packings.** For a natural number $d$, $\mathbb{R}^d$ denotes the
$d$-dimensional real Euclidean space: $d$-tuples of real numbers with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **Unit sphere packing.** For a natural number $d$, a set $X \subseteq \mathbb{R}^d$ is the
centre set of a unit sphere packing if the open balls of radius $1$ centred at any two distinct
points of $X$ are disjoint. -/
def IsPacking {d : ℕ} (X : Set (E d)) : Prop :=
  X.Pairwise (fun x y => Disjoint (Metric.ball x 1) (Metric.ball y 1))

/-- **Covered fraction of a ball.** For a natural number $d$, a set $X \subseteq \mathbb{R}^d$ and a
real number $R$, the covered fraction of $X$ at radius $R$ is
$$\frac{\operatorname{vol}\bigl(B_R(0) \cap \bigcup_{x \in X} B_1(x)\bigr)}
{\operatorname{vol}(B_R(0))},$$
where $B_r(y)$ is the open ball of radius $r$ about $y$ and $\operatorname{vol}$ is Lebesgue
measure; it equals $0$ when $R \le 0$. -/
noncomputable def coveredFraction {d : ℕ} (X : Set (E d)) (R : ℝ) : ℝ :=
  (volume ((⋃ x ∈ X, Metric.ball x 1) ∩ Metric.ball (0 : E d) R)).toReal /
    (volume (Metric.ball (0 : E d) R)).toReal

/-- **Density of a sphere packing.** For a natural number $d$, the density of a set
$X \subseteq \mathbb{R}^d$ is the limit superior, as $R \to \infty$, of the covered fraction of $X$
at radius $R$: the fraction of the open ball of radius $R$ about the origin covered by the open
unit balls centred at points of $X$. -/
noncomputable def density {d : ℕ} (X : Set (E d)) : ℝ :=
  Filter.limsup (coveredFraction X) Filter.atTop

/-- **Optimal sphere packing density.** For a natural number $d$, $\Delta(d)$ is the supremum of
the densities of all unit sphere packings in $\mathbb{R}^d$. -/
noncomputable def Δ (d : ℕ) : ℝ :=
  sSup {δ : ℝ | ∃ X : Set (E d), IsPacking X ∧ density X = δ}

/- **Kepler conjecture** (Hales 1998, Flyspeck 2014). The optimal
sphere-packing density in three dimensions equals `π / √18`. -/
/-- **Kepler conjecture.** Let $\Delta(3)$ be the supremum of the densities of all unit sphere
packings in $\mathbb{R}^3$. Then $\Delta(3) = \pi / \sqrt{18}$.

Source: Kepler conjecture 1611 (J. Kepler, *Strena seu de Nive Sexangula*); proof T. Hales, 'A proof of the Kepler conjecture', Ann. of Math. (2) 162 (2005) 1065–1185; formal verification in HOL Light + Isabelle by the Flyspeck project (T. Hales et al., completed August 2014), Forum Math. Pi 5 (2017) e2. Wiedijk-1000 #209; listed as §96 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `kepler_conjecture`. -/
public theorem_wanted kepler_conjecture : Δ 3 = Real.pi / Real.sqrt 18

end KeplerConjectureProblem
end Geometry

end MathlibExt.Geometry.KeplerConjectureWanted
