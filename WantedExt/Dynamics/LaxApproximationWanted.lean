/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lax's approximation theorem for toral homeomorphisms

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.LaxApproximation` — lax_approximation (manifest `manifests/problems/lax_approximation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.LaxApproximationWanted` namespace. Mathematical
statements are unchanged. Source: P. D. Lax, *Approximation of measure preserving transformations*, Comm. Pure Appl. Math. 24 (1971). Knill, *Some fundamental theorems in mathematics*, §110.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.LaxApproximationWanted
namespace Dynamics.LaxApproximation

/-!
# Lax's approximation theorem for toral homeomorphisms

`lax_approximation` (Peter Lax 1971): every volume-preserving homeomorphism of
the `d`-torus (`d ≥ 1`) can be approximated arbitrarily well, in the
`L∞`-metric `δ`, by cyclic cube exchange transformations. The trusted helpers
(`Torus`, `VolumePreservingEquiv`, `deltaDist`, `ToralDynamicalSystem`, `cube`,
`cubeShift`, `IsCyclicCubeExchange`, …) are non-holes. Mathlib has the torus,
measure-preserving maps, and Hall's marriage theorem (the combinatorial
ingredient) but not Lax's theorem, cube exchanges, or the metric `δ`.

Category-(b) candidate from §110 of the Knill survey. "Cyclic" is encoded as a
single full `nᵈ`-cycle (`σ.IsCycle ∧ σ.support = univ`), and `0 < d` is required
(for `d = 0` no non-identity cycle exists).
-/

open MeasureTheory
open scoped ENNReal

instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- **Torus.** For a natural number $d$, the $d$-dimensional torus is
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$, the product of $d$ copies of the circle
$\mathbb{R}/\mathbb{Z}$. -/
abbrev Torus (d : ℕ) : Type := Fin d → AddCircle (1 : ℝ)

/-- **Volume-preserving transformations of the torus.** Let $d$ be a natural number. A
volume-preserving transformation of the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is a
bijection $T$ of $\mathbb{T}^d$ such that $T$ and $T^{-1}$ are measurable and $T$ preserves
the volume measure. -/
structure VolumePreservingEquiv (d : ℕ) where
  toMeasurableEquiv : Torus d ≃ᵐ Torus d
  measurePreserving :
    MeasurePreserving toMeasurableEquiv (volume : Measure (Torus d)) volume


/-- **Essential-supremum distance between volume-preserving maps.** Let $d$ be a natural
number and let $T$ and $S$ be measurable, invertible, volume-preserving transformations of the
torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$. Let $\rho$ be the distance on $\mathbb{T}^d$
given by the maximum over the coordinates of the distance on the circle $\mathbb{R}/\mathbb{Z}$
(taken to be $0$ when $d = 0$). The distance $\delta(T, S) \in [0, \infty]$ is the essential
supremum, with respect to the volume measure, of the function $x \mapsto \rho(T x, S x)$.

This is Knill's metric $\delta$. -/
noncomputable def deltaDist {d : ℕ} (T S : VolumePreservingEquiv d) : ℝ≥0∞ :=
  essSup (fun x => edist (T.toMeasurableEquiv x) (S.toMeasurableEquiv x)) (volume : Measure (Torus d))

/-- **Toral dynamical system.** Let $d$ be a natural number. A toral dynamical system on the
torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is a homeomorphism of $\mathbb{T}^d$ that
preserves the volume measure. -/
structure ToralDynamicalSystem (d : ℕ) where
  toHomeomorph : Torus d ≃ₜ Torus d
  measurePreserving :
    MeasurePreserving toHomeomorph (volume : Measure (Torus d)) volume

/-- **Toral dynamical systems as volume-preserving transformations.** Let $d$ be a natural
number. A volume-preserving homeomorphism $T$ of the torus
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ is regarded as a measurable, invertible,
volume-preserving transformation of $\mathbb{T}^d$: the same map, with its inverse, viewed as
a measurable equivalence. -/
noncomputable def ToralDynamicalSystem.toVolumePreservingEquiv {d : ℕ}
    (T : ToralDynamicalSystem d) : VolumePreservingEquiv d where
  toMeasurableEquiv := T.toHomeomorph.toMeasurableEquiv
  measurePreserving := T.measurePreserving

/-- **Grid cube in the torus.** Let $n$ and $d$ be natural numbers and let
$k = (k_0, \dots, k_{d-1})$ with each $k_i \in \{0, \dots, n-1\}$. The grid cube with
index $k$ is the set of points $x$ of the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$
such that, for every $i < d$, the coordinate $x_i$ is the class modulo $1$ of some real
number $r$ with $k_i/n \le r < (k_i + 1)/n$. -/
def cube (n : ℕ) {d : ℕ} (k : Fin d → Fin n) : Set (Torus d) :=
  { x | ∀ i, ∃ r : ℝ, (k i : ℝ) / n ≤ r ∧ r < ((k i : ℝ) + 1) / n ∧
        x i = ((r : ℝ) : AddCircle (1 : ℝ)) }

/-- **Coordinate shift between grid cubes.** Let $n$ and $d$ be natural numbers, let
$\sigma$ be a permutation of the index set $\{0, \dots, n-1\}^d$, let $k$ be an index and
let $i < d$. The shift along axis $i$ determined by $\sigma$ and $k$ is the point
$(\sigma(k)_i - k_i)/n$ of the circle $\mathbb{R}/\mathbb{Z}$, that is, the class modulo $1$
of this real number.

For an index $j$, the grid cube with index $j$ is the set of points of the torus
$(\mathbb{R}/\mathbb{Z})^d$ whose $m$-th coordinate is the class of a real number in
$[j_m/n, (j_m + 1)/n)$ for every $m < d$. For $n > 0$, translating the $m$-th coordinate of
each point of the grid cube with index $k$ by the shift along axis $m$, for every $m < d$,
carries that cube onto the grid cube with index $\sigma(k)$. -/
noncomputable def cubeShift (n : ℕ) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) (i : Fin d) : AddCircle (1 : ℝ) :=
  ((((((σ k) i : ℤ) - (k i : ℤ) : ℝ) / (n : ℝ)) : ℝ) : AddCircle (1 : ℝ))

/-- **Cyclic cube exchange.** Let $n$ and $d$ be natural numbers. For an index
$k \in \{0, \dots, n-1\}^d$, the grid cube with index $k$ is the set of points of the torus
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ whose $i$-th coordinate is the class of a real
number in $[k_i/n, (k_i + 1)/n)$ for every $i < d$. A measurable, invertible,
volume-preserving transformation $T$ of $\mathbb{T}^d$ is a cyclic cube exchange with $n$
subdivisions if $n > 0$ and there is a permutation $\sigma$ of $\{0, \dots, n-1\}^d$ that is
a single cycle moving every index, such that for every index $k$, every point $x$ of the
grid cube with index $k$ and every $i < d$, we have
$(T x)_i = x_i + (\sigma(k)_i - k_i)/n$ in $\mathbb{R}/\mathbb{Z}$. Thus $T$ translates each
grid cube $k$ rigidly onto the grid cube $\sigma(k)$. -/
def IsCyclicCubeExchange {d : ℕ} (T : VolumePreservingEquiv d) (n : ℕ) : Prop :=
  0 < n ∧ ∃ σ : Equiv.Perm (Fin d → Fin n),
    σ.IsCycle ∧ σ.support = Finset.univ ∧
    ∀ k : Fin d → Fin n, ∀ x ∈ cube n k, ∀ i,
      T.toMeasurableEquiv x i = x i + cubeShift n σ k i

/- **Lax's approximation theorem.** Every toral dynamical system on `𝕋^d`
(`d ≥ 1`) is approximated arbitrarily well in the metric `δ` by cyclic cube
exchange transformations. -/
/-- **Lax's approximation theorem.** Let $d \ge 1$ be a natural number and let $T$ be a toral
dynamical system on the torus $\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$, regarded as a
measurable, invertible, volume-preserving transformation of $\mathbb{T}^d$. Then for every
$\varepsilon \in (0, \infty]$ there are a natural number $n$ and a measurable, invertible,
volume-preserving transformation $S$ of $\mathbb{T}^d$ such that $S$ is a cyclic cube exchange
with $n$ subdivisions and $\delta(T, S) < \varepsilon$, where $\delta$ is the
essential-supremum distance between volume-preserving maps.

Source: P. D. Lax, *Approximation of measure preserving transformations*, Comm. Pure Appl. Math. 24 (1971). Knill, *Some fundamental theorems in mathematics*, §110. Via leanprover/lean-eval@38361be, problem `lax_approximation`. -/
public theorem_wanted lax_approximation {d : ℕ} (hd : 0 < d) (T : ToralDynamicalSystem d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist T.toVolumePreservingEquiv S < ε

end Dynamics.LaxApproximation

end MathlibExt.Dynamics.LaxApproximationWanted
