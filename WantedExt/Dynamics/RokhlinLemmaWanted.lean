/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rokhlin lemma

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.RokhlinLemma` — rokhlin_lemma (manifest `manifests/problems/rokhlin_lemma.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.RokhlinLemmaWanted` namespace. Mathematical
statements are unchanged. Source: V. A. Rokhlin, *A general measure-preserving transformation is not mixing*, Doklady Akademii Nauk SSSR 60 (1948), 349-351 (original Russian; English translation later); S. Kakutani, *Induced measure-preserving transformations*, Proc. Imp. Acad. Tokyo 19 (1943), 635-641 (independent discovery); S.-M. Heinemann and O. Schmitt, *Rokhlin's lemma for non-invertible maps*, Dynam. Systems Appl. 10 (2001), no. 2, 201-213. The classical form is listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.RokhlinLemmaWanted
namespace Dynamics

/-!
# Rokhlin lemma (Rokhlin 1948; independently Kakutani 1943)

§109 of Knill's *Some Fundamental Theorems in Mathematics* states the
classical automorphism form. The formal target below strengthens this by
dropping invertibility: `T` is any aperiodic measure-preserving transformation
of a standard Borel probability space. Its conclusion is phrased using forward
images: for every height `n` and every `ε > 0` there is a measurable base `B`
such that `B, T B, …, T^{n−1} B` are pairwise disjoint and their union has outer
measure at least `1 − ε`. Non-invertible versions are often phrased using
preimage towers; the forward-image conclusion here follows from that form.

Mathlib has `MeasurePreserving`, `IsProbabilityMeasure`, periodic-point
infrastructure (`Function.periodicPts`), `Set.PairwiseDisjoint`, and
`StandardBorelSpace`, but no Rokhlin lemma (`grep -ri 'rokhlin'
Mathlib/Dynamics/` finds nothing; the only `tower` hits are
`IsScalarTower`). The Challenge ships four small helper definitions
(`IsAperiodic`, `towerFloor`, `towerUnion`, `IsRokhlinTower`).

The `[StandardBorelSpace Ω]` hypothesis is essential: the
countable-cocountable σ-algebra on `ℝ` with the integer-shift map
`x ↦ x + 1` is aperiodic and measure-preserving (for the 0/1 measure
that sends countable sets to 0 and cocountable sets to 1), but admits
no nontrivial Rokhlin towers — every cocountable base intersects its
own shift, and every countable base has zero-measure tower. The
countable-cocountable σ-algebra has `MeasurableSingletonClass` but is
strictly coarser than the Borel σ-algebra of any Polish topology on
`ℝ`, hence not standard Borel.
-/

open MeasureTheory Set

/-- **Aperiodic transformation.** Let $\mu$ be a measure on a measurable space $\Omega$. A map
$T : \Omega \to \Omega$ is aperiodic with respect to $\mu$ if the set of periodic points of $T$,
the points $x$ with $T^k(x) = x$ for some $k \ge 1$, where $T^k$ is the $k$-fold iterate of $T$,
has (outer) $\mu$-measure zero. Equivalently, for $\mu$-almost every $x$, no positive iterate of
$T$ fixes $x$. -/
def IsAperiodic {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (μ : Measure Ω) : Prop :=
  μ (Function.periodicPts T) = 0

/-- **Floor of a Rokhlin tower.** For a map $T : \Omega \to \Omega$, a set
$B \subseteq \Omega$ and $k \in \mathbb{N}$, the level-$k$ floor with base $B$ is the image
$T^k(B)$ of $B$ under the $k$-fold iterate $T^k$ of $T$; the level-$0$ floor is $B$. -/
def towerFloor {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (k : ℕ) : Set Ω :=
  T^[k] '' B

/-- **Union of a Rokhlin tower.** For a map $T : \Omega \to \Omega$, a set
$B \subseteq \Omega$ and $n \in \mathbb{N}$, the union of the tower with base $B$ and height $n$
is the set $\bigcup_{k=0}^{n-1} T^k(B)$ of its floors $B, T(B), \dots, T^{n-1}(B)$, where
$T^k(B)$ is the image of $B$ under the $k$-fold iterate of $T$. It is empty when $n = 0$, and
no disjointness of the floors is required. -/
def towerUnion {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range n, towerFloor T B k

/-- **Rokhlin tower.** Let $\Omega$ be a measurable space, $T : \Omega \to \Omega$ a map and
$n \in \mathbb{N}$. A set $B \subseteq \Omega$ is the base of a Rokhlin tower of height $n$
for $T$ if $B$ is measurable and the floors $B, T(B), \dots, T^{n-1}(B)$ are pairwise
disjoint, that is, $T^i(B) \cap T^j(B) = \emptyset$ for all $i \ne j$ with $i, j < n$; here
$T^k(B)$ is the image of $B$ under the $k$-fold iterate of $T$.

Only the base is required to be measurable. For a non-invertible $T$, the floors need not be
measurable, so evaluating a measure on their union uses its outer measure. -/
def IsRokhlinTower {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Prop :=
  MeasurableSet B ∧
    (Finset.range n : Set ℕ).PairwiseDisjoint (towerFloor T B)

/- **Rokhlin lemma, not-necessarily-invertible forward-image form.** For every
aperiodic measure-preserving transformation `T` of a standard Borel probability
space `(Ω, μ)`, every height `n ≥ 1`, and every `ε > 0`, there is a measurable
base whose `n` forward-image floors `B, T B, …, T^{n−1} B` are pairwise
disjoint and whose union has outer measure at least `1 − ε`. No invertibility
assumption is made. -/
/-- **Rokhlin lemma for non-invertible maps.** Let $\Omega$ be a standard Borel space with a
probability measure $\mu$, and let $T : \Omega \to \Omega$ be a measure-preserving map that is
aperiodic with respect to $\mu$. Then for every integer $n \ge 1$ and every
$\varepsilon \in (0, \infty]$ there is a measurable set $B \subseteq \Omega$ such that the
floors $B, T(B), \dots, T^{n-1}(B)$ are pairwise disjoint, where $T^k(B)$ is the image of $B$
under the $k$-fold iterate of $T$, and their union $\bigcup_{k=0}^{n-1} T^k(B)$ has outer
$\mu$-measure at least $1 - \varepsilon$ (truncated subtraction, so the bound is $0$ when
$\varepsilon \ge 1$). No invertibility of $T$ is assumed.

Source: V. A. Rokhlin, *A general measure-preserving transformation is not mixing*, Doklady Akademii Nauk SSSR 60 (1948), 349-351 (original Russian; English translation later); S. Kakutani, *Induced measure-preserving transformations*, Proc. Imp. Acad. Tokyo 19 (1943), 635-641 (independent discovery); S.-M. Heinemann and O. Schmitt, *Rokhlin's lemma for non-invertible maps*, Dynam. Systems Appl. 10 (2001), no. 2, 201-213. The classical form is listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `rokhlin_lemma`. -/
public theorem_wanted rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (_hT : MeasurePreserving T μ μ) (_hap : IsAperiodic T μ)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε

end Dynamics

end MathlibExt.Dynamics.RokhlinLemmaWanted
