/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ornstein–Weiss ℤᵈ Rokhlin lemma

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.OrnsteinWeiss` — ornstein_weiss_rokhlin (manifest `manifests/problems/ornstein_weiss_rokhlin.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.OrnsteinWeissWanted` namespace. Mathematical
statements are unchanged. Source: D. S. Ornstein and B. Weiss, *Entropy and isomorphism theorems for actions of amenable groups*, J. Anal. Math. 48 (1987), 1-141 — Theorem 5.2 establishes the multidimensional (and amenable-group) Rokhlin lemma. Listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). No formalization found in any major prover.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.OrnsteinWeissWanted
namespace Dynamics

/-!
# Ornstein–Weiss `ℤᵈ` Rokhlin lemma (Ornstein–Weiss, 1987)

§109 of Knill's *Some Fundamental Theorems in Mathematics* (additional
statement). The multidimensional Rokhlin lemma: for every free
measure-preserving `ℤᵈ`-action `T` on a standard Borel probability
space, every box size `N ≥ 1`, and every `ε > 0`, there is a measurable
base `B` such that the translates `T v '' B` for `v ∈ [0, N)ᵈ` are
pairwise disjoint and their union has measure at least `1 − ε`.

Mathlib has `MeasurePreserving`, `IsProbabilityMeasure`,
`Set.PairwiseDisjoint`, `Fintype.piFinset`, `Finset.Ico`, and
`StandardBorelSpace`, but **no Ornstein–Weiss lemma**, no free
measure-preserving `ℤᵈ`-actions, no multidimensional Rokhlin towers.
The Challenge ships two small helper definitions (`IsFreeAction` and
`boxShape`).

Three hypotheses beyond the classical Rokhlin lemma:

* `1 ≤ d` rules out the degenerate `d = 0` case.
* The identity axiom `T 0 = id` is imposed explicitly; the homomorphism
  axiom alone only forces `T 0` to be idempotent. Together with the
  homomorphism axiom this also gives bijectivity of each `T v` via
  `T (-v) ∘ T v = T 0 = id`.
* `[StandardBorelSpace Ω]` rules out the countable-cocountable
  σ-algebra defect (see the §109 Rokhlin lemma PR for the
  one-dimensional version of this counterexample).
-/

open MeasureTheory Set

/-- **Free $\mathbb{Z}^d$-action.** Let $d$ be a natural number, let $\mu$ be a measure on a
measurable space $\Omega$, and let $T$ assign to each $v \in \mathbb{Z}^d$ a map
$T_v \colon \Omega \to \Omega$. Then $T$ is free (in the Ornstein–Weiss sense) with respect to
$\mu$ if, for every nonzero $v \in \mathbb{Z}^d$, the set of points $x \in \Omega$ with
$T_v(x) = x$ has $\mu$-measure zero. -/
def IsFreeAction {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (T : (Fin d → ℤ) → Ω → Ω) : Prop :=
  ∀ v : Fin d → ℤ, v ≠ 0 → μ {x | T v x = x} = 0

/-- **Integer box.** For natural numbers $d$ and $N$, the integer box $[0, N)^d$ is the finite set
of vectors $v \in \mathbb{Z}^d$ with $0 \le v_i < N$ for every coordinate $i$. -/
noncomputable def boxShape (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (N : ℤ))

/- **Ornstein–Weiss `ℤᵈ` Rokhlin lemma.** For every free
measure-preserving `ℤᵈ`-action `T` on a standard Borel probability
space (with `d ≥ 1`, identity axiom `T 0 = id`, and the homomorphism
axiom), every box size `N ≥ 1`, and every `ε > 0`, there is a
measurable base `B` such that the translates `T v '' B` for
`v ∈ [0, N)ᵈ` are pairwise disjoint and their union has measure at
least `1 − ε`. -/
/-- **Ornstein–Weiss Rokhlin lemma for $\mathbb{Z}^d$-actions.** Let $d \ge 1$, let $\Omega$ be a
standard Borel space with a probability measure $\mu$, and let $T$ assign to each
$v \in \mathbb{Z}^d$ a map $T_v \colon \Omega \to \Omega$ such that $T_0$ is the identity,
$T_{u + v} = T_u \circ T_v$ for all $u, v \in \mathbb{Z}^d$, every $T_v$ is measure preserving
for $\mu$, and the action is free (for every $v \ne 0$ the set of fixed points of $T_v$ has
$\mu$-measure zero). Then for every integer $N \ge 1$ and every $\varepsilon \in (0, \infty]$
there is a measurable set $B \subseteq \Omega$ such that the images $T_v(B)$, for $v$ in the
integer box $[0, N)^d$, are pairwise disjoint and their union has measure at least
$1 - \varepsilon$.

Source: D. S. Ornstein and B. Weiss, *Entropy and isomorphism theorems for actions of amenable groups*, J. Anal. Math. 48 (1987), 1-141 — Theorem 5.2 establishes the multidimensional (and amenable-group) Rokhlin lemma. Listed as §109 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). No formalization found in any major prover. Via leanprover/lean-eval@38361be, problem `ornstein_weiss_rokhlin`. -/
public theorem_wanted ornstein_weiss_rokhlin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {d : ℕ} (_hd : 1 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (Fin d → ℤ) → Ω → Ω)
    (_hid : ∀ x, T 0 x = x)
    (_hT : ∀ v, MeasurePreserving (T v) μ μ)
    (_hgrp : ∀ u v x, T (u + v) x = T u (T v x))
    (_hfree : IsFreeAction μ T)
    (N : ℕ) (_hN : 1 ≤ N) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω,
      MeasurableSet B ∧
      ((boxShape d N : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
        (fun v => T v '' B) ∧
      μ (⋃ v ∈ boxShape d N, T v '' B) ≥ 1 - ε

end Dynamics

end MathlibExt.Dynamics.OrnsteinWeissWanted
