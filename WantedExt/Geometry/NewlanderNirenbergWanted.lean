/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Newlander–Nirenberg theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.NewlanderNirenberg` — newlander_nirenberg (manifest `manifests/problems/newlander_nirenberg.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.NewlanderNirenbergWanted` namespace. Mathematical
statements are unchanged. Source: A. Newlander and L. Nirenberg, `Complex analytic coordinates in almost complex manifolds`, Annals of Math, 65 (3) 1957, 391-404.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.NewlanderNirenbergWanted
namespace Geometry
namespace NewlanderNirenberg

/-!
# The Newlander–Nirenberg theorem

An almost complex structure whose Nijenhuis tensor vanishes is integrable:
near every point there are local coordinates in which the structure is the
standard one on `ℂⁿ`.

The content is local, so as with Darboux's theorem the statement lives on
an open set `U ⊆ ℝ^{2n}`. An almost complex structure on `U` is a smooth field
`J : U → End(ℝ^{2n})` with `J² = -1`; its Nijenhuis tensor is

  `N(V, W) = [JV, JW] - J[JV, W] - J[V, JW] - [V, W]`,

written with mathlib's `VectorField.lieBracket`. Because `N` is tensorial it
is enough to test it on globally smooth vector fields. The conclusion produces
a holomorphic coordinate chart: a local diffeomorphism `φ` onto an open subset
of `ℂⁿ` whose differential is complex linear, `dφ ∘ J = i · dφ`. Transition
maps between two such charts are then automatically biholomorphic, so the
charts make `U` a complex manifold inducing `J`.

mathlib has the Lie bracket of vector fields, `ContDiffOn`, `fderiv`,
`EuclideanSpace` and `OpenPartialHomeomorph`, but no almost complex
structures, no Nijenhuis tensor, and no Newlander–Nirenberg theorem. No
formalization of the theorem was found in any other proof assistant.
-/

open Set
open scoped ContDiff

/-- **Model space $\mathbb{R}^{2n}$ for the Newlander–Nirenberg theorem.** For a natural number
$n$, $E_n$ is the Euclidean space $\mathbb{R}^{2n}$, the model space carrying the almost complex
structure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- **Nijenhuis tensor.** Let $n$ be a natural number, let $J$ assign to each point
$y \in \mathbb{R}^{2n}$ a real linear map $J(y) : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$, and let
$V, W : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$ be vector fields. Write $JV$ for the vector field
$y \mapsto J(y)V(y)$ and $[V, W]$ for the Lie bracket of vector fields. The Nijenhuis tensor of
$J$ at a point $x \in \mathbb{R}^{2n}$ is
$$N(V, W)(x) = [JV, JW](x) - J(x)[JV, W](x) - J(x)[V, JW](x) - [V, W](x).$$

For an almost complex structure the last term is $J^2[V, W]$, so this is the usual torsion of
$J$. When $J$ is an almost complex structure on an open set $U \subseteq \mathbb{R}^{2n}$, the
expression is $C^\infty(U)$-bilinear in $V$ and $W$ on $U$: the terms involving the derivatives
of $V$ and $W$ cancel using $J^2 = -1$, so the value at a point $x$ of $U$ depends only on
$V(x)$, $W(x)$ and the derivative of $J$ there. -/
noncomputable def nijenhuis {n : ℕ} (J : E n → E n →L[ℝ] E n)
    (V W : E n → E n) (x : E n) : E n :=
  VectorField.lieBracket ℝ (fun y ↦ J y (V y)) (fun y ↦ J y (W y)) x
    - J x (VectorField.lieBracket ℝ (fun y ↦ J y (V y)) W x)
    - J x (VectorField.lieBracket ℝ V (fun y ↦ J y (W y)) x)
    - VectorField.lieBracket ℝ V W x

/-- **Almost complex structure on a subset of $\mathbb{R}^{2n}$.** Let $n$ be a natural number,
let $U \subseteq \mathbb{R}^{2n}$ and let $J$ assign to each point $y \in \mathbb{R}^{2n}$ a real
linear map $J(y) : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$. Then $J$ is an almost complex structure
on $U$ if $J$ is $C^\infty$ on $U$ and $J(x)(J(x)v) = -v$ for every $x \in U$ and every
$v \in \mathbb{R}^{2n}$. -/
def IsAlmostComplexOn {n : ℕ} (J : E n → E n →L[ℝ] E n) (U : Set (E n)) : Prop :=
  ContDiffOn ℝ ∞ J U ∧ ∀ x ∈ U, ∀ v : E n, J x (J x v) = -v

/-- **Vanishing of the Nijenhuis tensor on a set.** Let $n$ be a natural number, let
$U \subseteq \mathbb{R}^{2n}$, let $J$ assign to each point $y \in \mathbb{R}^{2n}$ a real linear
map $J(y) : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$, and write $N$ for the Nijenhuis tensor of $J$.
The Nijenhuis tensor of $J$ vanishes on $U$ if $N(V, W)(x) = 0$ for all $C^\infty$ vector fields
$V, W : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$ and every $x \in U$.

The vector fields range over globally smooth fields, which is the textbook hypothesis. Whenever
$U$ is open and $J$ is an almost complex structure on $U$ this is equivalent to the pointwise
condition: the tensor is bilinear over functions, and constant vector fields already realize
every pair of tangent vectors. -/
def NijenhuisVanishesOn {n : ℕ} (J : E n → E n →L[ℝ] E n) (U : Set (E n)) : Prop :=
  ∀ V W : E n → E n, ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
    ∀ x ∈ U, nijenhuis J V W x = 0

/- **The Newlander–Nirenberg theorem.** An almost complex structure with
vanishing Nijenhuis tensor is integrable. Formally: for every `x` in an open
set `U ⊆ ℝ^{2n}` carrying such a structure `J` there is a smooth local
diffeomorphism `φ` (an `OpenPartialHomeomorph`, smooth in both directions)
from a neighbourhood of `x` inside `U` onto an open subset of `ℂⁿ` whose
differential is complex linear:

  `dφ_y (J y v) = i · dφ_y v`.

Such charts are holomorphic coordinates for `J`. -/
/-- **Newlander–Nirenberg theorem.** Let $n$ be a natural number, let $U \subseteq \mathbb{R}^{2n}$
be open and let $J$ be an almost complex structure on $U$ whose Nijenhuis tensor vanishes on $U$.
Then every $x \in U$ has holomorphic coordinates for $J$: there are open sets
$S \subseteq \mathbb{R}^{2n}$ and $T \subseteq \mathbb{C}^n$ with $x \in S \subseteq U$ and a
homeomorphism $\varphi : S \to T$ such that $\varphi$ is $C^\infty$ on $S$, $\varphi^{-1}$ is
$C^\infty$ on $T$ (both as maps of real vector spaces), and for every $y \in S$ and every
$v \in \mathbb{R}^{2n}$ the real derivative of $\varphi$ satisfies
$D\varphi(y)(J(y)v) = i \, D\varphi(y)v$.

Source: A. Newlander and L. Nirenberg, `Complex analytic coordinates in almost complex manifolds`, Annals of Math, 65 (3) 1957, 391-404. Via leanprover/lean-eval@38361be, problem `newlander_nirenberg`. -/
public theorem_wanted newlander_nirenberg {n : ℕ} {U : Set (E n)} (_hU : IsOpen U)
    (J : E n → E n →L[ℝ] E n) (_hJ : IsAlmostComplexOn J U)
    (_hN : NijenhuisVanishesOn J U) {x : E n} (_hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (EuclideanSpace ℂ (Fin n)),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → EuclideanSpace ℂ (Fin n)) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : EuclideanSpace ℂ (Fin n) → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y (J y v)
          = Complex.I • fderiv ℝ (φ : E n → EuclideanSpace ℂ (Fin n)) y v

end NewlanderNirenberg
end Geometry

end MathlibExt.Geometry.NewlanderNirenbergWanted
