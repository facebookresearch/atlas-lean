/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared annulus-theorem infrastructure

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
38361be884302c7edce1908c4aef8296eb2cb27e, modules `LeanEval.Topology.AnnulusTheoremDimFour` and `LeanEval.Topology.AnnulusTheoremHighDim` —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. This neutral helper module is shared by the
dimension-four and high-dimensional annulus-theorem wanted entries, so
both theorems speak about the same `FlatSphere`, `inside`, and
`regionBetween`. The definitions are unchanged apart from the namespace.
-/
module

public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.AnnulusShared

open Metric (sphere)

/-!
# Shared infrastructure for the Annulus Theorem eval problems

The annulus theorem states that the closed region between two disjoint, nested,
*locally flat* embedded `(n-1)`-spheres in `ℝⁿ` is homeomorphic to `Sⁿ⁻¹ × [0,1]`.
This module collects the definitions shared by the two eval problems for the
theorem (`AnnulusTheoremDimFour` — Quinn (1982), and `AnnulusTheoremHighDim` —
Kirby (1969)), so both entries use the same `FlatSphere` API.
-/

/-- **Ambient Euclidean space.** For a natural number $n$, the ambient space is the real
Euclidean space $\mathbb{R}^n$ of dimension $n$, with coordinates indexed by $0, \dots, n-1$ and
the Euclidean norm. -/
abbrev Amb (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- **Unit sphere in Euclidean space.** For a natural number $n$, the unit sphere
$S^{n-1} \subseteq \mathbb{R}^n$ is the set of points of $\mathbb{R}^n$ at Euclidean distance $1$
from the origin. -/
abbrev Sph (n : ℕ) : Set (Amb n) := sphere (0 : Amb n) 1

/-- **Model hyperplane.** For $n \ge 1$, the model hyperplane in $\mathbb{R}^n$ is the set of
points $x = (x_0, \dots, x_{n-1})$ whose first coordinate $x_0$ is $0$. It is the local model for
a locally flat embedded sphere. -/
def modelHyperplane (n : ℕ) [NeZero n] : Set (Amb n) := {x | x 0 = 0}

/-- **Locally flat maps of the sphere.** Let $n \ge 1$, let $S^{n-1} \subseteq \mathbb{R}^n$ be the
unit sphere and let $H = \{x \in \mathbb{R}^n : x_0 = 0\}$ be the model hyperplane. A map
$c : S^{n-1} \to \mathbb{R}^n$ is locally flat if for every point $p \in S^{n-1}$ there are open
sets $U, V \subseteq \mathbb{R}^n$ with $c(p) \in U$ and a homeomorphism $h : U \to V$ such that
$h(U \cap c(S^{n-1})) = V \cap H$. -/
def LocallyFlat {n : ℕ} [NeZero n] (c : Sph n → Amb n) : Prop :=
  ∀ p : Sph n, ∃ h : OpenPartialHomeomorph (Amb n) (Amb n),
    c p ∈ h.source ∧
    h.toFun '' (h.source ∩ Set.range c) = h.target ∩ modelHyperplane n

/-- **Locally flat embedded sphere.** For $n \ge 1$, a locally flat embedded $(n-1)$-sphere in
$\mathbb{R}^n$ is a map $f : S^{n-1} \to \mathbb{R}^n$ from the unit sphere that is continuous,
injective and locally flat. -/
structure FlatSphere (n : ℕ) [NeZero n] where
  /-- The embedding. -/
  toFun : Sph n → Amb n
  /-- It is continuous. -/
  continuous : Continuous toFun
  /-- It is injective. -/
  injective : Function.Injective toFun
  /-- It is locally flat. -/
  flat : LocallyFlat toFun

/-- **Inside of a set.** For a set $S \subseteq \mathbb{R}^n$, the inside of $S$ is the set of
points $x \notin S$ whose connected component in the complement $\mathbb{R}^n \setminus S$ is
bounded.

For the image of a locally flat embedded sphere, this is the open ball it bounds. -/
def inside {n : ℕ} (S : Set (Amb n)) : Set (Amb n) :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- **Region between two flat spheres.** Let $n \ge 1$ and let $f$ and $g$ be locally flat
embedded $(n-1)$-spheres in $\mathbb{R}^n$. The region between $f$ and $g$ is the closure of the
inside of the image of $f$ with the inside of the image of $g$ removed, where the inside of a set
$S$ is the set of points $x \notin S$ whose connected component in $\mathbb{R}^n \setminus S$ is
bounded. -/
def regionBetween {n : ℕ} [NeZero n] (f g : FlatSphere n) : Set (Amb n) :=
  closure (inside (Set.range f.toFun)) \ inside (Set.range g.toFun)

end MathlibExt.Topology.AnnulusShared
