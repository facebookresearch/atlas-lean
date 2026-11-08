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

/-- Ambient Euclidean space `ℝⁿ`. -/
abbrev Amb (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The unit `(n-1)`-sphere `Sⁿ⁻¹ ⊂ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Set (Amb n) := sphere (0 : Amb n) 1

/-- The model hyperplane `{x | x₀ = 0}` in `ℝⁿ`, the local model for a flatly
embedded sphere. -/
def modelHyperplane (n : ℕ) [NeZero n] : Set (Amb n) := {x | x 0 = 0}

/-- An embedding `c : Sⁿ⁻¹ → ℝⁿ` is **locally flat** if near every image point
there is an ambient partial homeomorphism of `ℝⁿ` carrying the image of the
sphere locally onto the model hyperplane. -/
def LocallyFlat {n : ℕ} [NeZero n] (c : Sph n → Amb n) : Prop :=
  ∀ p : Sph n, ∃ h : OpenPartialHomeomorph (Amb n) (Amb n),
    c p ∈ h.source ∧
    h.toFun '' (h.source ∩ Set.range c) = h.target ∩ modelHyperplane n

/-- A **locally flat embedded `(n-1)`-sphere** in `ℝⁿ`: a continuous injective
locally flat map from the unit sphere. -/
structure FlatSphere (n : ℕ) [NeZero n] where
  /-- The embedding. -/
  toFun : Sph n → Amb n
  /-- It is continuous. -/
  continuous : Continuous toFun
  /-- It is injective. -/
  injective : Function.Injective toFun
  /-- It is locally flat. -/
  flat : LocallyFlat toFun

/-- The **inside** of a set `S ⊆ ℝⁿ`: the points of the complement whose
connected component there is bounded. For a locally flat sphere this is the open
ball it bounds. -/
def inside {n : ℕ} (S : Set (Amb n)) : Set (Amb n) :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

/-- The closed region between an outer flat sphere `f` and an inner flat sphere
`g`: the closed ball bounded by `f` with the open ball bounded by `g` removed. -/
def regionBetween {n : ℕ} [NeZero n] (f g : FlatSphere n) : Set (Amb n) :=
  closure (inside (Set.range f.toFun)) \ inside (Set.range g.toFun)

end MathlibExt.Topology.AnnulusShared
