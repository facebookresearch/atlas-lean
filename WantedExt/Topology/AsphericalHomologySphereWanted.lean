/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of an aspherical integer homology 4-sphere

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.AsphericalHomologySphere` — aspherical_integer_homology_four_sphere (manifest `manifests/problems/aspherical_integer_homology_four_sphere.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.AsphericalHomologySphereWanted` namespace. Mathematical
statements are unchanged. Source: J. G. Ratcliffe and S. T. Tschantz, *Some examples of aspherical 4-manifolds that are homology 4-spheres*, arXiv:math/0312436 (2003), solving [Kir97, Problem 4.17]. Earlier, F. Luo constructed an aspherical rational homology 4-sphere (1988).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.AsphericalHomologySphereWanted
namespace Topology

open CategoryTheory AlgebraicTopology
open Metric (sphere)

/-!
# Existence of an aspherical integer homology 4-sphere (Tschantz)

`[Kir97, Problem 4.17]` asks whether there is a closed aspherical 4-manifold
that is an integer homology 4-sphere. Ratcliffe and Tschantz answered this
affirmatively, constructing infinitely many aspherical 4-manifolds that are
homology 4-spheres (J. G. Ratcliffe and S. T. Tschantz, *Some examples of
aspherical 4-manifolds that are homology 4-spheres*, arXiv:math/0312436). (Earlier, Luo constructed an aspherical *rational*
homology 4-sphere.)

We state the existence of such a manifold. A closed topological 4-manifold is
bundled as `Closed4Manifold` so that we can quantify over its existence
together with its topological-space and chart data. The two conditions are:

* **aspherical** — every higher homotopy group `πₖ` (`k ≥ 2`) vanishes, at every
  basepoint. For a connected closed manifold (a CW complex) this is exactly the
  statement that the universal cover is contractible, i.e. that the manifold is a
  `K(π, 1)`.
* **integer homology 4-sphere** — the singular homology with `ℤ` coefficients
  agrees, in every degree, with that of the standard 4-sphere `S⁴`. (This forces
  `H₀ ≅ ℤ`, hence connectedness, `H₄ ≅ ℤ`, and `Hₖ = 0` otherwise.)

Mathlib has `HomotopyGroup`, singular homology (`singularHomologyFunctor`),
`ChartedSpace`, and the sphere as a topological space, but no aspherical
4-manifolds, no hyperbolic geometry in this range, and nothing resembling the
Davis/Tschantz construction.
-/

/-- A closed connected topological 4-manifold, bundled with its topological-space
and chart instances so its existence can be quantified over. Charts model
`carrier` on `EuclideanSpace ℝ (Fin 4)` (the whole space, not a half-space), so
the space is locally Euclidean with no boundary; together with `CompactSpace`
this is a closed manifold. This is the charted topological-manifold model — it
carries `ChartedSpace`, not Mathlib's stronger bundled `IsManifold` class, which
is exactly right for a topological (not necessarily smooth) manifold. -/
structure Closed4Manifold where
  /-- The underlying point set. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin 4)) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  /-- The carrier is nonempty: a closed manifold has points. -/
  [nonempty : Nonempty carrier]

attribute [instance] Closed4Manifold.topology Closed4Manifold.t2
  Closed4Manifold.secondCountable Closed4Manifold.charted Closed4Manifold.compact
  Closed4Manifold.connected Closed4Manifold.nonempty

/-- `Hₖ(X; ℤ)`, the `k`-th singular homology with integer coefficients, as an
object of `ModuleCat ℤ`. -/
noncomputable def intHomology (k : ℕ) (X : TopCat) : ModuleCat ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj X

/-- `M` is **aspherical**: every higher homotopy group vanishes at every
basepoint. -/
def Closed4Manifold.IsAspherical (M : Closed4Manifold) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ x : M.carrier, Subsingleton (HomotopyGroup (Fin k) M.carrier x)

/-- `M` is an **integer homology 4-sphere**: in every degree its integral
singular homology is isomorphic to that of the standard 4-sphere. -/
def Closed4Manifold.IsIntegerHomologySphere (M : Closed4Manifold) : Prop :=
  ∀ k : ℕ, Nonempty (intHomology k (TopCat.of M.carrier) ≅
    intHomology k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)))

/- **Existence of an aspherical integer homology 4-sphere** (Tschantz, answering
`[Kir97, Problem 4.17]`). There is a closed topological 4-manifold that is both
aspherical and an integer homology 4-sphere. -/
/-- Source: J. G. Ratcliffe and S. T. Tschantz, *Some examples of aspherical 4-manifolds that are homology 4-spheres*, arXiv:math/0312436 (2003), solving [Kir97, Problem 4.17]. Earlier, F. Luo constructed an aspherical rational homology 4-sphere (1988). Via leanprover/lean-eval@38361be, problem `aspherical_integer_homology_four_sphere`. -/
public theorem_wanted aspherical_integer_homology_four_sphere :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere

end Topology

end MathlibExt.Topology.AsphericalHomologySphereWanted
