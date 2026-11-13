/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A 3-manifold group with no faithful representation into GL(4, ℝ)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.NonlinearThreeManifoldGroup` — nonlinear_three_manifold_group (manifest `manifests/problems/nonlinear_three_manifold_group.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.NonlinearThreeManifoldGroupWanted` namespace. Mathematical
statements are unchanged. Source: J. O. Button, *Aspherical 3-manifold groups not in GL(4, k) for any field k*, arXiv:1404.4639 (2014). See the discussion of [Kir97, Problem 3.33] in the K3 problem list.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.NonlinearThreeManifoldGroupWanted
namespace Topology

open Matrix

/-!
# A 3-manifold group with no faithful representation into GL(4, ℝ) (Button)

`[Kir97, Problem 3.33]`, due to W. Thurston, asks whether every finitely
generated 3-manifold group admits a faithful (injective) representation into
`GL(4, ℝ)`. This is true for hyperbolic 3-manifolds, but Button gave a negative
answer in general: the fundamental groups of certain closed graph manifolds
admit no faithful representation into `GL(4, k)` for *any* field `k` (J. O.
Button, *Aspherical 3-manifold groups not in `GL(4, k)`*, 2014).

We state the negative answer to Thurston's question over `ℝ`: there is a closed
connected 3-manifold whose fundamental group has no faithful representation into
`GL(4, ℝ)`. (Button's theorem is in fact stronger, ruling out every field.)

A closed connected topological 3-manifold is bundled as `Closed3Manifold`. The
statement is not vacuous: a simply connected witness would have trivial `π₁`,
whose unique map to `GL(4, ℝ)` is injective, contradicting the universal
non-injectivity — so the witness must genuinely have a non-linear fundamental
group.

Mathlib has `FundamentalGroup`, `GL`, `MonoidHom`, and `ChartedSpace`, but no
graph manifolds and none of the linearity obstructions (residual properties,
the structure theory of 3-manifold groups) Button's argument relies on.
-/

/-- **Closed topological 3-manifold.** A closed topological 3-manifold is a nonempty, compact,
connected, Hausdorff, second-countable topological space $M$ together with an atlas of charts,
homeomorphisms from open subsets of $M$ onto open subsets of $\mathbb{R}^3$, whose domains cover
$M$. Since the charts land in $\mathbb{R}^3$ itself rather than in a half-space, $M$ has no
boundary. -/
structure Closed3Manifold where
  /-- The underlying point set. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  /-- The carrier is nonempty: a closed manifold has points. -/
  [nonempty : Nonempty carrier]

attribute [instance] Closed3Manifold.topology Closed3Manifold.t2
  Closed3Manifold.secondCountable Closed3Manifold.charted Closed3Manifold.compact
  Closed3Manifold.connected Closed3Manifold.nonempty

/- **A non-linear 3-manifold group** (Button, answering `[Kir97, Problem 3.33]`
negatively). There is a closed connected topological 3-manifold `M` and a
basepoint `x` such that the fundamental group `π₁(M, x)` admits no faithful
(injective) representation into `GL(4, ℝ)`. -/
/-- **A closed 3-manifold group with no faithful representation in $GL_4(\mathbb{R})$.** There
is a closed connected topological 3-manifold $M$ with a point $x$ such that no group
homomorphism from the fundamental group $\pi_1(M, x)$ to $GL_4(\mathbb{R})$ is injective.

Source: J. O. Button, *Aspherical 3-manifold groups not in GL(4, k) for any field k*, arXiv:1404.4639 (2014). See the discussion of [Kir97, Problem 3.33] in the K3 problem list. Via leanprover/lean-eval@38361be, problem `nonlinear_three_manifold_group`. -/
public theorem_wanted nonlinear_three_manifold_group :
    ∃ (M : Closed3Manifold) (x : M.carrier),
      ∀ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ, ¬ Function.Injective f

end Topology

end MathlibExt.Topology.NonlinearThreeManifoldGroupWanted
