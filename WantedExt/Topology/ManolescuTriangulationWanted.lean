/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Manolescu's disproof of the triangulation conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.ManolescuTriangulation` — manolescu_triangulation_disproof (manifest `manifests/problems/manolescu_triangulation_disproof.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.ManolescuTriangulationWanted` namespace. Mathematical
statements are unchanged. Source: C. Manolescu, *Pin(2)-equivariant Seiberg–Witten Floer homology and the triangulation conjecture*, J. Amer. Math. Soc. 29 (2016), via the Galewski–Stern and Matumoto reduction. Earlier, the triangulation conjecture was known false in dimension 4 (Casson).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.ManolescuTriangulationWanted
open Geometry

namespace Topology

/-!
# Manolescu's disproof of the triangulation conjecture (2016)

The triangulation conjecture asked whether every topological manifold is
homeomorphic to a simplicial complex. Manolescu disproved it: in every dimension
`n ≥ 5` there are closed topological `n`-manifolds that are not triangulable. He
proved this by constructing a `Pin(2)`-equivariant Seiberg–Witten Floer homology
and using it to refute the existence of an element of the homology-cobordism
group of homology 3-spheres demanded by the Galewski–Stern / Matumoto reduction
of the triangulation problem.

We state the resolved theorem: for every `n ≥ 5` there is a closed `n`-manifold
that is not triangulable.

* A closed topological `n`-manifold is bundled as `ClosedTopManifold n`.
* **Triangulable** is encoded as being homeomorphic to the geometric realization
  of a *finite* simplicial complex — Mathlib's `SimplicialComplex ℝ E` with
  `K.faces` finite, whose `space` is the union of its faces, carrying the
  subspace topology from `E`. We let `E` range over the finite-dimensional
  Euclidean spaces `ℝᴺ`. This is faithful for a *closed* (compact) manifold: a
  triangulation of a compact space is a finite complex, which geometrically
  realizes in some `ℝᴺ`, and on a finite complex the ambient subspace topology of
  `ℝᴺ` (a normed space) is the honest polyhedron topology. The finiteness
  requirement is essential — without it the union-of-faces could be taken to be
  one singleton `0`-face per point of an embedded copy of `M`, whose `space` is
  just `M` again, which would make every manifold vacuously "triangulable".

Mathlib has `SimplicialComplex` and `ChartedSpace`, but no PL topology, no
manifold triangulation theory, no Seiberg–Witten / Floer homology, and nothing
of the Galewski–Stern obstruction — so neither the construction nor the
obstruction is anywhere in reach.
-/

/-- **Closed topological manifold.** For a natural number $n$, a closed topological $n$-manifold
is a nonempty, compact, connected, Hausdorff, second-countable topological space $M$ together
with an atlas of charts, homeomorphisms from open subsets of $M$ onto open subsets of
$\mathbb{R}^n$, whose domains cover $M$. Since the charts land in $\mathbb{R}^n$ itself rather
than in a half-space, $M$ has no boundary. -/
structure ClosedTopManifold (n : ℕ) where
  /-- The underlying point set. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  /-- The carrier is nonempty: a closed manifold has points. -/
  [nonempty : Nonempty carrier]

attribute [instance] ClosedTopManifold.topology ClosedTopManifold.t2
  ClosedTopManifold.secondCountable ClosedTopManifold.charted
  ClosedTopManifold.compact ClosedTopManifold.connected ClosedTopManifold.nonempty

/-- **Triangulable closed manifold.** A closed topological $n$-manifold $M$ is triangulable if,
for some natural number $N$, there is a simplicial complex $K$ in $\mathbb{R}^N$ with finitely
many faces such that $M$ is homeomorphic to the geometric realization of $K$, the union of its
faces with the subspace topology from $\mathbb{R}^N$.

For a compact manifold this is the usual notion of triangulability. Requiring finitely many faces
is essential: otherwise any copy of $M$ embedded in $\mathbb{R}^N$ would be the realization of the
complex whose faces are its points. -/
def Triangulable {n : ℕ} (M : ClosedTopManifold n) : Prop :=
  ∃ (N : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
    K.faces.Finite ∧ Nonempty (M.carrier ≃ₜ K.space)

/- **Manolescu's theorem (2016): the triangulation conjecture is false**, in
every dimension `≥ 5`. For each `n ≥ 5` there is a closed connected topological
`n`-manifold that is not homeomorphic to any simplicial complex. -/
/-- **Manolescu's disproof of the triangulation conjecture.** For every natural number $n \ge 5$
there is a closed connected topological $n$-manifold that is not triangulable.

Source: C. Manolescu, *Pin(2)-equivariant Seiberg–Witten Floer homology and the triangulation conjecture*, J. Amer. Math. Soc. 29 (2016), via the Galewski–Stern and Matumoto reduction. Earlier, the triangulation conjecture was known false in dimension 4 (Casson). Via leanprover/lean-eval@38361be, problem `manolescu_triangulation_disproof`. -/
public theorem_wanted manolescu_triangulation_disproof :
    ∀ n : ℕ, 5 ≤ n → ∃ M : ClosedTopManifold n, ¬ Triangulable M

end Topology

end MathlibExt.Topology.ManolescuTriangulationWanted
