/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Topological classification of surfaces

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.ClassificationOfSurfaces` — topological_classification_of_surfaces (manifest `manifests/problems/topological_classification_of_surfaces.toml`, rev 1, submitter Junyan Xu, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.ClassificationOfSurfacesWanted` namespace. Mathematical
statements are unchanged, with the correction that `[Nonempty S]` is added (the empty type otherwise satisfies the hypotheses vacuously). Source: Jean Gallier & Dianna Xu, *A Guide to the Classification Theorem for Compact Surfaces*, https://www.cis.upenn.edu/~jean/surfclassif-root.pdf
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Real

@[expose] public section

namespace MathlibExt.Topology.ClassificationOfSurfacesWanted
/-!
Benchmark statements for topological classification of compact connected surfaces with boundary.

The representative surface in each homeomorphism class is obtained by
gluing certain arcs in the boundary of the unit disc.

Reference: Jean Gallier & Dianna Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
Definition 6.5, Lemma 6.1, Theorem 6.1.
https://www.cis.upenn.edu/~jean/surfclassif-root.pdf
-/

namespace Complex

/-- The closed unit disc in the complex plane. -/
abbrev ClosedUnitDisc : Type := Metric.closedBall (0 : ℂ) 1

/-- **Boundary point of the unit disc at a real parameter.** For a real number $r$, this is the
point $e^{2\pi i r}$ of the closed unit disc in $\mathbb{C}$, which lies on its boundary circle. -/
noncomputable def ClosedUnitDisc.bdyPtOfReal (r : ℝ) : ClosedUnitDisc :=
  ⟨r.fourierChar, r.fourierChar.2.le⟩

end Complex

namespace Topology.ClassificationOfSurfaces

open Complex Set

/-- **Gluing relation for the orientable normal form.** For natural numbers $p$ and $n$, put
$N = 4p + 3n$ and write $e(t) = e^{2\pi i t}$ for the boundary point of the closed unit disc at
the real parameter $t$. This is the relation on the closed unit disc under which, for every
$x \in [0, 1]$ and every natural number $k < p$, the point $e((4k + x)/N)$ is related to
$e((4k + 3 - x)/N)$ and the point $e((4k + 1 + x)/N)$ is related to $e((4k + 4 - x)/N)$, and
for every $x \in [0, 1]$ and every natural number $k < n$, the point $e(-(3k + x)/N)$ is related
to $e(-(3k + 3 - x)/N)$; no other pairs are related.

Gluing the disc along it identifies the boundary in the pattern $a_1 b_1 a_1^{-1} b_1^{-1}
\cdots a_p b_p a_p^{-1} b_p^{-1} c_1 h_1 c_1^{-1} \cdots c_n h_n c_n^{-1}$, where the arcs $h_j$
are left free. -/
inductive OrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 3 - x) / (4 * p + 3 * n))
  | b (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + 1 + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 4 - x) / (4 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : OrientableRel p n
      (.bdyPtOfReal <| - (3 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| - (3 * i + 3 - x) / (4 * p + 3 * n))

/-- **Gluing relation for the non-orientable normal form.** For natural numbers $p$ and $n$, put
$N = 2p + 3n$ and write $e(t) = e^{2\pi i t}$ for the boundary point of the closed unit disc at
the real parameter $t$. This is the relation on the closed unit disc under which, for every
$x \in [0, 1]$ and every natural number $k < p$, the point $e((2k + x)/N)$ is related to
$e((2k + 1 + x)/N)$, and for every $x \in [0, 1]$ and every natural number $k < n$, the point
$e(-(3k + x)/N)$ is related to $e(-(3k + 3 - x)/N)$; no other pairs are related.

Gluing the disc along it identifies the boundary in the pattern
$a_1 a_1 \cdots a_p a_p c_1 h_1 c_1^{-1} \cdots c_n h_n c_n^{-1}$, where the arcs $h_j$ are left
free. -/
inductive NonOrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : NonOrientableRel p n
      (.bdyPtOfReal <| (2 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| (2 * i + 1 + x) / (2 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : NonOrientableRel p n
      (.bdyPtOfReal <| -(3 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| -(3 * i + 3 - x) / (2 * p + 3 * n))

/-- **Classification of compact surfaces.** Let $S$ be a nonempty, compact, connected Hausdorff
space that is a topological manifold of dimension $2$ with boundary, with charts in the closed
half-plane $\{x \in \mathbb{R}^2 : x_1 \ge 0\}$. Then $S$ is homeomorphic to the unit sphere in
$\mathbb{R}^3$, or there are natural numbers $p$ and $n$ for which one of the following holds:
$p \ge 1$ or $n \ge 1$, and $S$ is homeomorphic to the quotient of the closed unit disc by the
orientable gluing relation with parameters $p$ and $n$; or $p \ge 1$, and $S$ is homeomorphic to
the quotient of the closed unit disc by the non-orientable gluing relation with parameters $p$
and $n$. Each quotient is taken by the equivalence relation that the gluing relation generates,
with the quotient topology.

Source: Jean Gallier & Dianna Xu, *A Guide to the Classification Theorem for Compact Surfaces*, https://www.cis.upenn.edu/~jean/surfclassif-root.pdf Via leanprover/lean-eval@38361be, problem `topological_classification_of_surfaces`. -/
public theorem_wanted classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S] [Nonempty S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
    ∃ p n, ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
      (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n)))

end Topology.ClassificationOfSurfaces

end MathlibExt.Topology.ClassificationOfSurfacesWanted
