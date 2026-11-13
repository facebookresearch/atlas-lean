/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Morrison–Walker Lemma B.0.1: adapting families of maps to open covers

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.FamiliesOfMapsB01` — families_of_maps_b01 (manifest `manifests/problems/families_of_maps_b01.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.FamiliesOfMapsB01Wanted` namespace. Mathematical
statements are unchanged. Source: S. Morrison and K. Walker, *The Blob Complex*, arXiv:1009.5025, Appendix B, Lemma B.0.1 (pp. 93–96): https://arxiv.org/pdf/1009.5025
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.FamiliesOfMapsB01Wanted
/-!
# Adapting families of maps to open covers (Morrison–Walker, *The Blob Complex*)

Lemma B.0.1 of Morrison and Walker, *The Blob Complex* (arXiv:1009.5025,
Appendix B, pp. 93–96): <https://arxiv.org/pdf/1009.5025>.

Given a continuous family `f : P × X → T` parametrised by a convex linear
polyhedron `P ⊆ ℝᵏ` and a partition of unity subordinate to an open cover
`U` of a compact space `X`, the lemma produces a homotopy `F` from `f` to
a family that is *adapted* to `U` on each closed cell of a polyhedral
subdivision of `P`, with support preserved both absolutely and along
boundary subpolyhedra.

Two holes:

* `FamiliesOfMapsB01.continuous` — the continuous case (clauses 1–3 of
  the paper). The polyhedral-subdivision conclusion is what makes
  Lemma B.0.2 (the chain-level deformation retract) a chain-complex
  consequence: each closed cell is a generator of `C∗(Maps(X → T))` and
  adjacent cells share `(k−1)`-faces with cancelling orientations.

* `FamiliesOfMapsB01.biLipschitz` — the bi-Lipschitz variant of clause 4.
  Each slice `f (p, ·)` is bundled as a homeomorphism `X ≃ₜ T` (so
  surjectivity is part of the data), the paper's joint Lipschitz
  hypothesis ("`f` is Lipschitz in the `P` direction as well") is
  imposed via `LipschitzWith L f.toFun`, and the conclusion produces the
  same bundled bi-Lipschitz homeomorphism structure on every slice
  `F (t, p, ·)`.

The smooth-diffeomorphism / immersion / PL variants are omitted. The
paper does *not* prove the analogous statement for plain (merely
continuous) homeomorphisms, and we do not state it.

The trusted supporting definitions (`Supported`, `AdaptedTo`,
`IsPolyhedron`, `Subdivision`, `closedCell`, `IsBoundarySubpolyhedron`)
are factored into `ChallengeDeps.lean` automatically by the multi-hole
generator.

This statement was corrected on 2026-06-14: the original
`IsBoundarySubpolyhedron` admitted any convex hull of frontier points,
including single non-vertex points of `∂P`, for which condition 4's
support hypothesis is vacuous and spuriously forced the homotopy to
freeze those points in time — making the lemma false. Lorenzo Luccioli,
using Harmonic's Aristotle, gave a formal disproof. The repair restricts
boundary subpolyhedra to genuine faces of `P` (`IsExtreme ℝ P`), matching
the paper's "convex linear subpolyhedron of `∂P`". Thanks to both.
-/

open Set unitInterval Geometry
open scoped Topology

namespace FamiliesOfMapsB01

variable {k : ℕ} {ι X T : Type*}
  [TopologicalSpace X] [TopologicalSpace T]

/-- **Families of maps supported on a set.** Let $X$ and $T$ be topological spaces and $P$ a set. A
family of maps $f : P \times X \to T$ is supported on a set $S \subseteq X$ when it does not depend
on the parameter outside $S$: $f(p, x) = f(p', x)$ for all $p, p' \in P$ and all $x \notin S$. -/
def Supported {P : Type*} (f : P × X → T) (S : Set X) : Prop :=
  ∀ p p' : P, ∀ x ∉ S, f (p, x) = f (p', x)

/-- **Adapted families of maps.** Let $X$ and $T$ be topological spaces, $P$ a set,
$U = (U_\alpha)_{\alpha \in \iota}$ a family of subsets of $X$ and $k$ a natural number. A
family of maps $f : P \times X \to T$ is adapted to $U$ with bound $k$ when there is a finite
set $A$ of at most $k$ indices such that $f$ is supported on $\bigcup_{\alpha \in A} U_\alpha$. -/
def AdaptedTo {P : Type*} (U : ι → Set X) (k : ℕ) (f : P × X → T) : Prop :=
  ∃ A : Finset ι, A.card ≤ k ∧ Supported f (⋃ α ∈ A, U α)

/-- **Convex linear polyhedra.** A subset $P \subseteq \mathbb{R}^k$ is a convex linear polyhedron
when it is the convex hull of a finite set of points (equivalently, a bounded intersection of
finitely many closed half-spaces). -/
def IsPolyhedron (P : Set (Fin k → ℝ)) : Prop :=
  ∃ S : Finset (Fin k → ℝ), P = convexHull ℝ (S : Set _)

/-- **Polyhedral subdivisions.** A polyhedral subdivision of a set $P \subseteq \mathbb{R}^k$ is a
geometric simplicial complex in $\mathbb{R}^k$ with finitely many faces whose underlying space
equals $P$. -/
structure Subdivision (P : Set (Fin k → ℝ)) where
  complex      : SimplicialComplex ℝ (Fin k → ℝ)
  faces_finite : complex.faces.Finite
  space_eq     : complex.space = P

/-- **Closed cells.** Let $P \subseteq \mathbb{R}^k$ and let $D \subseteq \mathbb{R}^k$ be a finite
set (typically the vertex set of a face of a subdivision of $P$). The closed cell of $D$ in $P$ is
the set of points of $P$ that lie in the convex hull of $D$, viewed as a subset of $P$. -/
def closedCell (P : Set (Fin k → ℝ)) (D : Finset (Fin k → ℝ)) : Set P :=
  { p | (p : Fin k → ℝ) ∈ convexHull ℝ (D : Set (Fin k → ℝ)) }

/-- **Boundary subpolyhedra.** Let $P \subseteq \mathbb{R}^k$. A subset $Q \subseteq P$ is a
boundary subpolyhedron of $P$ when $Q$ is the convex hull of a finite set of points of
$\mathbb{R}^k$, $Q$ lies in the intrinsic frontier (relative boundary) of $P$, and $Q$ is a face of
$P$: whenever a point of $Q$ lies in the open segment between two points of $P$, both of those
points lie in $Q$.

The face condition matches the paper's "convex linear subpolyhedron of $\partial P$"; without it a
single non-vertex point of the boundary of $P$ would qualify. -/
def IsBoundarySubpolyhedron {P : Set (Fin k → ℝ)} (Q : Set P) : Prop :=
  (∃ S : Finset (Fin k → ℝ),
      ((↑) : P → Fin k → ℝ) '' Q = convexHull ℝ (S : Set (Fin k → ℝ))) ∧
    ((↑) : P → Fin k → ℝ) '' Q ⊆ intrinsicFrontier ℝ P ∧
    IsExtreme ℝ P (((↑) : P → Fin k → ℝ) '' Q)

/- **Lemma B.0.1** of Morrison–Walker, *The Blob Complex*
(arXiv:1009.5025, §B), continuous case. -/
/-- **Morrison–Walker lemma on adapting families of maps to an open cover.** Let $X$ be a compact
topological space, $T$ a topological space, $P \subseteq \mathbb{R}^k$ a convex linear polyhedron,
$(U_\alpha)_{\alpha \in \iota}$ a family of open subsets of $X$, and $\rho$ a partition of unity on
$X$ indexed by $\iota$ and subordinate to $U$ (the closed support of $\rho_\alpha$ lies in
$U_\alpha$). Then for every continuous map $f : P \times X \to T$ there is a continuous map
$F : [0, 1] \times P \times X \to T$ such that: (i) $F(0, p, x) = f(p, x)$ for all $p \in P$ and
$x \in X$; (ii) there is a polyhedral subdivision $K$ of $P$ such that, for every facet (maximal
face) $D$ of $K$, the family $(p, x) \mapsto F(1, p, x)$ with $p$ in the closed cell of $D$ is
adapted to $U$ with bound $k$; (iii) for every $S \subseteq X$, if $f$ is supported on $S$, then
$F$, as a family with parameter $(t, p) \in [0, 1] \times P$, is supported on $S$; (iv) for every
boundary subpolyhedron $Q$ of $P$ and every $S' \subseteq X$, if the restriction of $f$ to
$Q \times X$ is supported on $S'$, then the restriction of $F$ to $[0, 1] \times Q \times X$, as a
family with parameter $(t, q) \in [0, 1] \times Q$, is supported on $S'$.

Source: S. Morrison and K. Walker, *The Blob Complex*, arXiv:1009.5025, Appendix B, Lemma B.0.1 (pp. 93–96): https://arxiv.org/pdf/1009.5025 Via leanprover/lean-eval@38361be, problem `families_of_maps_b01`. -/
public theorem_wanted continuous
    {P : Set (Fin k → ℝ)} (_hP : IsPolyhedron P)
    [CompactSpace X]
    (U : ι → Set X) (_hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (_hρ : ρ.IsSubordinate U)
    (f : C(P × X, T)) :
    ∃ F : C(I × P × X, T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S')

/- **Lemma B.0.1**, bi-Lipschitz variant (part 4 of the paper). -/
/-- **Morrison–Walker lemma on adapting families of maps, bi-Lipschitz case.** Let $X$ be a
compact metric space, $T$ a metric space, $P \subseteq \mathbb{R}^k$ a convex linear polyhedron,
$(U_\alpha)_{\alpha \in \iota}$ a family of open subsets of $X$, and $\rho$ a partition of unity on
$X$ indexed by $\iota$ and subordinate to $U$. Let $f : P \times X \to T$ be continuous and suppose
that for each $p \in P$ the map $x \mapsto f(p, x)$ is a homeomorphism $h_p : X \to T$, and that for
some constant $L \ge 0$ the map $f$ is $L$-Lipschitz on $P \times X$ (for the sup metrics on
$\mathbb{R}^k$ and on $P \times X$) and every inverse $h_p^{-1}$ is $L$-Lipschitz. Then there are a
continuous map $F : [0, 1] \times P \times X \to T$, a constant $L' \ge 0$ and homeomorphisms
$H_{t,p} : X \to T$ for $(t, p) \in [0, 1] \times P$ such that: (i) $F(0, p, x) = f(p, x)$ for all
$p$ and $x$; (ii) $F(t, p, x) = H_{t,p}(x)$ for all $t$, $p$, $x$; (iii) there is a polyhedral
subdivision $K$ of $P$ such that, for every facet (maximal face) $D$ of $K$, the family
$(p, x) \mapsto F(1, p, x)$ with $p$ in the closed cell of $D$ is adapted to $U$ with bound $k$;
(iv) for every $S \subseteq X$, if $f$ is supported on $S$, then $F$, as a family with parameter
$(t, p) \in [0, 1] \times P$, is supported on $S$; (v) for every boundary subpolyhedron $Q$ of $P$
and every $S' \subseteq X$, if the restriction of $f$ to $Q \times X$ is supported on $S'$, then
the restriction of $F$ to $[0, 1] \times Q \times X$, as a family with parameter
$(t, q) \in [0, 1] \times Q$, is supported on $S'$; and (vi) every $H_{t,p}$ and every inverse
$H_{t,p}^{-1}$ is $L'$-Lipschitz.

Source: S. Morrison and K. Walker, *The Blob Complex*, arXiv:1009.5025, Appendix B, Lemma B.0.1 (pp. 93–96): https://arxiv.org/pdf/1009.5025 Via leanprover/lean-eval@38361be, problem `families_of_maps_b01`. -/
public theorem_wanted biLipschitz
    {X T : Type*} [MetricSpace X] [MetricSpace T] [CompactSpace X]
    {P : Set (Fin k → ℝ)} (_hP : IsPolyhedron P)
    {ι : Type*}
    (U : ι → Set X) (_hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (_hρ : ρ.IsSubordinate U)
    (f : C(P × X, T))
    (slice : P → (X ≃ₜ T))
    (_h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal)
    (_hf_joint     : LipschitzWith L f.toFun)
    (_hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) :
    ∃ F : C(I × P × X, T), ∃ L' : NNReal, ∃ Slice : I × P → (X ≃ₜ T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∀ t : I, ∀ p : P, ∀ x : X, F (t, p, x) = Slice (t, p) x) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S') ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp)) ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp).symm)

end FamiliesOfMapsB01

end MathlibExt.Topology.FamiliesOfMapsB01Wanted
