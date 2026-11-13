/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Smale conjecture (Hatcher) in relative parameterized form

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.SmaleConjecture` — smale_conjecture (manifest `manifests/problems/smale_conjecture.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.SmaleConjectureWanted` namespace. Mathematical
statements are unchanged. Source: A. Hatcher, A proof of the Smale conjecture, Diff(S3) = O(4), Ann. of Math. 117 (1983).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace MathlibExt.Topology.SmaleConjectureWanted
namespace Topology

open scoped Manifold ContDiff
open Metric (sphere)

/-!
# Smale conjecture (Hatcher, 1983), relative parameterized form

Hatcher's theorem says the inclusion `O(4) ↪ Diff(S³)` (restriction of the linear action
on ℝ⁴) is a homotopy equivalence of topological spaces. Stating it in that form would
require mathlib to carry the C^∞ topology on `Diffeomorph S³ S³`, which it does not yet
have.

We state the equivalent **relative parameterized** form: for every compact smooth
manifold-with-boundary X and every smooth family of self-diffeomorphisms
`F : X × S³ → S³` whose restriction to `∂X × S³` already comes from a continuous map
`ψ_bdry : ∂X → O(4)` (acting by the linear action), there is a continuous extension
`ψ : X → O(4)` with `ψ|∂X = ψ_bdry` and a smooth isotopy rel `∂X` from `F` to the
family induced by `ψ`.

For `X = D^k`, `∂X = S^{k-1}`, this says `π_k(Diff(S³), O(4)) = 0` for all `k ≥ 1`
in the form formalized below (the `[NeZero n]` hypothesis on the model dimension
excludes the zero-dimensional parameter case),
which (modulo smoothing theory translating between smooth families parameterized by X
and continuous maps `X → Diff(S³)` with the C^∞ topology) is equivalent to
`O(4) ↪ Diff(S³)` being a homotopy equivalence.

The Cerf case `X = pt` (so `∂X = ∅`, the relative hypothesis is vacuous) is
Cerf's theorem Γ₄ = 0 (see `CerfGammaFour.lean`). That zero-dimensional case is
not a specialization of the declaration below and is omitted here; this entry is
the positive-dimensional relative form only.

**Desired future improvement.** Once mathlib gains a C^∞ topology on `Diffeomorph M N`
(making it a topological group, with smooth families ↔ continuous maps into it), this
statement should be rewritten in the direct form: the continuous group homomorphism
`O(4) ↪ Diff(S³)` is a homotopy equivalence of topological spaces. Until then, the
relative parameterized form below is the most faithful statement available.
-/

/- **Smale conjecture (Hatcher 1983), relative parameterized form.**
For every compact smooth manifold-with-boundary `X` and every smooth family `F` of
self-diffeomorphisms of `S³` parameterized by `X` whose boundary restriction already
factors through the linear action of `O(4)`, there is a smooth isotopy of `F`, rel
`∂X`, to a family fully factoring through `O(4)`. -/
/-- **Smale conjecture (Hatcher), relative parametrized form.** Let $n \ge 1$ and let $X$ be a
compact, Hausdorff, second-countable smooth manifold with boundary modelled on the
$n$-dimensional half-space, with boundary $\partial X$. Write $S^3$ for the unit sphere of
$\mathbb{R}^4$ and let the orthogonal group $O(4)$ act linearly on it. Let
$F, F' : X \times S^3 \to S^3$ be smooth maps with $F(x, F'(x, p)) = p$ and $F'(x, F(x, p)) = p$
for all $x \in X$ and $p \in S^3$, and let $\psi_\partial : \partial X \to O(4)$ be a continuous
map with $F(b, p) = \psi_\partial(b)\, p$ for all $b \in \partial X$ and $p \in S^3$. Then there
are a continuous map $\psi : X \to O(4)$ that agrees with $\psi_\partial$ on $\partial X$ and
smooth maps $H, H' : X \times [0, 1] \times S^3 \to S^3$ such that for all $x \in X$,
$t \in [0, 1]$ and $p \in S^3$ we have $H(x, t, H'(x, t, p)) = p$, $H'(x, t, H(x, t, p)) = p$,
$H(x, 0, p) = F(x, p)$ and $H(x, 1, p) = \psi(x)\, p$, and $H(b, t, p) = F(b, p)$ whenever
$b \in \partial X$.

Thus each $F(x, \cdot)$ is a diffeomorphism of $S^3$, and $H$ is a smooth isotopy through
diffeomorphisms, relative to $\partial X$, from the family $F$ to the linear family $\psi$.

Source: A. Hatcher, A proof of the Smale conjecture, Diff(S3) = O(4), Ann. of Math. 117 (1983). Via leanprover/lean-eval@38361be, problem `smale_conjecture`. -/
public theorem_wanted smale_conjecture
    {n : ℕ} [NeZero n]
    (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (EuclideanHalfSpace n) X] [IsManifold (𝓡∂ n) ∞ X]
    [CompactSpace X]
    (F F' : X × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
            sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hF  : ContMDiff ((𝓡∂ n).prod (𝓡 3)) (𝓡 3) ∞ F)
    (hF' : ContMDiff ((𝓡∂ n).prod (𝓡 3)) (𝓡 3) ∞ F')
    (hFinv₁ : ∀ x p, F  (x, F' (x, p)) = p)
    (hFinv₂ : ∀ x p, F' (x, F  (x, p)) = p)
    (ψ_bdry : (𝓡∂ n).boundary X → Matrix.orthogonalGroup (Fin 4) ℝ)
    (hψ_bdry_cont : Continuous ψ_bdry)
    (hF_bdry : ∀ (b : (𝓡∂ n).boundary X)
                 (p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
              (F ((b : X), p) : EuclideanSpace ℝ (Fin 4)) =
                Matrix.UnitaryGroup.toLinearEquiv (ψ_bdry b)
                  (p : EuclideanSpace ℝ (Fin 4))) :
    ∃ (ψ : X → Matrix.orthogonalGroup (Fin 4) ℝ)
      (H H' : X × unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
              sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      Continuous ψ ∧
      (∀ b : (𝓡∂ n).boundary X, ψ (b : X) = ψ_bdry b) ∧
      ContMDiff ((𝓡∂ n).prod ((𝓡∂ 1).prod (𝓡 3))) (𝓡 3) ∞ H ∧
      ContMDiff ((𝓡∂ n).prod ((𝓡∂ 1).prod (𝓡 3))) (𝓡 3) ∞ H' ∧
      (∀ x t p, H  (x, t, H' (x, t, p)) = p) ∧
      (∀ x t p, H' (x, t, H  (x, t, p)) = p) ∧
      (∀ x p, H (x, 0, p) = F (x, p)) ∧
      (∀ x (p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
              (H (x, 1, p) : EuclideanSpace ℝ (Fin 4)) =
              Matrix.UnitaryGroup.toLinearEquiv (ψ x)
                (p : EuclideanSpace ℝ (Fin 4))) ∧
      (∀ (b : (𝓡∂ n).boundary X)
         (t : unitInterval)
         (p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
              H ((b : X), t, p) = F ((b : X), p))

end Topology

end MathlibExt.Topology.SmaleConjectureWanted
