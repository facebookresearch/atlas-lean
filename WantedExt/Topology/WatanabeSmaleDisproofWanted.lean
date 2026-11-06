/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Watanabe's disproof of the 4-dimensional Smale conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.WatanabeSmaleDisproof` — watanabe_four_dim_smale_disproof (manifest `manifests/problems/watanabe_four_dim_smale_disproof.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.WatanabeSmaleDisproofWanted` namespace. Mathematical
statements are unchanged. Source: T. Watanabe, *Some exotic nontrivial elements of the rational homotopy groups of Diff(S⁴)*, arXiv:1812.02448 (2018). Pairs with the positive S³ statement of Hatcher (Ann. of Math. 117, 1983) in SmaleConjecture.lean.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace MathlibExt.Topology.WatanabeSmaleDisproofWanted
namespace Topology

open scoped Manifold ContDiff
open Metric (sphere)

/-!
# Watanabe's disproof of the 4-dimensional Smale conjecture, `[Kir97, Problems 4.34 and 4.126]`

The 4-dimensional generalized Smale conjecture asks whether the inclusion
`O(5) ↪ Diff(S⁴)` (restriction of the linear action on `ℝ⁵`) is a homotopy
equivalence — equivalently, whether `Diff(D⁴ rel ∂)` is contractible. Watanabe
(*Some exotic nontrivial elements of the rational homotopy groups of
`Diff(S⁴)`*, 2018) disproved it, showing `πₖ(Diff(D⁴ rel ∂)) ⊗ ℚ ≠ 0` for many
`k` (including `k = 1`), via configuration-space integrals.

This is the exact negation of the four-dimensional analogue of the (positive)
Smale conjecture for `S³` stated in `SmaleConjecture.lean`. That file states the
relative parameterized form of `O(4) ↪ Diff(S³)` being a homotopy equivalence —
the form Mathlib can express today, since it has no `C^∞` topology on
`Diffeomorph M N`. Here we bump `S³ ⤳ S⁴` and `O(4) ⤳ O(5)` and assert the
**negation**: the parameterized homotopy-equivalence statement for `S⁴` and
`O(5)` is false. Its inner statement reads: for every compact smooth
manifold-with-boundary `X` and every smooth family `F` of self-diffeomorphisms
of `S⁴` whose boundary restriction factors through the linear action of `O(5)`,
there is a smooth isotopy of `F`, rel `∂X`, to a family fully factoring through
`O(5)`. Taking `X = Sᵏ` (closed, so the boundary hypotheses are vacuous) this is
`πₖ(Diff(S⁴), O(5)) = 0`; Watanabe's nontriviality of `Diff(D⁴ rel ∂)` makes it
fail, which is exactly what the `¬` below records.

As in `SmaleConjecture.lean`, the translation between smooth families
parameterized by `X` and continuous maps into `Diff(S⁴)` with the `C^∞` topology
is the standard smoothing-theory dictionary; once Mathlib has that topology this
should be restated as "`O(5) ↪ Diff(S⁴)` is not a homotopy equivalence".
-/

/- **Watanabe's theorem (2018): the 4-dimensional Smale conjecture is false**,
answering `[Kir97, Problems 4.34 and 4.126]`. The relative parameterized
statement that `O(5) ↪ Diff(S⁴)` is a homotopy equivalence — the exact
four-dimensional analogue of the (true) Smale conjecture for `S³` — does not
hold. -/
/-- **The four-dimensional Smale conjecture is false (Watanabe).** Write $S^4$ for the unit sphere
of $\mathbb{R}^5$ and let the orthogonal group $O(5)$ act linearly on it. There are an $n \ge 1$,
a compact, Hausdorff, second-countable smooth manifold $X$ with boundary modelled on the
$n$-dimensional half-space, with boundary $\partial X$, smooth maps
$F, F' : X \times S^4 \to S^4$ with $F(x, F'(x, p)) = p$ and $F'(x, F(x, p)) = p$ for all
$x \in X$ and $p \in S^4$, and a continuous map $\psi_\partial : \partial X \to O(5)$ with
$F(b, p) = \psi_\partial(b)\, p$ for all $b \in \partial X$ and $p \in S^4$, such that the
following fails: there are a continuous map $\psi : X \to O(5)$ that agrees with
$\psi_\partial$ on $\partial X$ and smooth maps $H, H' : X \times [0, 1] \times S^4 \to S^4$
such that for all $x \in X$, $t \in [0, 1]$ and $p \in S^4$ we have
$H(x, t, H'(x, t, p)) = p$, $H'(x, t, H(x, t, p)) = p$, $H(x, 0, p) = F(x, p)$ and
$H(x, 1, p) = \psi(x)\, p$, and $H(b, t, p) = F(b, p)$ whenever $b \in \partial X$.

In other words, the relative parametrized form of the statement that $O(5) \to \mathrm{Diff}(S^4)$
is a homotopy equivalence, the analogue of Hatcher's theorem for $S^3$, does not hold.

Source: T. Watanabe, *Some exotic nontrivial elements of the rational homotopy groups of Diff(S⁴)*, arXiv:1812.02448 (2018). Pairs with the positive S³ statement of Hatcher (Ann. of Math. 117, 1983) in SmaleConjecture.lean. Via leanprover/lean-eval@38361be, problem `watanabe_four_dim_smale_disproof`. -/
public theorem_wanted watanabe_four_dim_smale_disproof :
    ¬ (∀ {n : ℕ} [NeZero n]
        (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
        [ChartedSpace (EuclideanHalfSpace n) X] [IsManifold (𝓡∂ n) ∞ X]
        [CompactSpace X]
        (F F' : X × sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 →
                sphere (0 : EuclideanSpace ℝ (Fin 5)) 1),
        ContMDiff ((𝓡∂ n).prod (𝓡 4)) (𝓡 4) ∞ F →
        ContMDiff ((𝓡∂ n).prod (𝓡 4)) (𝓡 4) ∞ F' →
        (∀ x p, F  (x, F' (x, p)) = p) →
        (∀ x p, F' (x, F  (x, p)) = p) →
        ∀ (ψ_bdry : (𝓡∂ n).boundary X → Matrix.orthogonalGroup (Fin 5) ℝ),
        Continuous ψ_bdry →
        (∀ (b : (𝓡∂ n).boundary X)
           (p : sphere (0 : EuclideanSpace ℝ (Fin 5)) 1),
              (F ((b : X), p) : EuclideanSpace ℝ (Fin 5)) =
                Matrix.UnitaryGroup.toLinearEquiv (ψ_bdry b)
                  (p : EuclideanSpace ℝ (Fin 5))) →
        ∃ (ψ : X → Matrix.orthogonalGroup (Fin 5) ℝ)
          (H H' : X × unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 →
                  sphere (0 : EuclideanSpace ℝ (Fin 5)) 1),
          Continuous ψ ∧
          (∀ b : (𝓡∂ n).boundary X, ψ (b : X) = ψ_bdry b) ∧
          ContMDiff ((𝓡∂ n).prod ((𝓡∂ 1).prod (𝓡 4))) (𝓡 4) ∞ H ∧
          ContMDiff ((𝓡∂ n).prod ((𝓡∂ 1).prod (𝓡 4))) (𝓡 4) ∞ H' ∧
          (∀ x t p, H  (x, t, H' (x, t, p)) = p) ∧
          (∀ x t p, H' (x, t, H  (x, t, p)) = p) ∧
          (∀ x p, H (x, 0, p) = F (x, p)) ∧
          (∀ x (p : sphere (0 : EuclideanSpace ℝ (Fin 5)) 1),
              (H (x, 1, p) : EuclideanSpace ℝ (Fin 5)) =
              Matrix.UnitaryGroup.toLinearEquiv (ψ x)
                (p : EuclideanSpace ℝ (Fin 5))) ∧
          (∀ (b : (𝓡∂ n).boundary X)
             (t : unitInterval)
             (p : sphere (0 : EuclideanSpace ℝ (Fin 5)) 1),
              H ((b : X), t, p) = F ((b : X), p)))

end Topology

end MathlibExt.Topology.WatanabeSmaleDisproofWanted
