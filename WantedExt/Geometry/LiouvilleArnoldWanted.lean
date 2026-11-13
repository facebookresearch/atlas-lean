/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Liouville–Arnold theorem on integrable systems

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.LiouvilleArnold` — liouville_arnold (manifest `manifests/problems/liouville_arnold.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.LiouvilleArnoldWanted` namespace. Mathematical
statements are unchanged. Source: V. I. Arnold, *Mathematical Methods of Classical Mechanics* (2nd ed., 1989), Theorem 49.A.1 (the standard modern reference). The result is due to Liouville (1855) for the local existence of action-angle coordinates and Arnold (1963) for the compact-connected-component topology. Listed as §45 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.LiouvilleArnoldWanted
namespace Geometry
namespace LiouvilleArnold

/-!
# Liouville–Arnold theorem

§45 of Knill's *Some Fundamental Theorems in Mathematics*. On a `2n`-
dimensional symplectic manifold with `n` smooth, pointwise linearly
independent, pairwise Poisson-commuting first integrals
`F₁, …, F_n`, every compact connected component of a joint level set
`{F₁ = c₁, …, F_n = c_n}` is diffeomorphic to the `n`-torus `T^n`.

We formalize on `E n := EuclideanSpace ℝ (Fin (2n))` with the standard
symplectic form `ω₀ = ∑ᵢ dpᵢ ∧ dqᵢ`. The induced Poisson bracket is
`{F, G}(x) = ∑ᵢ ((∂F/∂pᵢ)(x)(∂G/∂qᵢ)(x) − (∂F/∂qᵢ)(x)(∂G/∂pᵢ)(x))`.

Mathlib has `EuclideanSpace`, `fderiv`, `Matrix.charpoly`, `AddCircle`,
`Homeomorph`, and the standard smooth-manifold framework, but **no
Poisson brackets, no symplectic manifolds beyond `Matrix.symplecticGroup`,
no first integrals, no Liouville–Arnold theorem in any form** (the
`Liouville` files in `Mathlib/Analysis/Complex/` are Liouville's theorem
on bounded entire functions, a different theorem). The Challenge ships
~1 page of helper definitions (`E`, `idxP`, `idxQ`, `poissonBracket`,
`IsLiouvilleIntegrable`, `levelSet`).
-/

open Set
open scoped ContDiff

/-- **The model space $\mathbb{R}^{2n}$ of the Liouville–Arnold theorem.** For a natural number
$n$, $E_n$ is the Euclidean space $\mathbb{R}^{2n}$, with coordinates indexed by
$0, \dots, 2n-1$ and the standard inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- **Liouville–Arnold coordinates: index of $p_i$.** For $i \in \{0, \dots, n-1\}$, the
coordinate $p_i$ of $\mathbb{R}^{2n}$ is coordinate number $i$: this map sends $i$ to the same
number $i$, regarded as an index in $\{0, \dots, 2n-1\}$. -/
def idxP {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- **Liouville–Arnold coordinates: index of $q_i$.** For $i \in \{0, \dots, n-1\}$, the
coordinate $q_i$ of $\mathbb{R}^{2n}$ is coordinate number $n + i$: this map sends $i$ to
$n + i \in \{0, \dots, 2n-1\}$. -/
def idxQ {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val + n, by have := i.isLt; omega⟩

/-- **Standard Poisson bracket on $\mathbb{R}^{2n}$.** Write the coordinates of a point
$x \in \mathbb{R}^{2n}$ as $p_i = x_i$ and $q_i = x_{n+i}$ for $i = 0, \dots, n-1$. For functions
$F, G \colon \mathbb{R}^{2n} \to \mathbb{R}$, the Poisson bracket for the symplectic form
$\omega_0 = \sum_i dp_i \wedge dq_i$ is the function
$$
\{F, G\}(x) = \sum_{i=0}^{n-1} \left( \frac{\partial F}{\partial p_i}(x)
\frac{\partial G}{\partial q_i}(x) - \frac{\partial F}{\partial q_i}(x)
\frac{\partial G}{\partial p_i}(x) \right).
$$

Partial derivatives are read off the Fréchet derivative, which is taken to be zero at points
where the function is not differentiable. -/
noncomputable def poissonBracket {n : ℕ} (F G : E n → ℝ) (x : E n) : ℝ :=
  ∑ i : Fin n,
    (fderiv ℝ F x (EuclideanSpace.single (idxP i) (1 : ℝ)) *
        fderiv ℝ G x (EuclideanSpace.single (idxQ i) (1 : ℝ))
      - fderiv ℝ F x (EuclideanSpace.single (idxQ i) (1 : ℝ)) *
        fderiv ℝ G x (EuclideanSpace.single (idxP i) (1 : ℝ)))

/-- **Liouville integrable system on a subset of $\mathbb{R}^{2n}$.** Functions
$F_0, \dots, F_{n-1} \colon \mathbb{R}^{2n} \to \mathbb{R}$ are Liouville integrable on a set
$U \subseteq \mathbb{R}^{2n}$ if each $F_i$ is $C^\infty$ on $U$, the Poisson brackets
$\{F_i, F_j\}$ vanish at every point of $U$ for all $i, j$, and at every $x \in U$ the
Fréchet derivatives $dF_0(x), \dots, dF_{n-1}(x)$ are linearly independent over $\mathbb{R}$.

The set $U$ is not required to be open; the Liouville–Arnold theorem assumes this separately. -/
def IsLiouvilleIntegrable {n : ℕ} (F : Fin n → E n → ℝ) (U : Set (E n)) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (F i) U) ∧
  (∀ i j, ∀ x ∈ U, poissonBracket (F i) (F j) x = 0) ∧
  (∀ x ∈ U, LinearIndependent ℝ (fun i => fderiv ℝ (F i) x))

/-- **Common level set of $n$ functions on $\mathbb{R}^{2n}$.** For functions
$F_0, \dots, F_{n-1} \colon \mathbb{R}^{2n} \to \mathbb{R}$ and values
$c_0, \dots, c_{n-1} \in \mathbb{R}$, the common level set is
$\{x \in \mathbb{R}^{2n} : F_i(x) = c_i \text{ for all } i\}$. -/
def levelSet {n : ℕ} (F : Fin n → E n → ℝ) (c : Fin n → ℝ) : Set (E n) :=
  {x | ∀ i, F i x = c i}

/- **Liouville–Arnold theorem.** For a Liouville integrable system on an
open `U ⊆ ℝ^{2n}`, every compact connected joint level set
`M_c = {x ∈ ℝ^{2n} : F₁(x) = c₁, …, F_n(x) = c_n}` contained in `U` is
homeomorphic to the `n`-torus `T^n = (ℝ/ℤ)^n`.

The hypotheses *compact* and *connected* on the level set, and its
containment in the open set where the derivatives are independent,
restore standard regularity assumptions that Knill elides; without them
the conclusion fails. -/
/-- **Liouville–Arnold theorem.** Let $U \subseteq \mathbb{R}^{2n}$ be open and let
$F_0, \dots, F_{n-1} \colon \mathbb{R}^{2n} \to \mathbb{R}$ be Liouville integrable on $U$. For
$c = (c_0, \dots, c_{n-1}) \in \mathbb{R}^n$, let
$M_c = \{x \in \mathbb{R}^{2n} : F_i(x) = c_i \text{ for all } i\}$ be the common level set. If
$M_c \subseteq U$ and $M_c$ is compact and connected (in particular nonempty), then $M_c$ is
homeomorphic to the $n$-torus $(\mathbb{R}/\mathbb{Z})^n$.

The hypotheses *compact* and *connected* on the level set, and its
containment in the open set where the derivatives are independent,
restore standard regularity assumptions that Knill elides; without them
the conclusion fails.

Source: V. I. Arnold, *Mathematical Methods of Classical Mechanics* (2nd ed., 1989), Theorem 49.A.1 (the standard modern reference). The result is due to Liouville (1855) for the local existence of action-angle coordinates and Arnold (1963) for the compact-connected-component topology. Listed as §45 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `liouville_arnold`. -/
public theorem_wanted liouville_arnold
    {n : ℕ} (F : Fin n → E n → ℝ) (U : Set (E n)) (_hU : IsOpen U)
    (_hLI : IsLiouvilleIntegrable F U)
    (c : Fin n → ℝ)
    (_hMc_sub : levelSet F c ⊆ U)
    (_hMc_compact : IsCompact (levelSet F c))
    (_hMc_connected : IsConnected (levelSet F c)) :
    Nonempty ((levelSet F c) ≃ₜ (Fin n → AddCircle (1 : ℝ)))

end LiouvilleArnold
end Geometry

end MathlibExt.Geometry.LiouvilleArnoldWanted
