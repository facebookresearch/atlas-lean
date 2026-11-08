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

/-- The model space `ℝ^{2n}`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- The "p" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxP {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The "q" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxQ {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val + n, by have := i.isLt; omega⟩

/-- Standard **Poisson bracket** on `ℝ^{2n}` for the symplectic form
`ω₀ = ∑ᵢ dpᵢ ∧ dqᵢ`:
`{F, G}(x) = ∑ᵢ ((∂F/∂pᵢ)(x)(∂G/∂qᵢ)(x) − (∂F/∂qᵢ)(x)(∂G/∂pᵢ)(x))`. -/
noncomputable def poissonBracket {n : ℕ} (F G : E n → ℝ) (x : E n) : ℝ :=
  ∑ i : Fin n,
    (fderiv ℝ F x (EuclideanSpace.single (idxP i) (1 : ℝ)) *
        fderiv ℝ G x (EuclideanSpace.single (idxQ i) (1 : ℝ))
      - fderiv ℝ F x (EuclideanSpace.single (idxQ i) (1 : ℝ)) *
        fderiv ℝ G x (EuclideanSpace.single (idxP i) (1 : ℝ)))

/-- A tuple `F : Fin n → (E n → ℝ)` is **Liouville integrable on `U`**
(an open subset of `ℝ^{2n}`) if each component is smooth on `U`, they
pairwise Poisson-commute on `U`, and their Fréchet derivatives are
linearly independent at every point of `U`. -/
def IsLiouvilleIntegrable {n : ℕ} (F : Fin n → E n → ℝ) (U : Set (E n)) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (F i) U) ∧
  (∀ i j, ∀ x ∈ U, poissonBracket (F i) (F j) x = 0) ∧
  (∀ x ∈ U, LinearIndependent ℝ (fun i => fderiv ℝ (F i) x))

/-- The common level set `{x : F₁(x) = c₁, …, F_n(x) = c_n}`. -/
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
/-- Source: V. I. Arnold, *Mathematical Methods of Classical Mechanics* (2nd ed., 1989), Theorem 49.A.1 (the standard modern reference). The result is due to Liouville (1855) for the local existence of action-angle coordinates and Arnold (1963) for the compact-connected-component topology. Listed as §45 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `liouville_arnold`. -/
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
