/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Darboux's theorem (symplectic forms are locally standard)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.Darboux` — darboux (manifest `manifests/problems/darboux.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.DarbouxWanted` namespace. Mathematical
statements are unchanged. Source: J. G. Darboux, Sur le problème de Pfaff, Bull. Sci. Math. 6 (1882), 14-36, 49-68. Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.DarbouxWanted
namespace Geometry
namespace Darboux

/-!
# Darboux's theorem

§39 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Every
symplectic form on an open `U ⊆ ℝ^{2n}` is locally symplectomorphic to the
standard symplectic form `ω₀ = ∑_{i=1}^n dxᵢ ∧ dx_{n+i}`.

The local content lives entirely on open subsets of `ℝ^{2n}`; we formalize
Darboux against mathlib's normed-space differential-form machinery.

mathlib has continuous alternating maps, the exterior derivative `extDeriv`,
pullbacks of alternating forms, `Matrix.symplecticGroup`, and
`OpenPartialHomeomorph`, but no symplectic forms, no `ω₀` value, and no
Darboux theorem (`Analysis/Calculus/Darboux.lean` is the unrelated
derivative-IVT theorem). No formalization of Darboux's theorem was found in
any other proof assistant.
-/

open Set Function Matrix
open scoped ContDiff

/-- **Model space $\mathbb{R}^{2n}$ for Darboux's theorem.** For a natural number $n$, the model
space is $\mathbb{R}^{2n}$, the Euclidean space of dimension $2n$ with coordinates indexed by
$0, 1, \dots, 2n - 1$ and the standard inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- **Index of the $i$-th $p$-coordinate in $\mathbb{R}^{2n}$.** For $i \in \{0, \dots, n - 1\}$,
the index of the $i$-th $p$-coordinate among the coordinates $0, \dots, 2n - 1$ of
$\mathbb{R}^{2n}$ is $i$ itself. -/
def idxP {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- **Index of the $i$-th $q$-coordinate in $\mathbb{R}^{2n}$.** For $i \in \{0, \dots, n - 1\}$,
the index of the $i$-th $q$-coordinate among the coordinates $0, \dots, 2n - 1$ of
$\mathbb{R}^{2n}$ is $i + n$. -/
def idxQ {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val + n, by have := i.isLt; omega⟩

/-- **Darboux normal form.** Let $n$ be a natural number and let $e_0, \dots, e_{2n-1}$ be the
standard basis of $\mathbb{R}^{2n}$. A continuous alternating 2-form $\omega$ on $\mathbb{R}^{2n}$
is in Darboux normal form if for all $i, j \in \{0, \dots, n - 1\}$ we have
$\omega(e_i, e_{n+j}) = 1$ when $i = j$ and $0$ otherwise, $\omega(e_i, e_j) = 0$, and
$\omega(e_{n+i}, e_{n+j}) = 0$.

By antisymmetry these conditions determine the form uniquely: it is the standard symplectic form
$\omega_0 = \sum_i dx_i \wedge dx_{n+i}$. -/
def IsDarbouxNormal {n : ℕ} (α : E n [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxP i) (1 : ℝ),
          EuclideanSpace.single (idxQ j) (1 : ℝ)]
        = if i = j then (1 : ℝ) else 0) ∧
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxP i) (1 : ℝ),
          EuclideanSpace.single (idxP j) (1 : ℝ)] = 0) ∧
  (∀ i j : Fin n,
      α ![EuclideanSpace.single (idxQ i) (1 : ℝ),
          EuclideanSpace.single (idxQ j) (1 : ℝ)] = 0)

/-- **Symplectic 2-form fields.** Let $n$ be a natural number and $U$ a subset of
$\mathbb{R}^{2n}$. A field $\alpha$ of continuous alternating 2-forms on $\mathbb{R}^{2n}$ is
symplectic on $U$ if $\alpha$ is $C^\infty$ on $U$, its exterior derivative $d\alpha$ vanishes
at every point of $U$, and $\alpha$ is non-degenerate at every point of $U$: for every $x \in U$
and every nonzero $v \in \mathbb{R}^{2n}$ there is $w \in \mathbb{R}^{2n}$ with
$\alpha(x)(v, w) \neq 0$. -/
def IsSymplecticOn {n : ℕ}
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (U : Set (E n)) : Prop :=
  ContDiffOn ℝ ∞ α U ∧
  (∀ x ∈ U, extDeriv α x = 0) ∧
  (∀ x ∈ U, ∀ v : E n, v ≠ 0 → ∃ w : E n, α x ![v, w] ≠ 0)

/- **Darboux's theorem.** Every symplectic form on an open subset
`U ⊆ ℝ^{2n}` is locally symplectomorphic to the standard symplectic form
`ω₀`. Formally: for every `x ∈ U` there is a smooth local diffeomorphism
`φ` (`OpenPartialHomeomorph`, smooth in both directions) whose source lies
in `U` and contains `x`, such that on the target the pullback of `α` by
`φ⁻¹` is in Darboux normal form (and hence equals `ω₀`) at every point. -/
/-- **Darboux's theorem.** Let $n$ be a natural number, let $U$ be an open subset of the model
space $\mathbb{R}^{2n}$, and let $\alpha$ be a field of continuous alternating 2-forms on
$\mathbb{R}^{2n}$ that is symplectic on $U$. Then for every $x \in U$ there is an open partial
homeomorphism $\varphi$ of $\mathbb{R}^{2n}$ whose source contains $x$ and is contained in $U$, such
that $\varphi$ is $C^\infty$ on its source, $\varphi^{-1}$ is $C^\infty$ on its target, and for
every $z$ in the target the pullback of $\alpha(\varphi^{-1}(z))$ by the derivative
$D\varphi^{-1}(z)$, namely
$(v, w) \mapsto \alpha(\varphi^{-1}(z))(D\varphi^{-1}(z)\, v, D\varphi^{-1}(z)\, w)$, is in Darboux
normal form.

Source: J. G. Darboux, Sur le problème de Pfaff, Bull. Sci. Math. 6 (1882), 14-36, 49-68. Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `darboux`. -/
public theorem_wanted darboux {n : ℕ} {U : Set (E n)} (_hU : IsOpen U)
    (α : E n → E n [⋀^Fin 2]→L[ℝ] ℝ) (_hα : IsSymplecticOn α U)
    {x : E n} (_hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → E n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : E n → E n) φ.target ∧
      ∀ z ∈ φ.target,
        IsDarbouxNormal
          ((α (φ.symm z)).compContinuousLinearMap
            (fderiv ℝ (φ.symm : E n → E n) z))

end Darboux
end Geometry

end MathlibExt.Geometry.DarbouxWanted
