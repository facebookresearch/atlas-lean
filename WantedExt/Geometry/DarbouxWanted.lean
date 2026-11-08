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

/-- The model space `ℝ^{2n}` for the local Darboux theorem. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

/-- The "p" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxP {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The "q" coordinate index `i ∈ Fin n` viewed in `Fin (2n)`. -/
def idxQ {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨i.val + n, by have := i.isLt; omega⟩

/-- A continuous alternating 2-form on `E n = ℝ^{2n}` is in **Darboux normal
form** if its values on the standard basis are the Liouville symplectic
values: `ω(eP_i, eQ_j) = δ_{ij}`, and `ω(eP_i, eP_j) = ω(eQ_i, eQ_j) = 0`.
By antisymmetry these conditions uniquely determine the form (it is the
standard symplectic form `ω₀ = ∑_i dxᵢ ∧ dx_{n+i}`). -/
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

/-- A 2-form field `α` on an open set `U ⊆ ℝ^{2n}` is **symplectic** on `U`
if it is smooth on `U`, closed on `U` (`dα = 0`), and pointwise
non-degenerate. -/
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
/-- Source: J. G. Darboux, Sur le problème de Pfaff, Bull. Sci. Math. 6 (1882), 14-36, 49-68. Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `darboux`. -/
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
