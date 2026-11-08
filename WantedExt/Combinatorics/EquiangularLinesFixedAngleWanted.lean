/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equiangular lines with a fixed angle

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.EquiangularLinesFixedAngle` — annals_equiangular_lines_fixed_angle (manifest `manifests/problems/annals_equiangular_lines_fixed_angle.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted` namespace. Mathematical
statements are unchanged. Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-EquiangularLinesFixedAngle.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

@[expose] public section

namespace MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted
/-!
# Main Statement from Equiangular lines with a fixed angle

We formalise the statement of the main result from Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and
Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

namespace EquiangularLinesFixedAngle

open Filter

open scoped RealInnerProductSpace

/-- A set of unit vectors in `d`-dimensional euclidean space with pairwise inner product `±α`.
See the third paragraph of the introduction. -/
structure EquiangularLines (α : ℝ) (d : ℕ) where
  /-- The set of unit vectors in `d`-dimensional Euclidean space. -/
  carrier : Set (EuclideanSpace ℝ (Fin d))
  norm : ∀ x ∈ carrier, ‖x‖ = 1
  angle : carrier.Pairwise fun x y ↦ |⟪x, y⟫| = α

/-- The maximum number of lines in `d`-dimensional euclidean space through the origin with
pairwise angle `arccos(α)`. See the third paragraph of the introduction. We take the
supremum in `ℕ` here. Note that the carrier sets `E.carrier` are bounded above since
`N_α(d) ≤ binom(d+1,2)` by Gerzon (also mentioned in the introduction). -/
noncomputable def N (α : ℝ) (d : ℕ) : ℕ := ⨆ E : EquiangularLines α d, E.carrier.ncard

open Classical in
/-- The spectral radius order of a positive real number. See Definition 1.1. -/
noncomputable def spectralRadiusOrder (lambda : ℝ) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | ∃ G : SimpleGraph (Fin k), spectralRadius ℝ (G.adjMatrix ℝ) = .ofReal lambda}, k

/-
Note that if `λ > 0` then `spectralRadiusOrder λ` cannot be `0` or `1`, because the spectral
radius of the adjacency matrix of any graph with no edges is `0`. So our subtractions
and divisions below are not pathological.
-/

/--
Statement of Theorem 1.2 (Main theorem):

Fix `α ∈ (0, 1)`. Let `λ = (1 − α)/(2α)` and `k = k(λ)` be its spectral radius order.
The maximum number `N_α(d)` of equiangular lines in `ℝᵈ` with common angle `arccos α` satisfies
(a) `N_α(d) = ⌊k(d − 1)/(k − 1)⌋` for all sufficiently large `d > d₀(α)` if `k < ∞`;
(b) `N_α(d) = d + o(d)` as `d → ∞` if `k = ∞`.
Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-EquiangularLinesFixedAngle.lean Via leanprover/lean-eval@38361be, problem `annals_equiangular_lines_fixed_angle`.
-/
public theorem_wanted theorem_1_2 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    let k := spectralRadiusOrder ((1 - α) / (2 * α))
    (k < ⊤ → ∀ᶠ d in atTop, N α d = ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
    (k = ⊤ → ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d)

end EquiangularLinesFixedAngle

end MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted
