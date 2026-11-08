/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A reverse Minkowski theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ReverseMinkowski` — annals_reverse_minkowski (manifest `manifests/problems/annals_reverse_minkowski.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ReverseMinkowskiWanted` namespace. Mathematical
statements are unchanged. Source: O. Regev, N. Stephens-Davidowitz, `A reverse Minkowski theorem`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-ReverseMinkowski.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ReverseMinkowskiWanted
/-!
# Main Statement from A reverse Minkowski theorem

We formalise the statement of the main result from O. Regev, N. Stephens-Davidowitz,
`A reverse Minkowski theorem`, Annals of Math, 199 (1) 2024.
-/

set_option autoImplicit false

namespace ReverseMinkowski

open Module Real Matrix

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The Gaussian mass `ρ_s (ℒ)` is the function defined after the statement of Theorem 1.2. -/
noncomputable def ρ (s : ℝ) (ℒ : Submodule ℤ ℝⁿ) : ℝ := ∑' y : ℒ, rexp (- π * ‖y‖ ^ 2 / s ^ 2)

/-- For `ℤ`-lattice of rank `m`, define an `n × m` matrix whose columns are basis elements of `ℒ`.
-/
noncomputable def B (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] :
    Matrix (Fin n) (Fin (finrank ℤ ℒ)) ℝ := (of fun i ↦ (finBasis ℤ ℒ) i).transpose

/-- The determinant of a `ℤ`-lattice of arbitrary rank is the square root of the determinant of
`B^T * B`, where `B`is the basis matrix defined above. -/
noncomputable def determinant (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] : ℝ :=
  √ ((B ℒ).transpose * B ℒ).det

/--
Statement of Theorem 1.2 (Reverse Minkowski Theorem):

For any lattice `ℒ ⊆ ℝ^n` with determinant greater or equal to `1` for all sublattices `ℒ'` of `ℒ`,
`ρ_{1/t}(ℒ) ≤ 3/2` where `t = 10 (log n + 2)`.
Source: O. Regev, N. Stephens-Davidowitz, `A reverse Minkowski theorem`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-ReverseMinkowski.lean Via leanprover/lean-eval@38361be, problem `annals_reverse_minkowski`.
-/
public theorem_wanted theorem_1_2 (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (h : ∀ ℒ' (_hℒℒ' : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], determinant ℒ' ≥ 1) :
    let t : ℝ := 10 * (log n + 2)
    ρ (1 / t) ℒ ≤ 3 / 2

end ReverseMinkowski

end MathlibExt.NumberTheory.ReverseMinkowskiWanted
