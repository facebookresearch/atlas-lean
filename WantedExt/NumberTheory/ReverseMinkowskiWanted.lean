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

/-- **Gaussian mass of a lattice.** For a real number $s$ and a $\mathbb{Z}$-submodule
$\mathcal{L} \subseteq \mathbb{R}^n$, the Gaussian mass of $\mathcal{L}$ at parameter $s$ is
$\rho_s(\mathcal{L}) = \sum_{y \in \mathcal{L}} e^{-\pi \|y\|^2 / s^2}$, where $\|y\|$ is the
Euclidean norm.

The sum is taken to be $0$ when the series is not summable. -/
noncomputable def ρ (s : ℝ) (ℒ : Submodule ℤ ℝⁿ) : ℝ := ∑' y : ℒ, rexp (- π * ‖y‖ ^ 2 / s ^ 2)

/-- **Basis matrix of a lattice.** Let $\mathcal{L} \subseteq \mathbb{R}^n$ be a discrete
$\mathbb{Z}$-submodule of rank $m$. Its basis matrix $B(\mathcal{L})$ is the real
$n \times m$ matrix whose $j$-th column is the $j$-th vector of a fixed, arbitrarily chosen
$\mathbb{Z}$-basis of $\mathcal{L}$.
-/
noncomputable def B (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] :
    Matrix (Fin n) (Fin (finrank ℤ ℒ)) ℝ := (of fun i ↦ (finBasis ℤ ℒ) i).transpose

/-- **Determinant of a lattice.** For a discrete $\mathbb{Z}$-submodule
$\mathcal{L} \subseteq \mathbb{R}^n$ with basis matrix $B = B(\mathcal{L})$ (the real matrix whose
columns form a fixed $\mathbb{Z}$-basis of $\mathcal{L}$), the determinant of $\mathcal{L}$ is
$\det(\mathcal{L}) = \sqrt{\det(B^{T} B)}$. -/
noncomputable def determinant (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] : ℝ :=
  √ ((B ℒ).transpose * B ℒ).det

/--
**Reverse Minkowski theorem.** Let $\mathcal{L} \subseteq \mathbb{R}^n$ be a full-rank lattice, that
is, a discrete subgroup of $\mathbb{R}^n$ that spans $\mathbb{R}^n$, such that every subgroup
$\mathcal{L}' \subseteq \mathcal{L}$ (a lattice of possibly lower rank) has determinant
$\det(\mathcal{L}') \ge 1$. Let $t = 10(\log n + 2)$, where $\log$ is the natural logarithm. Then
the Gaussian mass of $\mathcal{L}$ at parameter $1/t$ satisfies
$\rho_{1/t}(\mathcal{L}) = \sum_{y \in \mathcal{L}} e^{-\pi t^2 \|y\|^2} \le 3/2$, where
$\|y\|$ is the Euclidean norm.

Source: O. Regev, N. Stephens-Davidowitz, `A reverse Minkowski theorem`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-ReverseMinkowski.lean Via leanprover/lean-eval@38361be, problem `annals_reverse_minkowski`.
-/
public theorem_wanted theorem_1_2 (ℒ : Submodule ℤ ℝⁿ) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (h : ∀ ℒ' (_hℒℒ' : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], determinant ℒ' ≥ 1) :
    let t : ℝ := 10 * (log n + 2)
    ρ (1 / t) ℒ ≤ 3 / 2

end ReverseMinkowski

end MathlibExt.NumberTheory.ReverseMinkowskiWanted
