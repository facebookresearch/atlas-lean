/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On a conjecture of Marton

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.ConjectureOfMarton` — annals_conjecture_of_marton (manifest `manifests/problems/annals_conjecture_of_marton.toml`, rev 1, submitter Thomas Browning, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.ConjectureOfMartonWanted` namespace. Mathematical
statements are unchanged. Source: W. T. Gowers, B. Green, F. Manners, and T. Tao, `On a conjecture of Marton`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-ConjectureOfMarton.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Additive.CovBySMul

@[expose] public section

namespace MathlibExt.Combinatorics.ConjectureOfMartonWanted
/-!
# Main Statement from On a conjecture of Marton

We formalise the statement of the main result from W. T. Gowers, B. Green, F. Manners, and T. Tao,
`On a conjecture of Marton`, Annals of Math, 201 (2) 2025.
-/

set_option autoImplicit false

namespace ConjectureOfMarton

open Pointwise

variable (n : ℕ)

/-- `F n` is the finite vector space `(𝔽₂)ⁿ`. -/
abbrev F := Fin n → ZMod 2

/--
Statement of Theorem 1.2:

Suppose that `A ⊂ (𝔽₂)ⁿ` is a set with `|A + A| ≤ K|A|`. Then `A` is covered by at most `2 K ^ 12`
cosets of some subgroup `H ≤ (𝔽₂)ⁿ` of size at most `|A|`.

Note that the set `A` must be nonempty, but this is left implicit in the paper.
Source: W. T. Gowers, B. Green, F. Manners, and T. Tao, `On a conjecture of Marton`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-ConjectureOfMarton.lean Via leanprover/lean-eval@38361be, problem `annals_conjecture_of_marton`.
-/
public theorem_wanted theorem_1_2 (A : Set (F n)) (K : ℝ) (h₀ : A.Nonempty) (h : (A + A).ncard ≤ K * A.ncard) :
    ∃ H : AddSubgroup (F n), Nat.card H ≤ A.ncard ∧ CovByVAdd (F n) (2 * K ^ 12) A H

end ConjectureOfMarton

end MathlibExt.Combinatorics.ConjectureOfMartonWanted
