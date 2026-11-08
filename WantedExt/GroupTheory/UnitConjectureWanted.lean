/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to the unit conjecture for group rings

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.UnitConjecture` — annals_unit_conjecture (manifest `manifests/problems/annals_unit_conjecture.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.UnitConjectureWanted` namespace. Mathematical
statements are unchanged. Source: G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.UnitConjectureWanted
/-!
# Main Statement from A counterexample to the unit conjecture for group rings

We formalise the statement of the main result from G. Gardam,
`A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

noncomputable section

namespace UnitConjecture

/-- The two generators of the group `P` defined in Theorem A of the paper. -/
inductive generators where
  | a
  | b

/-- The first generator of the group `P` defined in Theorem A of the paper. -/
def a : FreeGroup generators := .of generators.a

/-- The second generator of the group `P` defined in Theorem A of the paper. -/
def b : FreeGroup generators := .of generators.b

/-- The relations defining the group `P` defined in Theorem A of the paper. -/
def relations : Set (FreeGroup generators) :=
  {b⁻¹ * a ^ 2 * b * a ^ 2, a⁻¹ * b ^ 2 * a * b ^ 2}

/-- The group `P` defined in Theorem A of the paper. -/
def P := PresentedGroup relations
deriving Coe (FreeGroup generators), Group

/-- The element `x` defined in Theorem A of the paper. -/
def x : P := a ^ 2

/-- The element `y` defined in Theorem A of the paper. -/
def y : P := b ^ 2

/-- The element `z` defined in Theorem A of the paper. -/
def z : P := (a * b) ^ 2

/-- The group ring `𝔽₂[P]` defined in Theorem A of the paper. -/
abbrev R := MonoidAlgebra (ZMod 2) P

instance : Coe P R where
  coe := MonoidAlgebra.of (ZMod 2) P

/-- The element `p` defined in Theorem A of the paper. -/
def p : R := (1 + x) * (1 + y) * (1 + z⁻¹)

/-- The element `q` defined in Theorem A of the paper. -/
def q : R := x⁻¹ * y⁻¹ + x + y⁻¹ * z + z

/-- The element `r` defined in Theorem A of the paper. -/
def r : R := 1 + x + y⁻¹ * z + x * y * z

/-- The element `s` defined in Theorem A of the paper. -/
def s : R := 1 + (x + x⁻¹ + y + y⁻¹) * z⁻¹

/-- The nontrivial unit defined in Theorem A of the paper. -/
def u : R := p + q * a + r * b + s * (a * b)

/--
Statement of Theorem A:

Let P be the torsion-free group defined by the presentation
`⟨a,b | b⁻¹a²b = a⁻², a⁻¹b²a = b⁻²⟩`, and set `x = a²`, `y = b²`, `z = (ab)²`. Set
`p = (1 + x)(1 + y)(1 + z⁻¹)`, `q = x⁻¹y⁻¹ + x + y⁻¹z + z`,
`r = 1 + x + y⁻¹z + xyz`, `s = 1 + (x + x⁻¹ + y + y⁻¹)z⁻¹`.
Then `p + qa + rb + sab` is a non-trivial unit in the group ring `𝔽₂[P]`.
Source: G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_unit_conjecture`.
-/
public theorem_wanted theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g

end UnitConjecture

end

end MathlibExt.GroupTheory.UnitConjectureWanted
