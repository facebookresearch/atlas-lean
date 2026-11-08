/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Galois groups of random integer polynomials and van der Waerden's Conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.VanDerWaerdenConjecture` — annals_van_der_waerden_conjecture (manifest `manifests/problems/annals_van_der_waerden_conjecture.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.VanDerWaerdenConjectureWanted` namespace. Mathematical
statements are unchanged. Source: M. Bhargava, `Galois groups of random integer polynomials and van der Waerden's Conjecture`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-vanDerWaerdenConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.FieldTheory.PolynomialGaloisGroup

@[expose] public section

namespace MathlibExt.NumberTheory.VanDerWaerdenConjectureWanted
/-!
# Main Statement from Galois groups of random integer polynomials and van der Waerden's Conjecture

We formalise the statement of the main result from M. Bhargava,
`Galois groups of random integer polynomials and van der Waerden's Conjecture`,
Annals of Math, 201 (2) 2025.
-/

set_option autoImplicit false

namespace vanDerWaerdenConjecture

open Function Polynomial Filter

noncomputable section

/-- Definition of `Eₙ(H)` as the number of monic integer polynomials `f(x) = xⁿ + a₁ xⁿ⁻¹ + … aₙ` of
degree `n` with `|aᵢ| ≤ H` for all `i` such that the Galois group of `f` is not `Sₙ`.
-/
def E (n H : ℕ) : ℕ :=
  {p : ℤ[X] | p.Monic ∧ p.degree = n ∧ (∀ i < n, |p.coeff i| ≤ H) ∧
    Nat.card (p.map (algebraMap ℤ ℚ)).Gal < n.factorial}.ncard

/--
Statement of Theorem 1:

`Eₙ(H) = O(Hⁿ⁻¹)` for `n ≥ 3`.

The degree restriction is necessary: the theorem is false as stated for `n = 2`.
Source: M. Bhargava, `Galois groups of random integer polynomials and van der Waerden's Conjecture`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-vanDerWaerdenConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_van_der_waerden_conjecture`.
-/
public theorem_wanted theorem_1 (n : ℕ) (hn : 3 ≤ n) :
    (fun H ↦ (E n H : ℝ)) =O[atTop] (fun H ↦ (H ^ (n - 1) : ℝ))

end

end vanDerWaerdenConjecture

end MathlibExt.NumberTheory.VanDerWaerdenConjectureWanted
