/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On Zagier-Hoffman's conjectures in positive characteristic

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ZagierHoffmanPositiveChar` — annals_zagier_hoffman_positive_char (manifest `manifests/problems/annals_zagier_hoffman_positive_char.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted` namespace. Mathematical
statements are unchanged. Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted
/-!
# Main Statements from On Zagier-Hoffman's conjectures in positive characteristic

We formalise the statements of the main results from T. N. Dac,
`On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021.

## Implementation Details

Throughout the definitions and statements, we reindex the `i`'s so that they run from `0`
to `r - 1` rather than from `1` to `r`.
-/

set_option autoImplicit false

namespace ZagierHoffmanPositiveChar

open NNReal Polynomial RatFunc

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The set of `r`-tuples `(a_1,..., a_r)` of monic polynomials over the finite field `F`, such that
`deg a_1 > deg a_2 > ... > deg a_r`. -/
abbrev monicStrictAntiNatDegree (r : ℕ) :=
  {a : Fin r → Polynomial F // StrictAnti (Polynomial.natDegree ∘ a) ∧ ∀ i, (a i).Monic}

/-- Multiple zeta value (MZV) `ζ_A (s_1, ..., s_r)` in positive characteristic. -/
noncomputable def ζ_A {r : ℕ} (𝔰 : Fin r → ℕ+) : CompletionAtInfty F :=
  ∑' a : monicStrictAntiNatDegree F r, (∏ i, a.val i ^ (𝔰 i : ℕ))⁻¹

/-- `𝔖_w` is the set of `r`-tuples of positive natural numbers whose sum is `w`. -/
def 𝔖_w (w : ℕ) (r : ℕ) : Set (Fin r → ℕ+) := {𝔰 : Fin r → ℕ+ | ∑ i : Fin r, (𝔰 i : ℕ) = w}

/-- The multiple zeta value function `ζ_A 𝔰` is said to have weight `w` if `∑ i : Fin r, 𝔰 i = w`.
Below, we define the set of multiple zeta values (MZVs) `ζ_A (s_1,..., s_r)` of weight `w`. -/
def ζ_A_weight (w : ℕ) (r : ℕ) : Set (CompletionAtInfty F) := {ζ_A F 𝔰 | 𝔰 ∈ 𝔖_w w r}

/-- For `w ∈ ℕ`, define `𝒵 w` to be the vector space over the field of rational functions over `F`,
spanned by the MZVs of weight `w`. Note that in the paper, `RatFunc F` is denoted by `K`. -/
noncomputable def 𝒵 (w : ℕ) : Submodule (RatFunc F) (CompletionAtInfty F) :=
  Submodule.span (RatFunc F) (⋃ r, ζ_A_weight F w r)

/-- Let `q` be the size of the finite field `F`. `𝒯_aux w r` is the set of `ζ_A(s_1, ..., s_r)` of
weight `w`, with `1 ≤ s_i ≤ q` for `1 ≤ i ≤ r − 1` and `1 ≤ s_r < q`. -/
def 𝒯_aux (w : ℕ) (r : ℕ+) : Set (CompletionAtInfty F) :=
  let q := Nat.card F
  let 𝔖'_w := {𝔰 ∈ 𝔖_w w r | (∀ i : Fin r, i < (r - 1 : ℕ) → 𝔰 i ≤ q) ∧ 𝔰 ⟨r - 1, by simp⟩ < q}
  {ζ_A F s | s ∈ 𝔖'_w}

/-- Let `q` be the size of the finite field `F`. `𝒯_w` is the set of `ζ_A(s_1,..., s_r)` of weight
`w`, with `1 ≤ s_i ≤ q` for `1 ≤ i ≤ r − 1` and `1 ≤ s_r < q`, as `r` varies. -/
def 𝒯 (w : ℕ) : Set (CompletionAtInfty F) := ⋃ r : ℕ+, 𝒯_aux F w r

/-- Let `q` be the size of the finite field `F`. `𝒯0_aux` is the set of `ζ_A(s_1,..., s_r)` of
weight `w`, with `1 ≤ s_i < q` for all `i`. -/
def 𝒯0_aux (w : ℕ) (r : ℕ+) : Set (CompletionAtInfty F) :=
  let q := Nat.card F
  let 𝔖'_w := {𝔰 ∈ 𝔖_w w r | ∀ i, 𝔰 i < q}
  {ζ_A F s | s ∈ 𝔖'_w}

/-- Let `q` be the size of the finite field `F`. `𝒯0 w` is the set of `ζ_A(s_1,..., s_r)` of weight
`w`, with `1 ≤ s_i < q` for all `i`, as `r` varies. -/
def 𝒯0 (w : ℕ) : Set (CompletionAtInfty F) := ⋃ r : ℕ+, 𝒯0_aux F w r

/-- The sequence `d(w)` from Conjecture 1.5 and Theorems A and D. -/
noncomputable def d (w : ℕ) : ℕ :=
  let q := Nat.card F
  if w = 0 then 1
  else if w ≤ q - 1 then 2 ^ (w - 1)
  else if w = q then 2 ^ (w - 1) - 1
  else ∑ i ∈ Finset.range q, d (w - (i + 1))

/--
Statement of Theorem A (Brown's theorem in positive characteristic):

Let `w ∈ ℕ`, where `ℕ := {1,2,...}`. Then every MZV of weight `w` can be written as a `K`-linear
combination of MZV's in the set `𝒯_w`. In particular, `dim 𝒵_w ≤ d(w)`.
Note that `K` in the paper is `RatFunc F`.
Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_A (w : ℕ+) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≤ d F w

/--
Statement of Theorem B:

Let `w ∈ ℕ`, where `ℕ := {1,2,...}`. MZVs of weight `w` in `𝒯0 w` are all linearly independent over
`K`. In particular, `dim 𝒵 w ≥ |𝒯0 w|`. Note that `K` in the paper is `RatFunc F`.
Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_B (w : ℕ+) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≥ Set.ncard (𝒯0 F w)

/--
Statement of Theorem D:

Let `w ∈ ℕ+` with `w ≤ 2q − 2`. Then `𝒯 w` is a `K`-basis for `𝒵 w`. In particular,
`dim_K (𝒵 w) = d(w)`. Note that `K` in the paper is `RatFunc F`.

Note: Theorem A establishes that `𝒯 w` spans `𝒵 w`. So to prove `𝒯 w` is a `K`-basis for `𝒵 w`, we
only need to show that `𝒯 w` are linearly independent in `𝒵 w`.
Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_D (w : ℕ+) (hw : w ≤ 2 * Nat.card F - 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) = d F w

end ZagierHoffmanPositiveChar

end MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted
