/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Good Locally Testable Codes

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.GoodLTCodes` — annals_good_lt_codes (manifest `manifests/problems/annals_good_lt_codes.toml`, rev 1, submitter Thomas Browning, Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.GoodLTCodesWanted` namespace. Mathematical
statements are unchanged. Source: I. Dinur, S. Evra, R. Livne, A. Lubotzky, and S. Mozes, `Good Locally Testable Codes`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-GoodLTCodes.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.GoodLTCodesWanted
/-!
# Main Statement from Good Locally Testable Codes

We formalise the statement of the main result from I. Dinur, S. Evra, R. Livne,
A. Lubotzky, and S. Mozes, `Good Locally Testable Codes`, Annals of Math, 203 (2) 2026.
-/

set_option autoImplicit false

namespace GoodLTC

open NNReal

variable (n : ℕ)

local notation "𝔽₂ⁿ" => Fin n → ZMod 2

/-- A binary code of length `n` is a subspace of `(𝔽₂)ⁿ`. -/
abbrev BinaryCode : Type := Submodule (ZMod 2) 𝔽₂ⁿ

variable {n} (C : BinaryCode n)

/-- The dimension of a binary code is its dimension as an `𝔽₂` subspace. -/
noncomputable def dim : ℕ := Module.finrank (ZMod 2) C

/-- The rate of a binary code is its dimension divided by its length. -/
noncomputable def rate : ℝ := dim C / n

/-- The distance of a binary code `C` is the minimum of the Hamming distances between distinct
codewords. -/
noncomputable def distance : ℕ :=
  sInf {d | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = d}

/-- The normalised distance of a binary code `C` is its distance divided by its length. -/
noncomputable def normalisedDistance : ℝ := distance C / n

/-- The distance from a word `f` to a binary code `C` is the Hamming distance from `f` to the
closest codeword in `C`. -/
noncomputable def distanceFrom (f : 𝔽₂ⁿ) : ℕ :=
  sInf {d | ∃ c ∈ C, hammingNorm (f - c) = d}

/-- The normalised distance from a word `f` to a binary code `C` is the Hamming distance from `f`
to the closest codeword in `C` divided by its length. -/
noncomputable def normalisedDistanceFrom (f : 𝔽₂ⁿ) : ℝ≥0 := ⟨distanceFrom C f / n, by positivity⟩

/-- A family of codes `{Cᵢ}_{i ∈ ℕ}` of lengths `nᵢ → ∞` is called good if there exists `ε > 0`
such that the rate and normalised distance of each `Cᵢ` are bounded from below by `ε`. -/
def IsGood {n : ℕ → ℕ} (𝒞 : (i : ℕ) → BinaryCode (n i)) : Prop :=
  Filter.Tendsto n Filter.atTop Filter.atTop ∧
    ∃ ε > 0, ∀ i, ε ≤ rate (𝒞 i) ∧ ε ≤ normalisedDistance (𝒞 i)

variable (n) in
/-- The type of all `q`-element (or less) subsets `S ⊆ Fin n`. -/
abbrev cardLE (q : ℕ) : Type :=
  {S : Set (Fin n) // S.ncard ≤ q}

/-- A binary code `C ⊆ (𝔽₂)ⁿ` is `κ`-locally testable with `q` queries if there is a distribution
over a collection of `q`-element (or less) subsets `S ⊆ Fin n` such that each subset `S` is
associated with a set `V_S ⊆ 𝔽₂^S` of allowed local views, and such that the following hold:
* If `f ∈ C` then for every `S`, `f|_S ∈ V_S`.
* For every `f ∈ (𝔽₂)ⁿ`, `ℙ_S[f|_S ∉ V_S] ≥ κ * dist(f, C)`.

This is Definition 2.3 in `Locally Testable Codes with constant rate, distance, and locality` by
the same authors. This probability distribution formulation is also mentioned immediately after
Definition 1.1 in the original paper `Good Locally Testable Codes`. -/
structure LTC (q : ℕ) (κ : ℝ≥0) (C : BinaryCode n) where
  /-- The probability distribution on the collection of `q`-element (or less) subsets of `Fin n`. -/
  prob : PMF (cardLE n q)
  /-- The set `V_S ⊆ 𝔽₂^S` of allowed local views associated to a given subset `S ⊆ Fin n`. -/
  views (S : cardLE n q) : Set (S.val → ZMod 2)
  cond1 (f : 𝔽₂ⁿ) (hf : f ∈ C) (S : cardLE n q) : Set.domRestrict S f ∈ views S
  cond2 (f : 𝔽₂ⁿ) :
    prob.toMeasure {S | Set.domRestrict S f ∉ views S} ≥ κ * normalisedDistanceFrom C f

/--
Statement of Theorem 1.2:

There exist good locally testable codes (the source's explicitness is not formalized) (for every rate `ρ < 1`).
Source: I. Dinur, S. Evra, R. Livne, A. Lubotzky, and S. Mozes, `Good Locally Testable Codes`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-GoodLTCodes.lean Via leanprover/lean-eval@38361be, problem `annals_good_lt_codes`.
-/
public theorem_wanted theorem_1_2 (ρ : ℝ≥0) (hρ : ρ < 1) :
    ∃ q, ∃ κ ≠ 0, ∃ (n : ℕ → ℕ), ∃ (𝒞 : (i : ℕ) → BinaryCode (n i)), IsGood 𝒞 ∧
      ∀ i, Nonempty (LTC q κ (𝒞 i)) ∧ rate (𝒞 i) ≥ ρ

end GoodLTC

end MathlibExt.Combinatorics.GoodLTCodesWanted
