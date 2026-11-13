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

/-- **Binary code.** A binary code of length $n$ is a linear subspace of $\mathbb{F}_2^n$,
the vector space of words of length $n$ over the two-element field $\mathbb{F}_2$. -/
abbrev BinaryCode : Type := Submodule (ZMod 2) 𝔽₂ⁿ

variable {n} (C : BinaryCode n)

/-- **Dimension of a binary code.** The dimension of a binary code
$C \subseteq \mathbb{F}_2^n$ is its dimension as a vector space over $\mathbb{F}_2$. -/
noncomputable def dim : ℕ := Module.finrank (ZMod 2) C

/-- **Rate of a binary code.** The rate of a binary code $C \subseteq \mathbb{F}_2^n$ is its
dimension over $\mathbb{F}_2$ divided by its length $n$, as a real number; it is $0$ when
$n = 0$. -/
noncomputable def rate : ℝ := dim C / n

/-- **Minimum distance of a binary code.** The distance of a binary code
$C \subseteq \mathbb{F}_2^n$ is the smallest Hamming weight (number of nonzero coordinates) of
a nonzero codeword of $C$, and is $0$ if $C = \{0\}$.

When $C \neq \{0\}$, since $C$ is linear, this is the minimum Hamming distance between two
distinct codewords. -/
noncomputable def distance : ℕ :=
  sInf {d | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = d}

/-- **Normalised distance of a binary code.** The normalised distance of a binary code
$C \subseteq \mathbb{F}_2^n$ is its distance divided by its length $n$, as a real number; it is
$0$ when $n = 0$. -/
noncomputable def normalisedDistance : ℝ := distance C / n

/-- **Distance from a word to a binary code.** For a binary code $C \subseteq \mathbb{F}_2^n$
and a word $f \in \mathbb{F}_2^n$, the distance from $f$ to $C$ is the minimum, over all
codewords $c \in C$, of the Hamming distance between $f$ and $c$, that is, the number of
coordinates in which $f$ and $c$ differ. -/
noncomputable def distanceFrom (f : 𝔽₂ⁿ) : ℕ :=
  sInf {d | ∃ c ∈ C, hammingNorm (f - c) = d}

/-- **Normalised distance from a word to a binary code.** For a binary code
$C \subseteq \mathbb{F}_2^n$ and a word $f \in \mathbb{F}_2^n$, the normalised distance from $f$
to $C$ is the distance from $f$ to $C$ (the Hamming distance from $f$ to a closest codeword)
divided by the length $n$, as a nonnegative real number; it is $0$ when $n = 0$. -/
noncomputable def normalisedDistanceFrom (f : 𝔽₂ⁿ) : ℝ≥0 := ⟨distanceFrom C f / n, by positivity⟩

/-- **Good family of codes.** Let $(n_i)_{i \in \mathbb{N}}$ be natural numbers and, for each $i$,
let $C_i \subseteq \mathbb{F}_2^{n_i}$ be a binary code of length $n_i$. The family $(C_i)$ is
good if $n_i \to \infty$ as $i \to \infty$ and there is a real number $\varepsilon > 0$ such
that for every $i$ both the rate and the normalised distance of $C_i$ are at least
$\varepsilon$. -/
def IsGood {n : ℕ → ℕ} (𝒞 : (i : ℕ) → BinaryCode (n i)) : Prop :=
  Filter.Tendsto n Filter.atTop Filter.atTop ∧
    ∃ ε > 0, ∀ i, ε ≤ rate (𝒞 i) ∧ ε ≤ normalisedDistance (𝒞 i)

variable (n) in
/-- **Subsets with at most $q$ elements.** For natural numbers $n$ and $q$, this is the
collection of all subsets $S \subseteq \{0, 1, \dots, n - 1\}$ with at most $q$ elements. -/
abbrev cardLE (q : ℕ) : Type :=
  {S : Set (Fin n) // S.ncard ≤ q}

/-- **Locally testable code.** Let $C \subseteq \mathbb{F}_2^n$ be a binary code, let $q$ be a
natural number and let $\kappa \ge 0$ be a real number. A $\kappa$-local tester for $C$ with
$q$ queries consists of a probability distribution on the subsets
$S \subseteq \{0, 1, \dots, n - 1\}$ with at most $q$ elements, together with, for each such
$S$, a set $V_S \subseteq \mathbb{F}_2^S$ of allowed local views, such that:
* if $f \in C$, then $f|_S \in V_S$ for every such $S$;
* for every $f \in \mathbb{F}_2^n$, the probability that $f|_S \notin V_S$ for a random $S$ is
  at least $\kappa$ times the normalised distance from $f$ to $C$.

The code $C$ is $\kappa$-locally testable with $q$ queries exactly when such a tester exists.

Source: Definition 2.3 in `Locally Testable Codes with constant rate, distance, and locality` by
I. Dinur, S. Evra, R. Livne, A. Lubotzky and S. Mozes. This probability distribution formulation
is also mentioned immediately after Definition 1.1 in the original paper `Good Locally Testable
Codes`. -/
structure LTC (q : ℕ) (κ : ℝ≥0) (C : BinaryCode n) where
  /-- The probability distribution on the collection of `q`-element (or less) subsets of `Fin n`. -/
  prob : PMF (cardLE n q)
  /-- The set `V_S ⊆ 𝔽₂^S` of allowed local views associated to a given subset `S ⊆ Fin n`. -/
  views (S : cardLE n q) : Set (S.val → ZMod 2)
  cond1 (f : 𝔽₂ⁿ) (hf : f ∈ C) (S : cardLE n q) : Set.domRestrict S f ∈ views S
  cond2 (f : 𝔽₂ⁿ) :
    prob.toMeasure {S | Set.domRestrict S f ∉ views S} ≥ κ * normalisedDistanceFrom C f

/--
**Good locally testable codes of every rate below one.** For every real number $\rho$ with
$0 \le \rho < 1$ there exist a natural number $q$, a real number $\kappa > 0$, lengths
$n_i \in \mathbb{N}$ and binary codes $C_i$ of length $n_i$ for $i \in \mathbb{N}$ such that the
family $(C_i)_{i \in \mathbb{N}}$ is good and, for every $i$, the code $C_i$ is $\kappa$-locally
testable with $q$ queries and has rate at least $\rho$.

The source's theorem also asserts that the codes are explicit; explicitness is not formalized.

Source: I. Dinur, S. Evra, R. Livne, A. Lubotzky, and S. Mozes, `Good Locally Testable Codes`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-GoodLTCodes.lean Via leanprover/lean-eval@38361be, problem `annals_good_lt_codes`.
-/
public theorem_wanted theorem_1_2 (ρ : ℝ≥0) (hρ : ρ < 1) :
    ∃ q, ∃ κ ≠ 0, ∃ (n : ℕ → ℕ), ∃ (𝒞 : (i : ℕ) → BinaryCode (n i)), IsGood 𝒞 ∧
      ∀ i, Nonempty (LTC q κ (𝒞 i)) ∧ rate (𝒞 i) ≥ ρ

end GoodLTC

end MathlibExt.Combinatorics.GoodLTCodesWanted
