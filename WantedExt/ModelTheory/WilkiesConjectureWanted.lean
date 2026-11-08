/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wilkie's conjecture for Pfaffian structures

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ModelTheory.WilkiesConjecture` — annals_wilkies_conjecture (manifest `manifests/problems/annals_wilkies_conjecture.toml`, rev 1, submitter Justus Springer, Mathias Stout, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.ModelTheory.WilkiesConjectureWanted` namespace. Mathematical statements are unchanged, except in `degreeHeightLE`, where the lean-eval source's `IsIntegral ℚ` coordinate condition is replaced by `IsAlgebraic ℚ` (an equivalent reformulation over the field `ℚ`), and `corollary_1` adds an explicit finiteness conjunct, since `Nat.card` alone does not assert finiteness. Source: G. Binyamini, D. Novikov, and B. Zak, `Wilkie's conjecture for Pfaffian structures`, Annals of Math, 199 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-2-WilkiesConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Definability
public import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

namespace MathlibExt.ModelTheory.WilkiesConjectureWanted
/-!
# Main Statement from Wilkie's conjecture for Pfaffian structures

We formalise the statement of the main result from G. Binyamini, D. Novikov, and B. Zak,
`Wilkie's conjecture for Pfaffian structures`, Annals of Math, 199 (2) 2024.
-/

set_option autoImplicit false

noncomputable section

namespace WilkiesConjecture

open FirstOrder Language IntermediateField

/-- The type of function symbols for `Language.exp`. The only function symbol is a unary `exp`. -/
inductive expFunc : ℕ → Type
  | exp : expFunc 1

/-- The language consisting of a single symbol `exp`. -/
def Language.exp : Language where
  Functions := expFunc
  Relations _ := Empty
  deriving Language.IsAlgebraic

/-- We endow the real numbers with the structure of `Language.exp`.
The `exp` symbol is interpreted by `Real.exp`. -/
instance : Language.exp.Structure ℝ where
  funMap {n} f := match n, f with
    | 1, .exp => fun x ↦ Real.exp (x 0)

/-- Endow the real numbers with a `CompatibleRing` instance
(which extends `Language.ring.Structure`). -/
instance : Ring.CompatibleRing ℝ := Ring.compatibleRingOfRing ℝ

/-- The language of rings plus exponentials contains function symbols `(+,*,-,0,1,exp)`. -/
abbrev expRing := Language.ring.sum Language.exp

variable {n : ℕ}

local notation "ℝⁿ" => Fin n → ℝ

/-- A set `X ⊆ ℝⁿ` is called semialgebraic if it is definable in the language of rings over `ℝ`. -/
def IsSemialgebraic (X : Set ℝⁿ) : Prop :=
  Set.Definable Set.univ Language.ring X

/-- A set `X ⊆ ℝⁿ` is definable in `ℝₑₓₚ` if it is definable in the language of rings + `exp`. -/
def IsRExpDefinable (X : Set ℝⁿ) : Prop :=
  Set.Definable Set.univ expRing X

/-- If `X ⊆ ℝⁿ` then we denote by `Xᵃˡᵍ` the union of all connected,
positive-dimensional semialgebraic sets contained in X. Note that here, we say "infinite"
instead of positive-dimensional, which is equivalent in this setting. -/
def algPart (X : Set ℝⁿ) : Set ℝⁿ :=
  sSup { Y : Set ℝⁿ | Y ⊆ X ∧ IsSemialgebraic Y ∧ Y.Infinite ∧ IsConnected Y }

/-- If `X ⊆ ℝⁿ` then we denote `Xᵗʳᵃⁿˢ := X \ Xᵃˡᵍ`. -/
def transPart (X : Set ℝⁿ) : Set ℝⁿ := X \ algPart X

/-- We extend the multiplicative Weil height on `ℝ` to `ℝⁿ` by taking the maximum
of the heights of the coordinates. -/
def height (a : ℝⁿ) : ℝ := ⨆ i, NumberField.absMulHeight₁ (a i)

/-- For `g H : ℕ` we define `X(g,H) := {x ∈ X : [Q(x) : Q] ≤ g, H(x) ≤ H}`. -/
def degreeHeightLE (X : Set ℝⁿ) (g H : ℕ) : Set ℝⁿ :=
  { x ∈ X | (∀ i, IsAlgebraic ℚ (x i)) ∧
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) ≤ g ∧ height x ≤ H }

/--
Statement of Corollary 1 (Wilkie's conjecture):

Let `X` be definable in `ℝₑₓₚ`. Then `#Xᵗʳᵃⁿˢ(g,H) ≤ poly_X (g,log H)`.
Source: G. Binyamini, D. Novikov, and B. Zak, `Wilkie's conjecture for Pfaffian structures`, Annals of Math, 199 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-2-WilkiesConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_wilkies_conjecture`.
-/
public theorem_wanted corollary_1 (X : Set ℝⁿ) (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      (degreeHeightLE (transPart X) g H).Finite ∧
        Nat.card (degreeHeightLE (transPart X) g H) ≤ f.eval ![(g : ℝ), Real.log H]

end WilkiesConjecture

end

end MathlibExt.ModelTheory.WilkiesConjectureWanted
