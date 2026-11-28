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

/-- **Function symbols of the language of exponentiation.** The function symbols of the language
of exponentiation, sorted by arity: there is exactly one, the unary symbol $\exp$, and there are
none of any other arity. -/
inductive expFunc : ℕ → Type
  | exp : expFunc 1

/-- **Language of exponentiation.** The first-order language with a single function symbol, the
unary symbol $\exp$, and no relation symbols. -/
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

/-- **Language of rings with exponentiation.** The first-order language whose function symbols
are those of the language of rings, namely the binary symbols $+$ and $\cdot$, the unary symbol
$-$ and the constants $0$ and $1$, together with the unary symbol $\exp$ of the language of
exponentiation; it has no relation symbols. -/
abbrev expRing := Language.ring.sum Language.exp

variable {n : ℕ}

local notation "ℝⁿ" => Fin n → ℝ

/-- **Semialgebraic set.** A set $X \subseteq \mathbb{R}^n$ is semialgebraic if it is definable,
with parameters from $\mathbb{R}$, in the real numbers viewed as a structure for the language of
rings. -/
def IsSemialgebraic (X : Set ℝⁿ) : Prop :=
  Set.Definable Set.univ Language.ring X

/-- **Definable sets of the real exponential field.** A set $X \subseteq \mathbb{R}^n$ is definable
in $\mathbb{R}_{\exp}$ if it is definable, with parameters from $\mathbb{R}$, in the real numbers
viewed as a structure for the language of rings with exponentiation, where the ring symbols have
their usual meaning and $\exp$ is interpreted as the real exponential function. -/
def IsRExpDefinable (X : Set ℝⁿ) : Prop :=
  Set.Definable Set.univ expRing X

/-- **Algebraic part of a set.** For a set $X \subseteq \mathbb{R}^n$, the algebraic part
$X^{\mathrm{alg}}$ of $X$ is the union of all connected, infinite semialgebraic sets $Y$ with
$Y \subseteq X$.

The source takes the union of the connected, positive-dimensional semialgebraic subsets of $X$;
for connected semialgebraic sets, being infinite is equivalent to being positive-dimensional. -/
def algPart (X : Set ℝⁿ) : Set ℝⁿ :=
  sSup { Y : Set ℝⁿ | Y ⊆ X ∧ IsSemialgebraic Y ∧ Y.Infinite ∧ IsConnected Y }

/-- **Transcendental part of a set.** For a set $X \subseteq \mathbb{R}^n$, the transcendental
part of $X$ is $X^{\mathrm{trans}} := X \setminus X^{\mathrm{alg}}$, where $X^{\mathrm{alg}}$ is
the algebraic part of $X$. -/
def transPart (X : Set ℝⁿ) : Set ℝⁿ := X \ algPart X

/-- **Height of a point.** For $a = (a_1, \dots, a_n) \in \mathbb{R}^n$, the height $H(a)$ is the
maximum of the absolute multiplicative Weil heights of the coordinates $a_1, \dots, a_n$. A
coordinate that is not algebraic over $\mathbb{Q}$ counts with height $1$, and for $n = 0$ the
height is $0$. -/
def height (a : ℝⁿ) : ℝ := ⨆ i, NumberField.absMulHeight₁ (a i)

/-- **Points of bounded degree and height.** For a set $X \subseteq \mathbb{R}^n$ and natural
numbers $g$ and $H$, the set $X(g, H)$ consists of the points $x = (x_1, \dots, x_n) \in X$ whose
coordinates are all algebraic over $\mathbb{Q}$, such that the field
$\mathbb{Q}(x) = \mathbb{Q}(x_1, \dots, x_n)$ satisfies $[\mathbb{Q}(x) : \mathbb{Q}] \le g$ and
the height $H(x)$ of $x$, the maximum of the absolute multiplicative Weil heights of
$x_1, \dots, x_n$ (taken to be $0$ when $n = 0$), satisfies $H(x) \le H$. -/
def degreeHeightLE (X : Set ℝⁿ) (g H : ℕ) : Set ℝⁿ :=
  { x ∈ X | (∀ i, IsAlgebraic ℚ (x i)) ∧
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) ≤ g ∧ height x ≤ H }

/-- **Wilkie's conjecture for the real exponential field.** Let $X \subseteq \mathbb{R}^n$ be
definable in $\mathbb{R}_{\exp}$. Then there is a polynomial $f$ in two variables with real
coefficients such that the following holds for all natural numbers $g$ and $H$. Let
$X^{\mathrm{trans}}(g, H)$ be the set of points $x = (x_1, \dots, x_n)$ of the transcendental part
$X^{\mathrm{trans}}$ of $X$ whose coordinates are all algebraic over $\mathbb{Q}$, such that the
field $\mathbb{Q}(x) = \mathbb{Q}(x_1, \dots, x_n)$ satisfies $[\mathbb{Q}(x) : \mathbb{Q}] \le g$
and the height $H(x)$ of $x$, the maximum of the absolute multiplicative Weil heights of
$x_1, \dots, x_n$ (taken to be $0$ when $n = 0$), satisfies $H(x) \le H$. Then
$X^{\mathrm{trans}}(g, H)$ is finite and has at most $f(g, \log H)$ elements, where $\log 0$ is
taken to be $0$.

This is Corollary 1 of the source.

Source: G. Binyamini, D. Novikov, and B. Zak, `Wilkie's conjecture for Pfaffian structures`, Annals of Math, 199 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-2-WilkiesConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_wilkies_conjecture`.
-/
public theorem_wanted corollary_1 (X : Set ℝⁿ) (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      (degreeHeightLE (transPart X) g H).Finite ∧
        Nat.card (degreeHeightLE (transPart X) g H) ≤ f.eval ![(g : ℝ), Real.log H]

end WilkiesConjecture

end

end MathlibExt.ModelTheory.WilkiesConjectureWanted
