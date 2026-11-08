/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quantifier elimination for the theory of real closed fields

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ProgramVerification.RealClosedFieldQE` — rcf_quantifier_elimination (manifest `manifests/problems/rcf_quantifier_elimination.toml`, rev 1, submitter Kim Morrison, status draft) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted` namespace. Mathematical
statements are unchanged. Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
/-!
# Quantifier elimination for real closed fields

## The task

Work in the first-order language of ordered rings: `Term`s are built from variables, integer
constants, `+`, `*` and `-`, and `Formula`s are built from the atoms `<` and `=` using `⊥`, `→`
and `∀`. `Formula.Holds` interprets a formula in `ℝ` under an environment assigning a real to
each variable, and `Formula.IsQF` says that a formula contains no quantifier.

Implement `qe`, which converts an arbitrary formula into an equivalent quantifier-free one, and
prove that it does. `isQF_qe` says the output contains no quantifier. `holds_qe` says the input
and the output have the same truth value in every environment. No separate free-variable
condition is needed for semantic equivalence, although the output may syntactically mention
additional variables in vacuous expressions such as `x = x`.

For example, `∃ x. x * x = a` has the de Bruijn form

    Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))

with `a` free, and `qe` must return something equivalent to `¬ (a < 0)`, such as

    Formula.not (.lt (.var 0) (.const 0))

This is the point at which real closedness does the work: the equivalence fails over `ℚ`.

Tarski proved that such a `qe` exists, which is what makes the theory decidable: to decide a
sentence, run `qe` and evaluate the resulting closed quantifier-free formula. The
Cohen-Hörmander route has a comparatively small formalization footprint. Cylindrical algebraic
decomposition is an important practical route and has also been formalized in Coq; see
Mahboubi's certified CAD work and the current MathComp CAD development. Cohen and Mahboubi's
quantifier-elimination development instead follows an algebraic pseudo-remainder route.

The problem is posed over `ℝ` for concreteness. Tarski's theorem holds over an arbitrary real
closed field. Generalising `holds_qe` in that direction would require a more abstract algebraic
development than the concrete Mathlib API over `ℝ` used here.

## Design notes

The trusted vocabulary is deliberately small and purely syntactic. Variables are raw de Bruijn
indices and environments are total functions `Nat → ℝ`, so there is no well-scopedness
bookkeeping to do.

`isQF_qe` and `holds_qe` are jointly load-bearing and neither can be dropped:

* with only `isQF_qe`, take `qe := fun _ => .fals`;
* with only `holds_qe`, take `qe := id`.

Terms and quantifier-free formulas are enumerable, but enumerating candidates does not provide
a shortcut: recognizing which candidate is equivalent to the input already requires the
substantive quantifier-elimination argument. There is likewise no `Classical.choice` shortcut,
because the existence proof one would have to exhibit before choosing a quantifier-free
equivalent is Tarski's theorem itself.

A decision procedure `valid? : Formula → Bool` with `valid? φ = true ↔ ∀ env, φ.Holds env` was
considered as a further hole and rejected: `noncomputable def valid? φ := decide (∀ env,
φ.Holds env)` satisfies it with a one-line proof. Declaring it a plain `def` does make Lean
reject that, but `noncomputable` is recorded in a separate environment extension rather than in
the `ConstantInfo`, so a checker comparing name, type, universe levels and safety will not see
the difference.
-/

namespace ProgramVerification
namespace RealClosedFieldQE

/-! ## Syntax -/

/-- Terms in the language of ordered rings, with de Bruijn variables. -/
inductive Term where
  | var : Nat → Term
  | const : Int → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | neg : Term → Term
  deriving DecidableEq, Repr, Inhabited

/--
Formulas in the language of ordered rings. The connectives are the minimal set
`⊥`, `→`, `∀`; the usual derived connectives are provided as abbreviations below.
-/
inductive Formula where
  | lt : Term → Term → Formula
  | eq : Term → Term → Formula
  /-- Falsity. -/
  | fals : Formula
  | imp : Formula → Formula → Formula
  /-- Universal quantification; binds de Bruijn index `0` in the body. -/
  | all : Formula → Formula
  deriving DecidableEq, Repr, Inhabited

namespace Formula

/-- Negation. -/
def not (φ : Formula) : Formula := .imp φ .fals

/-- Truth. -/
def tru : Formula := .not .fals

/-- Disjunction. -/
def or (φ ψ : Formula) : Formula := .imp φ.not ψ

/-- Conjunction. -/
def and (φ ψ : Formula) : Formula := (φ.imp ψ.not).not

/-- Existential quantification; binds de Bruijn index `0` in the body. -/
def ex (φ : Formula) : Formula := φ.not.all.not

/-!
Under the classical logic available in this problem, these derived connectives have their
usual semantics under `Formula.Holds`.
-/

end Formula

/-! ## Semantics -/

/-- Extend an environment, binding de Bruijn index `0` to `x`. -/
def cons (x : ℝ) (env : Nat → ℝ) : Nat → ℝ
  | 0 => x
  | i + 1 => env i

/-- Interpretation of a term in `ℝ`. -/
def Term.eval (env : Nat → ℝ) : Term → ℝ
  | .var i => env i
  | .const k => (k : ℝ)
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -a.eval env

/-- Satisfaction of a formula in `ℝ` under an environment. -/
def Formula.Holds (env : Nat → ℝ) : Formula → Prop
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .fals => False
  | .imp φ ψ => φ.Holds env → ψ.Holds env
  | .all φ => ∀ x : ℝ, φ.Holds (cons x env)

/-- A formula is quantifier free if it contains no `Formula.all`. -/
def Formula.IsQF : Formula → Prop
  | .lt _ _ => True
  | .eq _ _ => True
  | .fals => True
  | .imp φ ψ => φ.IsQF ∧ ψ.IsQF
  | .all _ => False

/-! ## The problem -/

/--
Quantifier elimination: `qe φ` is a quantifier-free formula equivalent to `φ` over `ℝ` in
every environment. Its syntax may mention additional variables vacuously.
Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`.
-/
public def_wanted qe (φ : Formula) : Formula

/- The output of `qe` is quantifier free. -/
/-- Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`. -/
public theorem_wanted isQF_qe (φ : Formula) : (❰qe❱ φ).IsQF

/- The output of `qe` is equivalent to its input, under every environment. -/
/-- Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`. -/
public theorem_wanted holds_qe (φ : Formula) (env : Nat → ℝ) :
    (❰qe❱ φ).Holds env ↔ φ.Holds env

/--
Anti-vacuity guard for the semantics and de Bruijn convention: a real number is a square
exactly when it is nonnegative.
Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`.
-/
public theorem_wanted holds_ex_sq (env : Nat → ℝ) :
    (Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))).Holds env ↔
      (Formula.not (.lt (.var 0) (.const 0))).Holds env

end RealClosedFieldQE
end ProgramVerification

end MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
