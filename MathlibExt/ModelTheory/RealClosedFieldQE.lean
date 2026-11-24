/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ProgramVerification/RealClosedFieldQE.lean` (leanprover/lean-eval),
problem `rcf_quantifier_elimination` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter).
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The syntax, semantics, and statement of `holds_ex_sq` were adapted into the ATLAS namespace
and moved here from `WantedExt/TheoryOfComputation/RealClosedFieldQEWanted.lean`.
The proof of `holds_ex_sq` is original to ATLAS.
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Square roots in the first-order language of ordered rings

The theorem `holds_ex_sq` eliminates the existential quantifier from the formula
`∃ x, x * x = a` over the reals by showing that it holds exactly when `¬ (a < 0)` holds.
-/

@[expose] public section

namespace MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
namespace ProgramVerification.RealClosedFieldQE

/-! ## Syntax -/

/-- **Terms of the language of ordered rings.** Terms are built from variables $x_i$, one for
each natural number $i$ (a de Bruijn index), and integer constants $k \in \mathbb{Z}$, using
addition $s + t$, multiplication $s \cdot t$ and negation $-t$. -/
inductive Term where
  | var : Nat → Term
  | const : Int → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | neg : Term → Term
  deriving DecidableEq, Repr, Inhabited

/--
**Formulas of the language of ordered rings.** Formulas are built from the atomic formulas
$s < t$ and $s = t$, for terms $s$ and $t$, and falsity $\bot$, by implication $\varphi \to \psi$
and universal quantification $\forall \varphi$, which binds de Bruijn index $0$ in $\varphi$.
Negation, truth, disjunction, conjunction and existential quantification are defined from these.
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

/-- **Negation of a formula.** The negation $\neg\varphi$ of a formula $\varphi$ is the formula
$\varphi \to \bot$. -/
def not (φ : Formula) : Formula := .imp φ .fals

/-- **The true formula.** The formula $\top$ is the negation $\neg\bot$ of falsity, that is, the
formula $\bot \to \bot$. -/
def tru : Formula := .not .fals

/-- **Disjunction of formulas.** The disjunction $\varphi \lor \psi$ of formulas $\varphi$ and
$\psi$ is the formula $\neg\varphi \to \psi$. -/
def or (φ ψ : Formula) : Formula := .imp φ.not ψ

/-- **Conjunction of formulas.** For formulas $\varphi$ and $\psi$, the conjunction
$\varphi \wedge \psi$ is the formula $\neg(\varphi \to \neg\psi)$. -/
def and (φ ψ : Formula) : Formula := (φ.imp ψ.not).not

/-- **Existential quantification of formulas.** For a formula $\varphi$, the formula
$\exists \varphi$ is $\neg \forall \neg \varphi$; it binds de Bruijn index $0$ in $\varphi$. -/
def ex (φ : Formula) : Formula := φ.not.all.not

/-!
Under the classical logic available in this problem, these derived connectives have their
usual semantics under `Formula.Holds`.
-/

end Formula

/-! ## Semantics -/

/-- **Extending an environment.** An environment is a map $e : \mathbb{N} \to \mathbb{R}$ that
assigns a real number to each de Bruijn index. For $x \in \mathbb{R}$, the extension of $e$ by $x$
sends index $0$ to $x$ and index $i + 1$ to $e(i)$ for every $i \in \mathbb{N}$. -/
def cons (x : ℝ) (env : Nat → ℝ) : Nat → ℝ
  | 0 => x
  | i + 1 => env i

/-- **Evaluation of terms.** Given an environment $e : \mathbb{N} \to \mathbb{R}$, the value of a
term in $\mathbb{R}$ is defined by recursion on the term: the variable with de Bruijn index $i$ has
value $e(i)$, the integer constant $k$ has value $k$, and the value of a sum, product or negation
of terms is the sum, product or negation in $\mathbb{R}$ of the values of its parts. -/
def Term.eval (env : Nat → ℝ) : Term → ℝ
  | .var i => env i
  | .const k => (k : ℝ)
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -a.eval env

/--
**Satisfaction of formulas over the reals.** Let $e : \mathbb{N} \to \mathbb{R}$ be an
environment. Whether a formula holds under $e$ is defined by recursion on the formula: $s < t$
holds when the value of $s$ under $e$ is less than the value of $t$ under $e$; $s = t$ holds when
these values are equal; $\bot$ never holds; $\varphi \to \psi$ holds when $\varphi$ holding under
$e$ implies $\psi$ holding under $e$; and $\forall \varphi$ holds when, for every
$x \in \mathbb{R}$, $\varphi$ holds under the extension of $e$ by $x$.
-/
def Formula.Holds (env : Nat → ℝ) : Formula → Prop
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .fals => False
  | .imp φ ψ => φ.Holds env → ψ.Holds env
  | .all φ => ∀ x : ℝ, φ.Holds (cons x env)

/-- **Quantifier-free formulas.** A formula is quantifier free if it contains no universal
quantifier $\forall$. -/
def Formula.IsQF : Formula → Prop
  | .lt _ _ => True
  | .eq _ _ => True
  | .fals => True
  | .imp φ ψ => φ.IsQF ∧ ψ.IsQF
  | .all _ => False

/--
**A real number is a square exactly when it is nonnegative.** For every environment
$e : \mathbb{N} \to \mathbb{R}$, the formula $\exists x.\ x \cdot x = a$ holds under $e$ if and
only if the formula $\neg(a < 0)$ holds under $e$. In the first formula the bound variable $x$ is
de Bruijn index $0$ and $a$ is index $1$; in the second $a$ is index $0$; in both, $a$ denotes
$e(0)$. Thus $e(0)$ is a square in $\mathbb{R}$ exactly when $e(0) \ge 0$.

This checks the semantics and the de Bruijn convention against a known fact.

Source: Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier
elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi,
'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal
proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via
leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`.
-/
theorem holds_ex_sq (env : Nat → ℝ) :
    (Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))).Holds env ↔
      (Formula.not (.lt (.var 0) (.const 0))).Holds env := by
  change (¬ ∀ x : ℝ, x * x ≠ env 0) ↔ ¬ env 0 < ((0 : ℤ) : ℝ)
  rw [Int.cast_zero, not_forall_not, not_lt]
  simpa only [isSquare_iff_exists_mul_self, eq_comm] using (Real.isSquare_iff (x := env 0))

end ProgramVerification.RealClosedFieldQE
end MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
