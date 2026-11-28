/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREDICATE LOGIC WITHOUT NEGATION, existential sentences over two constants,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO15] PREDICATE LOGIC WITHOUT
NEGATION, p. 263, comment: remains NP-complete even if there are no universal quantifiers, no
relation symbols, and only two functions, both with dimension 0 (and hence constants);
D. Kozen, "First order predicate logic without negation is NP-complete", Report 77-307,
Department of Computer Science, Cornell University (1977); journal version: D. Kozen,
"Positive first-order logic is NP-complete", IBM Journal of Research and Development 25 (1981),
327-332, doi:10.1147/rd.254.0327.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.ModelTheory.Satisfiability

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PredicateLogicWithoutNegationExistentialConstants

open FirstOrder FirstOrder.Language

/-- The language: two constant symbols `c₀`, `c₁`, and no relation symbols. -/
abbrev Lang : Language := constantsOn (Fin 2)

/-- The constant symbol `cᵢ`. -/
def const (i : Fin 2) : Lang.Constants := i

/-- A token `(code, a, b)` of the prefix notation. -/
abbrev Token := ℕ × ℕ × ℕ

/-- An instance: the token list of the sentence `A`. -/
abbrev PredicateLogicInstance := List Token

/-- The term with code `t` inside `k` existential quantifiers: `c₀` for `0`, `c₁` for `1`, and
for `j + 2` with `j < k` the variable bound by the `(j + 1)`-th enclosing quantifier, counted
from the outermost (Mathlib's de Bruijn levels). -/
def term (k : ℕ) : ℕ → Option (Lang.Term (Empty ⊕ Fin k))
  | 0 => some (const 0).term
  | 1 => some (const 1).term
  | j + 2 => if h : j < k then some (Term.var (Sum.inr ⟨j, h⟩)) else none

/-- Read one formula inside `k` existential quantifiers from the front of the token list,
returning it with the unread tokens; the first argument is recursion fuel. -/
def parseAux : ℕ → (k : ℕ) → List Token → Option (Lang.BoundedFormula Empty k × List Token)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, k, t :: r =>
    match t.1 with
    | 0 => (term k t.2.1).bind fun s => (term k t.2.2).map fun u => (s.bdEqual u, r)
    | 1 => (parseAux f k r).bind fun p => (parseAux f k p.2).map fun q => (p.1 ⊓ q.1, q.2)
    | 2 => (parseAux f k r).bind fun p => (parseAux f k p.2).map fun q => (p.1 ⊔ q.1, q.2)
    | 3 => (parseAux f (k + 1) r).map fun p => (p.1.ex, p.2)
    | _ => none

/-- The sentence spelled by a token list, if the whole list spells exactly one. -/
def parse (toks : List Token) : Option Lang.Sentence :=
  match parseAux toks.length 0 toks with
  | some (φ, []) => some φ
  | _ => none

/-- Well-formedness of an instance: the token list spells a sentence. -/
def WellFormed (i : PredicateLogicInstance) : Prop :=
  (parse i).isSome

/-- The sentence is true under all interpretations of the two constants: it holds in every
nonempty structure for the language (Mathlib's `(∅ : Theory) ⊨ᵇ A`). -/
def PredicateLogicFeasible (i : PredicateLogicInstance) : Prop :=
  ∃ A, parse i = some A ∧ (∅ : Lang.Theory) ⊨ᵇ A

open Classical in
/-- PREDICATE LOGIC WITHOUT NEGATION restricted to existential sentences over two constants, as
a decision problem over bitstrings. -/
noncomputable def predicateLogicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PredicateLogicInstance) x with
  | some i => decide (WellFormed i ∧ PredicateLogicFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PredicateLogicWithoutNegationExistentialConstants
