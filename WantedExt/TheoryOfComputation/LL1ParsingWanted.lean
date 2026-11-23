/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# Semantic LL(1) predictive parsing is correct on LL(1) grammars

The statement is registered here as a `theorem_wanted`. The `FIRST`
and `FOLLOW` sets are defined through derivations
(`Cslib.Language.Yields` and `ContextFreeGrammar.Derives`), and the
LL(1) condition is the standard disjointness condition.

Nothing here is an executable parser. `ll1SemanticChoose` is a
*semantic abstraction*: it picks a production by classical choice
(`Classical.propDecidable` / `Classical.choose`) over a `FIRST`/`FOLLOW`
condition stated with the semantic derivability predicates
`Yields` / `Derives`. Evaluating it presupposes decisions about
derivability, so it does not compute a parse table. An executable
predictive parser would instead compute `FIRST` and `FOLLOW` by a
least-fixpoint iteration over the finite grammar (which needs
decidable equality on terminals and nonterminals and a termination
argument for the fixpoint), then build the table from those computed
sets; that construction is not attempted here. What
`ll1SemanticParse_correct` records is the specification an
executable parser must satisfy: the semantic choice, applied
deterministically at each nonterminal, accepts exactly the words of
an LL(1) grammar. Correctness needs the LL(1) disjointness at every
prediction step and a fuel bound for completeness, so it is left as
a `theorem_wanted`. The Earley recognizer, whose correctness
`Cslib.Language.earleyAccepts_iff` is proved in `CSLibExt`, covers
general context-free grammars.
-/

@[expose] public section

namespace Cslib.LL1ParsingWanted

open Cslib.Language

variable {T : Type*}

-- The derivability oracle: this instance is what lets the `if` in
-- `ll1SemanticChoose` decide an existential over the semantic
-- `FIRST`/`FOLLOW` predicates. It is the reason the definitions below
-- are a semantic abstraction, not an executable parser.
attribute [local instance] Classical.propDecidable

/-- The `FIRST` set of a sentential form: the terminals that can begin
a word it yields. This is a semantic set, defined through
derivations, not a computed fixpoint.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing). -/
public def firstSet (g : ContextFreeGrammar T) (α : List (Symbol T g.NT)) :
    Set T :=
  {a | ∃ u, Yields g α (a :: u)}

/-- A sentential form is nullable when it yields the empty word.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing). -/
public def nullableForm (g : ContextFreeGrammar T) (α : List (Symbol T g.NT)) :
    Prop :=
  Yields g α []

/-- The `FOLLOW` set of a nonterminal: the terminals that can
immediately follow it in a sentential form derived from the initial
nonterminal. This is a semantic set, defined through derivations,
not a computed fixpoint.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing). -/
public def followSet (g : ContextFreeGrammar T) (A : g.NT) : Set T :=
  {a | ∃ (u v : List (Symbol T g.NT)), g.Derives
    [Symbol.nonterminal g.initial]
    (u ++ [Symbol.nonterminal A, Symbol.terminal a] ++ v)}

/-- A grammar is LL(1) when, for any two distinct productions of the
same nonterminal, their `FIRST` sets are disjoint; a nullable
production's `FIRST` set is also disjoint from the `FOLLOW` set of
its nonterminal; and at most one production of a nonterminal is
nullable.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing);
Hopcroft, Motwani, and Ullman, Introduction to Automata Theory,
Languages, and Computation, 3rd ed., Chapter 5. -/
public def IsLL1 (g : ContextFreeGrammar T) : Prop :=
  ∀ {A : g.NT} {r₁ r₂ : ContextFreeRule T g.NT},
    r₁ ∈ g.rules → r₂ ∈ g.rules → r₁.input = A → r₂.input = A →
      r₁ ≠ r₂ →
        (firstSet g r₁.output ∩ firstSet g r₂.output) = ∅ ∧
          (nullableForm g r₁.output →
            (firstSet g r₂.output ∩ followSet g A) = ∅) ∧
          (nullableForm g r₂.output →
            (firstSet g r₁.output ∩ followSet g A) = ∅) ∧
          ¬ (nullableForm g r₁.output ∧ nullableForm g r₂.output)

/-- The semantic LL(1) table entry for a nonterminal and an optional
lookahead (`none` is end of input): some production of the
nonterminal whose `FIRST` set contains the lookahead, or, for end of
input or a lookahead in the `FOLLOW` set, a nullable production.
This is a *semantic abstraction*, not a computed table entry: the
production is picked by classical choice over a condition stated
with the semantic derivability predicates, so evaluating it
presupposes derivability decisions. An executable parser would
compute `FIRST`/`FOLLOW` by fixpoint instead.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing). -/
public noncomputable def ll1SemanticChoose (g : ContextFreeGrammar T)
    (A : g.NT) (a : Option T) : Option (ContextFreeRule T g.NT) :=
  if h : ∃ r ∈ g.rules, r.input = A ∧
      (match a with
       | some b => b ∈ firstSet g r.output ∨
           (nullableForm g r.output ∧ b ∈ followSet g A)
       | none => nullableForm g r.output) then
    some (Classical.choose h)
  else none

/-- The semantic LL(1) predictive parser, fuelled by the number of
steps it may still take: terminals on the stack must match the
input, and nonterminals on the stack expand by their semantic table
entry. It accepts exactly when the stack empties at the same time
as the input. This is a *semantic abstraction*, not an executable
parser: expansion uses `ll1SemanticChoose`, whose choice is
classical over derivability predicates. Terminal matching is the
only computable step, via the explicit `[DecidableEq T]`
assumption.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing). -/
public noncomputable def ll1SemanticParse [DecidableEq T]
    (g : ContextFreeGrammar T) :
    ℕ → List (Symbol T g.NT) → List T → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | _ + 1, [], _ :: _ => false
  | _ + 1, Symbol.terminal _ :: _, [] => false
  | fuel + 1, Symbol.terminal a :: stack, b :: input =>
      if a = b then ll1SemanticParse g fuel stack input else false
  | fuel + 1, Symbol.nonterminal A :: stack, input =>
      match ll1SemanticChoose g A input.head? with
      | some r => ll1SemanticParse g fuel (r.output ++ stack) input
      | none => false

/-- Semantic LL(1) predictive parsing is correct on LL(1) grammars:
the semantic parser accepts a word for some fuel bound exactly
when the word is in the grammar's language. The fuel existential
is outside the equivalence: putting it inside would make the
statement vacuous for words outside the language, since
`ll1SemanticParse g 0 … = false` always. This is a statement
about the semantic abstraction, not about an executable parser.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (predictive parsing);
Hopcroft, Motwani, and Ullman, Introduction to Automata Theory,
Languages, and Computation, 3rd ed., Chapter 5. -/
public theorem_wanted ll1SemanticParse_correct {T : Type*} [DecidableEq T]
    {g : ContextFreeGrammar T} (hg : IsLL1 g) (w : List T) :
    (∃ (fuel : ℕ),
      ll1SemanticParse g fuel [Symbol.nonterminal g.initial] w = true) ↔
        w ∈ g.language

end Cslib.LL1ParsingWanted
