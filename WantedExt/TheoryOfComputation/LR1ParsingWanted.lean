/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.Deterministic

/-!
# LR(1) grammars generate deterministic context-free languages

The statement is registered here as a `theorem_wanted`. The LR(1)
condition is stated as conflict-freedom of the LR(1) action table,
indexed by viable prefix and one-letter lookahead: for every viable
prefix `π` and lookahead `ℓ`, at most one reduce handle applies, and
a reduce handle and a shift on `ℓ` never both apply. Comparing only
two reductions with the same viable prefix would miss shift/reduce
conflicts: the even-palindrome grammar `S → 0 S 0 | 1 S 1 | ε` has a
shift/reduce conflict at viable prefix `[0]` with lookahead `0`
(reduce `S → ε` versus shift `0`), yet every pair of reductions
sharing a viable prefix agrees, so a reductions-only condition would
wrongly classify it as LR(1) even though its language is not
deterministic context-free. Building the canonical LR(1) parser
(items with lookahead, closure, goto, action/goto tables) and showing
it is a deterministic pushdown automaton is a large construction, so
the theorem is left as a `theorem_wanted`. The parser accepts by
final state; it is turned into end-marker acceptance by draining the
stack on the end marker exactly from accepting LR states. The
converse, that every deterministic context-free language has an LR(1)
grammar, is Knuth's theorem; see the audit row.
-/

@[expose] public section

namespace Cslib.LR1ParsingWanted

open Cslib.Language

variable {T : Type*}

/-- A rightmost derivation step: the rewritten nonterminal is the
rightmost nonterminal of the sentential form, so everything to its
right is terminals.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def RightmostStep (g : ContextFreeGrammar T)
    (u v : List (Symbol T g.NT)) : Prop :=
  ∃ (r : ContextFreeRule T g.NT) (p q : List (Symbol T g.NT)),
    r ∈ g.rules ∧ u = p ++ Symbol.nonterminal r.input :: q ∧
      v = p ++ r.output ++ q ∧ ∀ s ∈ q, ∃ a, s = Symbol.terminal a

/-- Rightmost derivations: reflexive-transitive closure of rightmost
steps.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def RightmostDerives (g : ContextFreeGrammar T)
    (u v : List (Symbol T g.NT)) : Prop :=
  Relation.ReflTransGen (RightmostStep g) u v

/-- The one-letter lookahead of a terminal word: its first letter,
or `none` at end of input.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def first1 (w : List T) : Option T :=
  w.head?

/-- A viable prefix is a prefix of `α ++ β` for some rightmost
derivation `S ⇒* α A w` whose nonterminal `A` has a production
`A → β`: it is a stack content the LR parser can reach without
passing a handle.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def IsViablePrefix (g : ContextFreeGrammar T)
    (π : List (Symbol T g.NT)) : Prop :=
  ∃ (α : List (Symbol T g.NT)) (A : g.NT) (β : List (Symbol T g.NT))
    (w : List T),
    RightmostDerives g [Symbol.nonterminal g.initial]
        (α ++ [Symbol.nonterminal A] ++ w.map Symbol.terminal) ∧
      (∃ r ∈ g.rules, r.input = A ∧ r.output = β ∧ π <:+ α ++ β)

/-- A reduce action at viable prefix `π` with lookahead `ℓ`: the
handle `A → β` ends exactly at `π` (`π = α ++ β`), the sentential
form `α A w` is rightmost-derivable, and the lookahead is the first
letter of the terminal suffix `w` (or `none` when `w` is empty).
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def IsReduceAction (g : ContextFreeGrammar T)
    (π : List (Symbol T g.NT)) (ℓ : Option T)
    (α : List (Symbol T g.NT)) (A : g.NT) (β : List (Symbol T g.NT))
    (w : List T) : Prop :=
  π = α ++ β ∧
    RightmostDerives g [Symbol.nonterminal g.initial]
        (α ++ [Symbol.nonterminal A] ++ w.map Symbol.terminal) ∧
      (∃ r ∈ g.rules, r.input = A ∧ r.output = β) ∧ first1 w = ℓ

/-- A shift action at viable prefix `π` with lookahead `some a`:
shifting `a` is possible, that is, `π ++ [a]` is itself a viable
prefix.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def IsShiftAction (g : ContextFreeGrammar T)
    (π : List (Symbol T g.NT)) (ℓ : Option T) : Prop :=
  ∃ (a : T), ℓ = some a ∧
    IsViablePrefix g (π ++ [Symbol.terminal a])

/-- A grammar is LR(1) when its LR(1) action table is conflict-free:
for every viable prefix `π` and lookahead `ℓ`, any two reduce
actions with that prefix and lookahead have the same handle (the
same left context, nonterminal, and production output), and no
reduce action coexists with a shift action on `ℓ`. The second clause
rules out shift/reduce conflicts; the first rules out reduce/reduce
conflicts.
Source: Aho, Lam, Sethi, and Ullman, Compilers: Principles,
Techniques, and Tools, 2nd ed., Chapter 4 (LR parsing); Knuth, "On
the translation of languages from left to right", Information and
Control 8 (1965), 607-639. -/
public def IsLR1 (g : ContextFreeGrammar T) : Prop :=
  (∀ {π : List (Symbol T g.NT)} {ℓ : Option T}
    {α₁ α₂ : List (Symbol T g.NT)} {A₁ A₂ : g.NT}
    {β₁ β₂ : List (Symbol T g.NT)} {w₁ w₂ : List T},
    IsReduceAction g π ℓ α₁ A₁ β₁ w₁ →
    IsReduceAction g π ℓ α₂ A₂ β₂ w₂ →
      α₁ = α₂ ∧ A₁ = A₂ ∧ β₁ = β₂) ∧
  (∀ {π : List (Symbol T g.NT)} {ℓ : Option T}
    {α : List (Symbol T g.NT)} {A : g.NT}
    {β : List (Symbol T g.NT)} {w : List T},
    IsReduceAction g π ℓ α A β w → ¬ IsShiftAction g π ℓ)

/-- The language of an LR(1) grammar is deterministic context-free.
Source: Knuth, "On the translation of languages from left to
right", Information and Control 8 (1965), 607-639; Aho, Lam, Sethi,
and Ullman, Compilers: Principles, Techniques, and Tools, 2nd ed.,
Chapter 4 (LR parsing). -/
public theorem_wanted isDeterministicContextFree_of_isLR1 {T : Type*}
    {g : ContextFreeGrammar T} (hg : IsLR1 g) :
    IsDeterministicContextFree g.language

end Cslib.LR1ParsingWanted
