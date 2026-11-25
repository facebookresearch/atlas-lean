/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Leftmost derivations and ambiguous context-free grammars
-/
module

public import Mathlib.Computability.ContextFreeGrammar

/-!
# Leftmost derivations and ambiguous context-free grammars

A **leftmost derivation** rewrites the leftmost nonterminal at every step. `LeftDerivation g u w
rs` says that applying the rules `rs` of `g` in order, each to the leftmost nonterminal, rewrites
the sentential form `u` to the word of terminals `w`. A grammar is **ambiguous** (`IsAmbiguous`)
when some word has two different leftmost derivations from the start symbol, which is Sipser's
Definition 2.7.

## Main results

- `LeftDerivation`, `IsAmbiguous`.
- `LeftDerivation.derives`, `LeftDerivation.mem_language` : leftmost derivations are derivations.
- `LeftDerivation.eq_of_terminal` : from a word of terminals, the only leftmost derivation is
  empty.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §2.1,
  Definition 2.7.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Language

variable {T : Type*}

/-- **Leftmost derivation.** Let $g$ be a context-free grammar, $u$ a sentential form of $g$, $w$ a
word of terminals and $r_1, \dots, r_n$ a list of rules over the terminals and nonterminals of
$g$. The list $r_1, \dots, r_n$ is a leftmost derivation of $w$ from $u$ in $g$ when every $r_i$
is a production of $g$, and, starting from $u$ and for $i = 1, \dots, n$ in turn, the leftmost
nonterminal of the current sentential form is the left-hand side of $r_i$ and is replaced by the
right-hand side of $r_i$, and the sentential form reached after these $n$ steps is $w$, read as a
string of terminals. In particular the empty list is a leftmost derivation of $w$ from $u$
exactly when $u$ is $w$ read as a string of terminals. -/
inductive LeftDerivation (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List T → List (ContextFreeRule T g.NT) → Prop
  /-- A word of terminals has the empty leftmost derivation. -/
  | done (w : List T) : LeftDerivation g (w.map Symbol.terminal) w []
  /-- Rewrite the leftmost nonterminal `r.input`, after the terminal prefix `p`. -/
  | step {p : List T} {v : List (Symbol T g.NT)} {w : List T} {r : ContextFreeRule T g.NT}
      {rs : List (ContextFreeRule T g.NT)} :
      r ∈ g.rules → LeftDerivation g (p.map Symbol.terminal ++ r.output ++ v) w rs →
      LeftDerivation g (p.map Symbol.terminal ++ Symbol.nonterminal r.input :: v) w (r :: rs)

/-- **Ambiguous grammar.** A context-free grammar $g$ is **ambiguous** if some word of terminals
$w$ has two leftmost derivations from the start symbol of $g$ that use different lists of rules. -/
def IsAmbiguous (g : ContextFreeGrammar T) : Prop :=
  ∃ w rs₁ rs₂, rs₁ ≠ rs₂ ∧ LeftDerivation g [Symbol.nonterminal g.initial] w rs₁ ∧
    LeftDerivation g [Symbol.nonterminal g.initial] w rs₂

namespace LeftDerivation

variable {g : ContextFreeGrammar T}

/-- **Leftmost derivations are derivations.** Let $g$ be a context-free grammar. If a sentential
form $u$ has a leftmost derivation in $g$ to a word of terminals $w$, then $u$ derives $w$ in $g$
(by zero or more rewriting steps). -/
theorem derives {u : List (Symbol T g.NT)} {w : List T} {rs : List (ContextFreeRule T g.NT)}
    (h : LeftDerivation g u w rs) : g.Derives u (w.map Symbol.terminal) := by
  induction h with
  | done => exact ContextFreeGrammar.Derives.refl _
  | @step p v w r rs hr _ ih =>
    refine ContextFreeGrammar.Produces.trans_derives ⟨r, hr, ?_⟩ ih
    simpa using r.rewrites_of_exists_parts (p.map Symbol.terminal) v

/-- **Words with a leftmost derivation lie in the language.** Let $g$ be a context-free grammar.
If a word of terminals $w$ has a leftmost derivation in $g$ from the start symbol of $g$, then $w$
belongs to the language of $g$. -/
theorem mem_language {w : List T} {rs : List (ContextFreeRule T g.NT)}
    (h : LeftDerivation g [Symbol.nonterminal g.initial] w rs) : w ∈ g.language :=
  (ContextFreeGrammar.mem_language_iff g w).mpr h.derives

/-- **Leftmost derivations from a word of terminals are empty.** Let $g$ be a context-free grammar
and $u$ a word of terminals. If $u$ has a leftmost derivation in $g$ with list of rules $\rho$ to a
word of terminals $w$, then $\rho$ is the empty list and $w = u$. -/
theorem eq_of_terminal {u w : List T} {rs : List (ContextFreeRule T g.NT)}
    (h : LeftDerivation g (u.map Symbol.terminal) w rs) : rs = [] ∧ w = u := by
  generalize hs : u.map Symbol.terminal = s at h
  cases h with
  | done w' =>
    exact ⟨rfl, List.map_injective_iff.mpr (fun _ _ h ↦ Symbol.terminal.inj h) hs.symm⟩
  | @step p v w r rs' _ _ =>
    have : Symbol.nonterminal r.input ∈ u.map (Symbol.terminal (N := g.NT)) := by
      rw [hs]
      simp
    simp at this

end LeftDerivation

end Cslib.Language
