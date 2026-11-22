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

/-- `LeftDerivation g u w rs`: applying the rules `rs` in order, each to the leftmost nonterminal,
rewrites the sentential form `u` to the word of terminals `w`. -/
inductive LeftDerivation (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List T → List (ContextFreeRule T g.NT) → Prop
  /-- A word of terminals has the empty leftmost derivation. -/
  | done (w : List T) : LeftDerivation g (w.map Symbol.terminal) w []
  /-- Rewrite the leftmost nonterminal `r.input`, after the terminal prefix `p`. -/
  | step {p : List T} {v : List (Symbol T g.NT)} {w : List T} {r : ContextFreeRule T g.NT}
      {rs : List (ContextFreeRule T g.NT)} :
      r ∈ g.rules → LeftDerivation g (p.map Symbol.terminal ++ r.output ++ v) w rs →
      LeftDerivation g (p.map Symbol.terminal ++ Symbol.nonterminal r.input :: v) w (r :: rs)

/-- A grammar is **ambiguous** if some word has two different leftmost derivations from the start
symbol. -/
def IsAmbiguous (g : ContextFreeGrammar T) : Prop :=
  ∃ w rs₁ rs₂, rs₁ ≠ rs₂ ∧ LeftDerivation g [Symbol.nonterminal g.initial] w rs₁ ∧
    LeftDerivation g [Symbol.nonterminal g.initial] w rs₂

namespace LeftDerivation

variable {g : ContextFreeGrammar T}

/-- A leftmost derivation is a derivation. -/
theorem derives {u : List (Symbol T g.NT)} {w : List T} {rs : List (ContextFreeRule T g.NT)}
    (h : LeftDerivation g u w rs) : g.Derives u (w.map Symbol.terminal) := by
  induction h with
  | done => exact ContextFreeGrammar.Derives.refl _
  | @step p v w r rs hr _ ih =>
    refine ContextFreeGrammar.Produces.trans_derives ⟨r, hr, ?_⟩ ih
    simpa using r.rewrites_of_exists_parts (p.map Symbol.terminal) v

/-- A word with a leftmost derivation from the start symbol is in the language. -/
theorem mem_language {w : List T} {rs : List (ContextFreeRule T g.NT)}
    (h : LeftDerivation g [Symbol.nonterminal g.initial] w rs) : w ∈ g.language :=
  (ContextFreeGrammar.mem_language_iff g w).mpr h.derives

/-- From a word of terminals, the only leftmost derivation is the empty one. -/
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
