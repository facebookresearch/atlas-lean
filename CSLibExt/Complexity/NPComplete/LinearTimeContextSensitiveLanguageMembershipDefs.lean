/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Membership for some fixed linear-time context-sensitive grammar: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL20], comment: NP-complete for some
fixed "linear time" context-sensitive grammar;
R. V. Book, "On the complexity of formal grammars", Acta Informatica 9 (1978), 171-182,
doi:10.1007/BF00289076;
R. V. Book, "Time-bounded grammars and their languages", Journal of Computer and System
Sciences 5 (1971), 397-429, doi:10.1016/S0022-0000(71)80025-9 (time-bounded grammars).
-/
module

public import CSLibExt.Computability.Languages.ContextSensitive.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearTimeContextSensitiveLanguageMembership

open Cslib.Language

/-- The word `w` has a derivation in `g` with at most `m` rewriting steps: a chain of sentential
forms from the initial nonterminal to `w`, consecutive forms related by `Rewrites g`, with at most
`m` forms after the first. -/
def DerivableWithin {N : Type} (g : CSGrammar ℕ N) (m : ℕ) (w : List ℕ) : Prop :=
  ∃ l : List (List (Symbol ℕ N)), l.length ≤ m ∧
    List.IsChain (Rewrites g) ([Symbol.nonterminal g.initial] :: l) ∧
    ([Symbol.nonterminal g.initial] :: l).getLast (List.cons_ne_nil _ _) =
      w.map Symbol.terminal

/-- The grammar `g` is linear time: for some constant `k`, every word `w` of its language has a
derivation with at most `k · |w|` steps. -/
def IsLinearTime {N : Type} (g : CSGrammar ℕ N) : Prop :=
  ∃ k : ℕ, ∀ w ∈ language g, DerivableWithin g (k * w.length) w

open Classical in
/-- Membership in the language of the fixed grammar `g`, as a decision problem over
bitstrings. -/
noncomputable def membershipDec {N : Type} (g : CSGrammar ℕ N) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List ℕ) x with
  | some w => decide (w ∈ language g)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LinearTimeContextSensitiveLanguageMembership
