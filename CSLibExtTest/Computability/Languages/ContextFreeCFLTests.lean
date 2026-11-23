/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Deterministic
public import CSLibExt.Computability.Languages.ContextFree.Earley
public import CSLibExt.Computability.Languages.ContextFree.GreibachNormalForm
public import CSLibExt.Computability.Languages.ContextFree.Parikh

/-!
# Tests for the context-free-language gap close-out

* `singleA`: the one-production grammar `S → true`. The Earley
  recognizer accepts `[true]` and rejects `[true, true]`, and the
  grammar is in Greibach normal form.
* A singleton Parikh image is semilinear.
* The DCFL ⊆ CFL inclusion applies to any deterministic
  context-free language.

Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102; Hopcroft and Ullman,
Introduction to Automata Theory, Languages, and Computation,
Addison-Wesley, 1979, Chapter 7; Parikh, "On context-free languages",
Journal of the ACM 13 (1966), 570-581; Ginsburg and Greibach,
"Deterministic context free languages", Information and Control 9
(1966), 620-648.
-/

@[expose] public section

namespace Cslib.Language.CFLTests

open Cslib.Language

/-- The one-production grammar `S → true`.
Source: Earley, "An efficient context-free parsing algorithm",
Communications of the ACM 13 (1970), 94-102. -/
def singleA : ContextFreeGrammar Bool where
  NT := Unit
  initial := ()
  rules := {⟨(), [Symbol.terminal true]⟩}

example : earleyAccepts singleA [true] := by
  refine ⟨⟨(), [Symbol.terminal true]⟩, Finset.mem_singleton_self _, rfl, ?_⟩
  exact EarleyChart.scan (EarleyChart.init (Finset.mem_singleton_self _) rfl)
    rfl rfl

example : ¬ earleyAccepts singleA [true, true] := by
  intro h
  rw [earleyAccepts_iff] at h
  obtain ⟨r, hr, -, hout⟩ := exists_rule_of_yields_singleton
    (mem_language_iff_yields.mp h)
  have hr' : r = ⟨(), [Symbol.terminal true]⟩ :=
    Finset.mem_singleton.mp hr
  subst hr'
  cases hout with
  | terminal _ htail => cases htail

example : IsGreibachNormalForm singleA := by
  refine ⟨?_, Or.inl ?_⟩
  · intro r hr
    have hr' : r = ⟨(), [Symbol.terminal true]⟩ :=
      Finset.mem_singleton.mp hr
    subst hr'
    exact Or.inr ⟨true, [], rfl⟩
  · intro r hr hmem
    have hr' : r = ⟨(), [Symbol.terminal true]⟩ :=
      Finset.mem_singleton.mp hr
    subst hr'
    simp at hmem

example : IsSemilinear ({parikhVector [true, false]} : Set (Bool → ℕ)) :=
  isSemilinear_singleton _

/-- Boundary test: a shorter coefficient list is rejected, not
truncated: `linComb [p, p] [1] = 0`, not `p`.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
example (p : Bool → ℕ) : linComb [p, p] [1] = 0 :=
  linComb_eq_zero_of_length_lt (by simp)

/-- Boundary test: a longer coefficient list is rejected, not
truncated: `linComb [p] [1, 0] = 0`, not `p`.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
example (p : Bool → ℕ) : linComb [p] [1, 0] = 0 :=
  linComb_eq_zero_of_length_gt (by simp)

/-- Boundary test: equal-length duplicate periods keep independent
coefficients: `linComb [p, p] [1, 0] = p`.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
example (p : Bool → ℕ) : linComb [p, p] [1, 0] = p :=
  linComb_dup p

example {L : Language Bool} (h : IsDeterministicContextFree L) :
    L.IsContextFree :=
  h.isContextFree

end Cslib.Language.CFLTests
