/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.FullBuchi

/-!
# An exponential bound on the Büchi automaton of an LTL formula

The truth-annotation tableau of `CSLibExt.Logics.LTL.Tableau` has one Boolean per syntactic
occurrence of the formula, so it has exactly `2 ^ |φ|` states, where `|φ|` is the number of
occurrences (`Cslib.LTL.Formula.size`). Degeneralization multiplies this by the number of
until occurrences plus one, which is at most `|φ|`. Hence every LTL formula is recognized
by a nondeterministic Büchi automaton with at most `4 ^ |φ| = 2 ^ (2 |φ|)` states: the
`2^{O(|φ|)}` bound of the Vardi–Wolper translation.

* `Cslib.LTL.Formula.size`: number of occurrences of primitive connectives and atoms.
* `Cslib.LTL.Tableau.natCard_state`: the tableau has exactly `2 ^ |φ|` states.
* `Cslib.LTL.Tableau.obligationCount_lt_size`: fewer than `|φ|` fairness obligations.
* `Cslib.LTL.Tableau.natCard_buchi_state_le`: the degeneralized automaton has at most
  `4 ^ |φ|` states.
* `Cslib.LTL.exists_buchi_card_le`: every LTL formula has a Büchi automaton with at most
  `4 ^ |φ|` states.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Corollary 23 (author's posted version `banff94rj.pdf`).
* M. Y. Vardi and P. Wolper, "Reasoning about infinite computations", *Information and
  Computation* 115 (1994), 1-37.
-/

@[expose] public section

namespace Cslib.LTL

variable {Atom Symbol : Type*}

namespace Formula

/-- **Size of an LTL formula.** The number of occurrences of atoms and primitive connectives
(truth, negation, conjunction, next and until) in the formula, that is, the number of nodes
of its syntax tree. Derived connectives count with their definitions: `eventually φ` is
`top U φ` and has size `|φ| + 2`. -/
def size : Formula Atom → ℕ
  | .atom _ => 1
  | .top => 1
  | .not φ => size φ + 1
  | .and φ ψ => size φ + size ψ + 1
  | .next φ => size φ + 1
  | .until φ ψ => size φ + size ψ + 1

/-- **Formulas have positive size.** Every LTL formula has at least one occurrence. -/
theorem one_le_size (φ : Formula Atom) : 1 ≤ size φ := by
  cases φ <;> simp [size]

end Formula

namespace Tableau

/-- **Exact state count of the LTL tableau.** The truth-annotation states of the
tableau of `φ` carry one Boolean per syntactic occurrence, so there are `2 ^ |φ|` of them,
where `|φ|` is `Cslib.LTL.Formula.size φ`. This is the exponential state space of the
Vardi–Wolper construction (Vardi, "An automata-theoretic approach to linear temporal logic",
LNCS 1043, 1996, Corollary 23). -/
theorem natCard_state : ∀ φ : Formula Atom, Nat.card (State φ) = 2 ^ φ.size
  | .atom _ => by simp [State, Formula.size]
  | .top => by simp [State, Formula.size]
  | .not φ => by
      rw [show State (.not φ) = (Bool × State φ) from rfl, Nat.card_prod, natCard_state φ]
      simp [Formula.size, pow_succ, mul_comm]
  | .and φ ψ => by
      rw [show State (.and φ ψ) = (Bool × (State φ × State ψ)) from rfl, Nat.card_prod,
        Nat.card_prod, natCard_state φ, natCard_state ψ]
      simp [Formula.size, pow_succ, pow_add, mul_comm]
  | .next φ => by
      rw [show State (.next φ) = (Bool × State φ) from rfl, Nat.card_prod, natCard_state φ]
      simp [Formula.size, pow_succ, mul_comm]
  | .until φ ψ => by
      rw [show State (.until φ ψ) = (Bool × (State φ × State ψ)) from rfl, Nat.card_prod,
        Nat.card_prod, natCard_state φ, natCard_state ψ]
      simp [Formula.size, pow_succ, pow_add, mul_comm]

/-- **Fairness obligations are fewer than the formula size.** The number of until occurrences
of an LTL formula, which is the number of generalized Büchi acceptance sets of its tableau, is
strictly smaller than its size, since every formula has at least one atom or truth leaf. -/
theorem obligationCount_lt_size : ∀ φ : Formula Atom, obligationCount φ < φ.size
  | .atom _ => by simp [obligationCount, Formula.size]
  | .top => by simp [obligationCount, Formula.size]
  | .not φ => by
      have := obligationCount_lt_size φ
      simp only [obligationCount, Formula.size]
      omega
  | .and φ ψ => by
      have := obligationCount_lt_size φ
      have := obligationCount_lt_size ψ
      simp only [obligationCount, Formula.size]
      omega
  | .next φ => by
      have := obligationCount_lt_size φ
      simp only [obligationCount, Formula.size]
      omega
  | .until φ ψ => by
      have := obligationCount_lt_size φ
      have := obligationCount_lt_size ψ
      simp only [obligationCount, Formula.size]
      omega

/-- **Exponential state bound for the Büchi automaton of an LTL formula.** The degeneralized
tableau `Cslib.LTL.Tableau.buchi`, whose states are a truth annotation and a fairness counter,
has at most `|φ| · 2 ^ |φ| ≤ 4 ^ |φ|` states (Vardi, "An automata-theoretic approach to linear
temporal logic", LNCS 1043, 1996, Corollary 23: `2^{O(|φ|)}` states). -/
theorem natCard_buchi_state_le (φ : Formula Atom) :
    Nat.card (State φ × Fin (obligationCount φ + 1)) ≤ 4 ^ φ.size := by
  rw [Nat.card_prod, natCard_state, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h1 : obligationCount φ + 1 ≤ φ.size := obligationCount_lt_size φ
  have h2 : φ.size ≤ 2 ^ φ.size := (Nat.lt_two_pow_self).le
  calc 2 ^ φ.size * (obligationCount φ + 1) ≤ 2 ^ φ.size * 2 ^ φ.size :=
        Nat.mul_le_mul_left _ (h1.trans h2)
    _ = 4 ^ φ.size := by rw [← mul_pow]; norm_num

end Tableau

open Automata.ωAcceptor

/-- **Vardi–Wolper translation with an exponential state bound.** For every LTL formula `φ`
and valuation of its atoms on the input letters, some nondeterministic Büchi automaton with
at most `4 ^ |φ| = 2 ^ (2 |φ|)` states accepts exactly the infinite words satisfying `φ`
(Vardi, "An automata-theoretic approach to linear temporal logic", LNCS 1043, 1996,
Corollary 23, which states `2^{O(|φ|)}` states over the alphabet `2^Prop`; here the alphabet
is arbitrary and letters are read through `valuation`). -/
theorem exists_buchi_card_le (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S Symbol),
      Nat.card S ≤ 4 ^ φ.size ∧ language a = Word.language valuation φ :=
  ⟨Tableau.State φ × Fin (Tableau.obligationCount φ + 1), inferInstance,
    Tableau.buchi valuation φ, Tableau.natCard_buchi_state_le φ,
    Tableau.language_buchi valuation φ⟩

end Cslib.LTL
