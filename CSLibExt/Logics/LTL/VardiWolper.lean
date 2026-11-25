/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vardi-Wolper state bound for the LTL tableau
-/
module

public import CSLibExt.Logics.LTL.FullBuchi
public import CSLibExt.Logics.LTL.FragmentBuchi

/-!
# Vardi-Wolper state bound for the LTL tableau

The tableau construction of Vardi and Wolper (LICS 1986) represents states by
truth annotations of subformulas. The construction in
`CSLibExt.Logics.LTL.Tableau` uses one Boolean per syntactic occurrence, so a
formula of size `s` with `k` until-obligations has exactly `2 ^ s` annotation
states and `2 ^ s * (k + 1)` degeneralized Büchi states, at most
`2 ^ (2 * s)`. This file proves that count, gives the explicit state bound for
every formula, and gives the Büchi recognizer for the general safety fragment.
The exact constant in the
exponent is a property of this per-occurrence encoding; the source states the
asymptotic form `2 ^ O(|φ|)`.
-/

@[expose] public section

namespace Cslib
namespace LTL
namespace Tableau

variable {Atom : Type*}

/-- The size of an LTL formula (the number of connective occurrences plus the
number of atoms), an upper bound on the number of distinct subformulas. -/
def formulaSize : Formula Atom → ℕ
  | .atom _ => 1
  | .top => 1
  | .not φ => formulaSize φ + 1
  | .and φ ψ => formulaSize φ + formulaSize ψ + 1
  | .next φ => formulaSize φ + 1
  | .until φ ψ => formulaSize φ + formulaSize ψ + 1

/-- The tableau state type has one Boolean per syntactic occurrence, so its
cardinality is two to the formula size. -/
theorem card_state (φ : Formula Atom) :
    Nat.card (State φ) = 2 ^ formulaSize φ := by
  induction φ with
  | atom _ =>
      change Nat.card Bool = 2 ^ 1
      rw [Nat.card_eq_fintype_card, Fintype.card_bool, pow_one]
  | top =>
      change Nat.card Bool = 2 ^ 1
      rw [Nat.card_eq_fintype_card, Fintype.card_bool, pow_one]
  | not φ ih =>
      change Nat.card (Bool × State φ) = 2 ^ (formulaSize φ + 1)
      rw [Nat.card_prod, ih, Nat.card_eq_fintype_card, Fintype.card_bool, pow_succ]
      ring
  | and φ ψ ih1 ih2 =>
      change Nat.card (Bool × (State φ × State ψ)) = 2 ^ (formulaSize φ + formulaSize ψ + 1)
      rw [Nat.card_prod, Nat.card_prod, ih1, ih2, Nat.card_eq_fintype_card,
        Fintype.card_bool, pow_succ, pow_add]
      ring
  | next φ ih =>
      change Nat.card (Bool × State φ) = 2 ^ (formulaSize φ + 1)
      rw [Nat.card_prod, ih, Nat.card_eq_fintype_card, Fintype.card_bool, pow_succ]
      ring
  | «until» φ ψ ih1 ih2 =>
      change Nat.card (Bool × (State φ × State ψ)) = 2 ^ (formulaSize φ + formulaSize ψ + 1)
      rw [Nat.card_prod, Nat.card_prod, ih1, ih2, Nat.card_eq_fintype_card,
        Fintype.card_bool, pow_succ, pow_add]
      ring

/-- Until-obligations are a sub-count of all connective occurrences. -/
theorem obligationCount_le_formulaSize (φ : Formula Atom) :
    obligationCount φ ≤ formulaSize φ := by
  induction φ <;> simp only [obligationCount, formulaSize] <;> omega

/-- Arithmetic form of the degeneralization bound. -/
private theorem two_pow_mul_succ_le (n : ℕ) :
    2 ^ n * (n + 1) ≤ 2 ^ (2 * n) := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  calc 2 ^ n * (n + 1) ≤ 2 ^ n * 2 ^ n := by gcongr
    _ = 2 ^ (2 * n) := by rw [← pow_add, two_mul]

/-- The degeneralized Büchi state type (states times the fairness counter)
meets the bound `2 ^ (2 * formulaSize φ)` for this per-occurrence encoding;
the source states the bound in asymptotic form. -/
theorem card_tableau_state_le (φ : Formula Atom) :
    Nat.card (State φ × Fin (obligationCount φ + 1)) ≤ 2 ^ (2 * formulaSize φ) := by
  have h : obligationCount φ + 1 ≤ formulaSize φ + 1 := by
    have hle := obligationCount_le_formulaSize (φ := φ)
    omega
  rw [Nat.card_prod, card_state, Nat.card_fin]
  calc 2 ^ formulaSize φ * (obligationCount φ + 1)
      ≤ 2 ^ formulaSize φ * (formulaSize φ + 1) := by gcongr
    _ ≤ 2 ^ (2 * formulaSize φ) := two_pow_mul_succ_le _

end Tableau

/-- **Vardi-Wolper bound.** Every LTL formula is accepted by a nondeterministic
Büchi automaton with the same ω-language, over the alphabet `Set Atom` of atom
valuations, with at most `2 ^ (2 * formulaSize φ)` states. Source: M. Y. Vardi
and P. Wolper, "An automata-theoretic approach to automatic program
verification", Proceedings of LICS 1986, 332-344. The concrete constant in
the exponent is a property of this per-occurrence encoding; the source states
the bound in asymptotic form. -/
theorem vardi_wolper {Atom : Type*} (φ : Formula Atom) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set Atom)),
      Automata.ωAcceptor.language a = Word.language (fun s a => a ∈ s) φ ∧
        Nat.card S ≤ 2 ^ (2 * Tableau.formulaSize φ) :=
  ⟨Tableau.State φ × Fin (Tableau.obligationCount φ + 1), inferInstance,
    Tableau.buchi (fun s a => a ∈ s) φ, Tableau.language_buchi _ φ,
    Tableau.card_tableau_state_le φ⟩

/-- The general safety fragment of LTL: propositional formulas, conjunction,
disjunction, next, and `always` applied to an arbitrary safety formula. -/
inductive SafetyExt (Atom : Type*) where
  /-- A propositional formula, checked on the first letter. -/
  | prop (φ : PropFormula Atom) : SafetyExt Atom
  /-- Conjunction. -/
  | and (ψ ρ : SafetyExt Atom) : SafetyExt Atom
  /-- Disjunction. -/
  | or (ψ ρ : SafetyExt Atom) : SafetyExt Atom
  /-- Next. -/
  | next (ψ : SafetyExt Atom) : SafetyExt Atom
  /-- `always` of a safety formula. -/
  | always (ψ : SafetyExt Atom) : SafetyExt Atom

namespace SafetyExt

/-- A general safety formula as an LTL formula. -/
def toLTL {Atom : Type*} : SafetyExt Atom → Formula Atom
  | .prop φ => φ.toLTL
  | .and ψ ρ => .and ψ.toLTL ρ.toLTL
  | .or ψ ρ => Formula.or ψ.toLTL ρ.toLTL
  | .next ψ => .next ψ.toLTL
  | .always ψ => Formula.always ψ.toLTL

end SafetyExt

/-- **Büchi automata for the general safety fragment.** Every general safety
formula has a nondeterministic Büchi automaton with finitely many states and
with the same ω-language, as a corollary of the full tableau recognizer. The
stronger safety-automaton form of O. Kupferman and M. Y. Vardi, "Model
checking of safety properties", Formal Methods in System Design 19 (2001),
291-314, with all states accepting, is not proved here; it remains a wanted
statement (`LTLSafetyAutomatonWanted`). -/
theorem safety_general_buchi {Atom : Type*} (ψ : SafetyExt Atom) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set Atom)),
      Automata.ωAcceptor.language a = Word.language (fun s a => a ∈ s) ψ.toLTL :=
  exists_buchi (fun s a => a ∈ s) ψ.toLTL

end LTL
end Cslib
