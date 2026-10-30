/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Relation

/-!
# Propositional dynamic logic (PDL)

PDL (Fischer and Ladner, *Propositional dynamic logic of regular programs*,
JCSS 1979) extends modal logic with a regular program combinator layer:
programs are built from atomic actions by sequencing, choice, iteration
(`star`), and tests; formulas add `[α]φ`, "every `α`-execution ends in a
state satisfying `φ`". Programs denote binary relations on worlds, with
`star` as the reflexive-transitive closure, and tests as the sub-identity
relation on states satisfying the tested formula.

Main results: the standard program laws, as validities on every model:

* `sat_box_seq`: `[α;β]φ ↔ [α][β]φ`.
* `sat_box_choice`: `[α ∪ β]φ ↔ [α]φ ∧ [β]φ`.
* `sat_box_star_unfold`: `[α*]φ ↔ φ ∧ [α][α*]φ`.
* `sat_box_test`: `[ψ?]φ ↔ (ψ → φ)`.

Plus a concrete calculation on the toggle model: `[a;a]p` fails at
`false`, since two flips return to `false` where `p` is false.
-/

@[expose] public section

namespace Cslib
namespace PDL

universe u v w

/-- A PDL model: an accessibility relation per atomic action, and an
atom valuation. -/
structure Model (World : Type u) (Atom : Type v) (Label : Type w) where
  /-- One accessibility relation per atomic program label. -/
  rel : Label → World → World → Prop
  /-- The atoms true at each world. -/
  valuation : World → Atom → Prop

mutual
/-- Formulas of PDL: atoms, falsity, implication, and `[α]φ`. -/
inductive Formula (Atom : Type v) (Label : Type w) where
  | atom (a : Atom) : Formula Atom Label
  | bot : Formula Atom Label
  | imp (φ ψ : Formula Atom Label) : Formula Atom Label
  | box (α : Program Atom Label) (φ : Formula Atom Label) : Formula Atom Label

/-- Programs of PDL: atomic actions, sequencing, choice, iteration, tests. -/
inductive Program (Atom : Type v) (Label : Type w) where
  | atomic (a : Label) : Program Atom Label
  | seq (α β : Program Atom Label) : Program Atom Label
  | choice (α β : Program Atom Label) : Program Atom Label
  | star (α : Program Atom Label) : Program Atom Label
  | test (φ : Formula Atom Label) : Program Atom Label
end

/-- Possibility as the dual of necessity. -/
def Formula.dia {Atom Label : Type*} (α : Program Atom Label) (φ : Formula Atom Label) :
    Formula Atom Label :=
  .imp (.box α (.imp φ .bot)) .bot

mutual
/-- The relation a program denotes on a model. `star` is the
reflexive-transitive closure; a test is the sub-identity on states
satisfying the tested formula. -/
def ProgRel {World Atom Label : Type*} (M : Model World Atom Label) :
    Program Atom Label → World → World → Prop
  | .atomic a, w, v => M.rel a w v
  | .seq α β, w, v => ∃ u, ProgRel M α w u ∧ ProgRel M β u v
  | .choice α β, w, v => ProgRel M α w v ∨ ProgRel M β w v
  | .star α, w, v => Relation.ReflTransGen (ProgRel M α) w v
  | .test φ, w, v => w = v ∧ Sat M φ w

/-- Satisfaction of a PDL formula at a world. -/
def Sat {World Atom Label : Type*} (M : Model World Atom Label) :
    Formula Atom Label → World → Prop
  | .atom a, w => M.valuation w a
  | .bot, _ => False
  | .imp φ ψ, w => Sat M φ w → Sat M ψ w
  | .box α φ, w => ∀ v, ProgRel M α w v → Sat M φ v
end

variable {World Atom Label : Type*} (M : Model World Atom Label)
  {α β : Program Atom Label} {φ ψ : Formula Atom Label} {w : World}

/-- `[α;β]φ ↔ [α][β]φ`: sequencing composes the relations. -/
theorem sat_box_seq :
    Sat M (.box (.seq α β) φ) w ↔ Sat M (.box α (.box β φ)) w := by
  constructor
  · intro h v hα u hβ
    exact h u ⟨v, hα, hβ⟩
  · intro h v hseq
    obtain ⟨u, hα, hβ⟩ := hseq
    exact h u hα v hβ

/-- `[α ∪ β]φ ↔ [α]φ ∧ [β]φ`: choice is the union of the relations. -/
theorem sat_box_choice :
    Sat M (.box (.choice α β) φ) w ↔
      Sat M (.box α φ) w ∧ Sat M (.box β φ) w := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hα, hβ⟩ v (hα' | hβ')
    · exact hα v hα'
    · exact hβ v hβ'

/-- `[α*]φ ↔ φ ∧ [α][α*]φ`: iteration unfolds to the exit case plus
one more step. -/
theorem sat_box_star_unfold :
    Sat M (.box (.star α) φ) w ↔
      Sat M φ w ∧ Sat M (.box α (.box (.star α) φ)) w := by
  constructor
  · intro h
    refine ⟨h w Relation.ReflTransGen.refl, fun v hα u hrtc => ?_⟩
    exact h u (Relation.ReflTransGen.head hα hrtc)
  · rintro ⟨h0, hstep⟩ v hrtc
    have key : ∀ {a b : World}, Relation.ReflTransGen (ProgRel M α) a b →
        Sat M φ a → Sat M (Formula.box α (Formula.box (.star α) φ)) a →
        Sat M φ b := by
      intro a b hrtc
      induction hrtc using Relation.ReflTransGen.head_induction_on with
      | refl => intro hφ _; exact hφ
      | head hα hrest _ => intro _ hst; exact hst _ hα _ hrest
    exact key hrtc h0 hstep

/-- `[ψ?]φ ↔ (ψ → φ)`: a test either blocks (when `ψ` fails) or leaves
the state unchanged. -/
theorem sat_box_test :
    Sat M (.box (.test ψ) φ) w ↔ (Sat M ψ w → Sat M φ w) := by
  constructor
  · intro h hψ
    exact h w ⟨rfl, hψ⟩
  · intro h v ⟨rfl, hψ⟩
    exact h hψ

/-- The toggle model: one atomic action flips the state, `p` holds at
`true`. -/
def toggleModel : Model Bool Unit Unit where
  rel := fun _ s t => t = !s
  valuation := fun s _ => s = true

/-- On the toggle model, `[a;a]p` fails at `false`: two flips return to
`false`, where `p` is false. -/
theorem toggle_not_box_seq_atom :
    ¬ Sat toggleModel
      (.box (.seq (.atomic ()) (.atomic ())) (.atom ())) false := by
  intro h
  have hwit : ProgRel toggleModel (.seq (.atomic ()) (.atomic ())) false false :=
    ⟨true, rfl, rfl⟩
  exact Bool.false_ne_true (h false hwit)

end PDL
end Cslib
