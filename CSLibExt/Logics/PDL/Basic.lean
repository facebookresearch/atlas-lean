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

/-- **PDL model.** A model of propositional dynamic logic with set of worlds $W$ consists of a
binary accessibility relation $R_a$ on $W$ for each atomic action label $a$, and a valuation that
says which atoms are true at each world. -/
structure Model (World : Type u) (Atom : Type v) (Label : Type w) where
  /-- One accessibility relation per atomic program label. -/
  rel : Label → World → World → Prop
  /-- The atoms true at each world. -/
  valuation : World → Atom → Prop

mutual
/-- **PDL formulas.** The formulas of propositional dynamic logic over a type of atoms and a type
of atomic action labels are the atoms $p$, falsity $\bot$, implications $\varphi \to \psi$ of
formulas, and boxes $[\alpha]\varphi$ of a program $\alpha$ and a formula $\varphi$. Formulas and
programs are defined by simultaneous induction. -/
inductive Formula (Atom : Type v) (Label : Type w) where
  | atom (a : Atom) : Formula Atom Label
  | bot : Formula Atom Label
  | imp (φ ψ : Formula Atom Label) : Formula Atom Label
  | box (α : Program Atom Label) (φ : Formula Atom Label) : Formula Atom Label

/-- **PDL programs.** The programs of propositional dynamic logic over a type of atoms and a type
of atomic action labels are the atomic actions $a$, sequential compositions $\alpha ; \beta$,
nondeterministic choices $\alpha \cup \beta$, iterations $\alpha^*$, and tests $\varphi?$ of a
formula $\varphi$. Programs and formulas are defined by simultaneous induction. -/
inductive Program (Atom : Type v) (Label : Type w) where
  | atomic (a : Label) : Program Atom Label
  | seq (α β : Program Atom Label) : Program Atom Label
  | choice (α β : Program Atom Label) : Program Atom Label
  | star (α : Program Atom Label) : Program Atom Label
  | test (φ : Formula Atom Label) : Program Atom Label
end

/-- **Possibility in PDL.** For a program $\alpha$ and a formula $\varphi$, the formula
$\langle\alpha\rangle\varphi$ is defined as $[\alpha](\varphi \to \bot) \to \bot$, that is, as
$\neg[\alpha]\neg\varphi$: possibility is the dual of necessity. -/
def Formula.dia {Atom Label : Type*} (α : Program Atom Label) (φ : Formula Atom Label) :
    Formula Atom Label :=
  .imp (.box α (.imp φ .bot)) .bot

mutual
/-- **Relation denoted by a PDL program.** In a model $M$, each program $\alpha$ denotes a binary
relation $R_\alpha$ on worlds: an atomic action $a$ denotes its accessibility relation $R_a$;
$(w, v) \in R_{\alpha;\beta}$ iff $(w, u) \in R_\alpha$ and $(u, v) \in R_\beta$ for some world
$u$; $R_{\alpha \cup \beta} = R_\alpha \cup R_\beta$; $R_{\alpha^*}$ is the reflexive-transitive
closure of $R_\alpha$; and $(w, v) \in R_{\varphi?}$ iff $w = v$ and $\varphi$ holds at $w$ in
$M$. -/
def ProgRel {World Atom Label : Type*} (M : Model World Atom Label) :
    Program Atom Label → World → World → Prop
  | .atomic a, w, v => M.rel a w v
  | .seq α β, w, v => ∃ u, ProgRel M α w u ∧ ProgRel M β u v
  | .choice α β, w, v => ProgRel M α w v ∨ ProgRel M β w v
  | .star α, w, v => Relation.ReflTransGen (ProgRel M α) w v
  | .test φ, w, v => w = v ∧ Sat M φ w

/-- **Satisfaction of PDL formulas.** Truth of a formula at a world $w$ of a model $M$ is defined
by recursion: an atom $p$ holds at $w$ iff the valuation of $M$ makes $p$ true at $w$; $\bot$
holds nowhere; $\varphi \to \psi$ holds at $w$ iff $\psi$ holds at $w$ whenever $\varphi$ does;
and $[\alpha]\varphi$ holds at $w$ iff $\varphi$ holds at every world $v$ with
$(w, v) \in R_\alpha$, where $R_\alpha$ is the relation denoted by $\alpha$ in $M$. -/
def Sat {World Atom Label : Type*} (M : Model World Atom Label) :
    Formula Atom Label → World → Prop
  | .atom a, w => M.valuation w a
  | .bot, _ => False
  | .imp φ ψ, w => Sat M φ w → Sat M ψ w
  | .box α φ, w => ∀ v, ProgRel M α w v → Sat M φ v
end

variable {World Atom Label : Type*} (M : Model World Atom Label)
  {α β : Program Atom Label} {φ ψ : Formula Atom Label} {w : World}

/-- **Box of a sequential composition.** For every model $M$, world $w$, programs $\alpha$ and
$\beta$, and formula $\varphi$, the formula $[\alpha;\beta]\varphi$ holds at $w$ if and only if
$[\alpha][\beta]\varphi$ holds at $w$. -/
theorem sat_box_seq :
    Sat M (.box (.seq α β) φ) w ↔ Sat M (.box α (.box β φ)) w := by
  constructor
  · intro h v hα u hβ
    exact h u ⟨v, hα, hβ⟩
  · intro h v hseq
    obtain ⟨u, hα, hβ⟩ := hseq
    exact h u hα v hβ

/-- **Box of a choice.** For every model $M$, world $w$, programs $\alpha$ and $\beta$, and formula
$\varphi$, the formula $[\alpha \cup \beta]\varphi$ holds at $w$ if and only if both
$[\alpha]\varphi$ and $[\beta]\varphi$ hold at $w$. -/
theorem sat_box_choice :
    Sat M (.box (.choice α β) φ) w ↔
      Sat M (.box α φ) w ∧ Sat M (.box β φ) w := by
  constructor
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hα, hβ⟩ v (hα' | hβ')
    · exact hα v hα'
    · exact hβ v hβ'

/-- **Unfolding the box of an iteration.** For every model $M$, world $w$, program $\alpha$ and
formula $\varphi$, the formula $[\alpha^*]\varphi$ holds at $w$ if and only if $\varphi$ holds at
$w$ and $[\alpha][\alpha^*]\varphi$ holds at $w$. -/
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

/-- **Box of a test.** For every model $M$, world $w$ and formulas $\psi$ and $\varphi$, the formula
$[\psi?]\varphi$ holds at $w$ if and only if $\varphi$ holds at $w$ whenever $\psi$ holds at $w$. -/
theorem sat_box_test :
    Sat M (.box (.test ψ) φ) w ↔ (Sat M ψ w → Sat M φ w) := by
  constructor
  · intro h hψ
    exact h w ⟨rfl, hψ⟩
  · intro h v ⟨rfl, hψ⟩
    exact h hψ

/-- **The toggle model.** The PDL model whose worlds are the two Booleans $\mathsf{true}$ and
$\mathsf{false}$, with a single atomic action $a$ and a single atom $p$: the action $a$ relates
each world $s$ exactly to its negation $\lnot s$, and $p$ holds exactly at $\mathsf{true}$. -/
def toggleModel : Model Bool Unit Unit where
  rel := fun _ s t => t = !s
  valuation := fun s _ => s = true

/-- **Failure of $[a;a]\,p$ in the toggle model.** In the toggle model, with atomic action $a$
and atom $p$, the formula $[a;a]\,p$ is not satisfied at the world $\mathsf{false}$.

Performing $a$ twice leads from $\mathsf{false}$ back to $\mathsf{false}$, where $p$ is false. -/
theorem toggle_not_box_seq_atom :
    ¬ Sat toggleModel
      (.box (.seq (.atomic ()) (.atomic ())) (.atom ())) false := by
  intro h
  have hwit : ProgRel toggleModel (.seq (.atomic ()) (.atomic ())) false false :=
    ⟨true, rfl, rfl⟩
  exact Bool.false_ne_true (h false hwit)

end PDL
end Cslib
