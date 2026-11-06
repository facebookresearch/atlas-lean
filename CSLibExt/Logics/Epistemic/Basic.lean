/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Relation


/-!
# Epistemic logic: multi-agent S5

Epistemic logic (Hintikka, *Knowledge and Belief*, 1962) is basic modal
logic with one accessibility relation per agent: `Kᵢ φ` reads "agent `i`
knows `φ`". On models where every agent's relation is reflexive,
transitive, and euclidean (an equivalence relation), the S5 axioms are
valid: truth (`Kᵢ φ → φ`), positive introspection
(`Kᵢ φ → Kᵢ Kᵢ φ`), and negative introspection
(`¬Kᵢ φ → Kᵢ ¬Kᵢ φ`), together with the distribution axiom K.

Main results: `valid_know_dist`, `valid_know_truth`, `valid_know_pos`,
`valid_know_neg`. The concrete example is a two-agent model where agent
`0` sees a coin and agent `1` does not: agent `1` does not know whether
the coin is heads, but knows that agent `0` does
(`muddy_know_one_knows_whether`).
-/

@[expose] public section

namespace Cslib
namespace Epistemic

universe u v w

/-- **Epistemic models.** Given a type of worlds $W$, a type of atoms and a type of agents, an
epistemic model consists of a binary accessibility relation $R_i$ on $W$ for each agent $i$ and a
valuation assigning to each world the atoms true there; the world type $W$ is required to be
nonempty.

Nonemptiness is assumed as for Kripke models: with no worlds, validity would hold vacuously and
even $\bot$ would be valid. -/
structure Model (World : Type u) (Atom : Type v) (Agent : Type w) where
  /-- One accessibility relation per agent. -/
  rel : Agent → World → World → Prop
  /-- The atoms true at each world. -/
  valuation : World → Atom → Prop
  /-- There is at least one world. -/
  nonempty_world : Nonempty World

/-- **Epistemic formulas.** Given a type of atoms and a type of agents, the formulas of epistemic
logic are built inductively: every atom $p$ is a formula, falsity $\bot$ is a formula, if $\varphi$
and $\psi$ are formulas then so is the implication $\varphi \to \psi$, and if $\varphi$ is a
formula and $i$ is an agent then $K_i \varphi$ (read "agent $i$ knows $\varphi$") is a formula. -/
inductive Formula (Atom : Type v) (Agent : Type w) where
  | atom (a : Atom) : Formula Atom Agent
  | bot : Formula Atom Agent
  | imp (φ ψ : Formula Atom Agent) : Formula Atom Agent
  | know (i : Agent) (φ : Formula Atom Agent) : Formula Atom Agent

namespace Formula

/-- **Negation of epistemic formulas.** The negation $\neg\varphi$ of an epistemic formula
$\varphi$ is the implication $\varphi \to \bot$. -/
def not {Atom : Type*} {Agent : Type*} (φ : Formula Atom Agent) : Formula Atom Agent := .imp φ .bot

/-- **Disjunction of epistemic formulas.** The disjunction $\varphi \lor \psi$ of epistemic
formulas $\varphi$ and $\psi$ is the implication $\neg\varphi \to \psi$. -/
def or {Atom : Type*} {Agent : Type*} (φ ψ : Formula Atom Agent) : Formula Atom Agent :=
  .imp (.not φ) ψ

end Formula

/-- **Satisfaction in an epistemic model.** Satisfaction of an epistemic formula at a world $w$
of a model $M$ is defined by recursion on the formula, writing $R_i$ for the accessibility
relation of agent $i$ in $M$ and $K_i \varphi$ for the formula "agent $i$ knows $\varphi$": an
atom $a$ holds at $w$ when the valuation of $M$ makes $a$ true at $w$; $\bot$ holds at no world;
$\varphi \to \psi$ holds at $w$ when $\psi$ holds at $w$ whenever $\varphi$ does; and
$K_i \varphi$ holds at $w$ when $\varphi$ holds at every world $v$ with $w \mathrel{R_i} v$. -/
def Sat {World Atom Agent : Type*} (M : Model World Atom Agent) :
    Formula Atom Agent → World → Prop
  | .atom a, w => M.valuation w a
  | .bot, _ => False
  | .imp φ ψ, w => Sat M φ w → Sat M ψ w
  | .know i φ, w => ∀ v, M.rel i w v → Sat M φ v

/-- **Validity in an epistemic model.** A formula $\varphi$ is valid in an epistemic model $M$
when $\varphi$ is satisfied at every world of $M$. -/
def Valid {World Atom Agent : Type*} (M : Model World Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ w, Sat M φ w

/-- **Falsity is not valid in an epistemic model.** In every epistemic model, the formula $\bot$
is not valid: it fails at some world.

The nonempty world set rules out vacuous validity. -/
theorem not_valid_bot {World Atom Agent : Type*} (M : Model World Atom Agent) :
    ¬ Valid M .bot := by
  intro h
  obtain ⟨w⟩ := M.nonempty_world
  exact h w

variable {World Atom Agent : Type*} (M : Model World Atom Agent)
  {i : Agent} {φ ψ : Formula Atom Agent} {w : World}

/-- **Satisfaction of a disjunction.** In an epistemic model $M$, the disjunction
$\varphi \lor \psi$ of two formulas, defined as $\neg \varphi \to \psi$, is satisfied at a world
$w$ if and only if $\varphi$ is satisfied at $w$ or $\psi$ is satisfied at $w$. -/
theorem sat_or :
    Sat M (.or φ ψ) w ↔ Sat M φ w ∨ Sat M ψ w := by
  constructor
  · intro h
    exact Classical.byCases (fun hφ => Or.inl hφ) (fun hφ => Or.inr (h hφ))
  · rintro (hφ | hψ) hnot
    · exact (hnot hφ).elim
    · exact hψ

/-- **Distribution axiom K.** Write $K_i \varphi$ for "agent $i$ knows $\varphi$". For every
epistemic model $M$, every agent $i$ and all formulas $\varphi$ and $\psi$, the formula
$K_i (\varphi \to \psi) \to (K_i \varphi \to K_i \psi)$ is valid in $M$: knowledge distributes
over implication. -/
theorem valid_know_dist :
    Valid M (.imp (.know i (.imp φ ψ)) (.imp (.know i φ) (.know i ψ))) := by
  intro w hK hφ v hv
  exact hK v hv (hφ v hv)

/-- **Truth axiom T.** Write $K_i \varphi$ for "agent $i$ knows $\varphi$". Let $M$ be an
epistemic model in which the accessibility relation $R_i$ of agent $i$ is reflexive. Then for
every formula $\varphi$, the formula $K_i \varphi \to \varphi$ is valid in $M$. -/
theorem valid_know_truth (hrefl : ∀ v, M.rel i v v) :
    Valid M (.imp (.know i φ) φ) := by
  intro w hK
  exact hK w (hrefl w)

/-- **Positive introspection axiom 4.** Write $K_i \varphi$ for "agent $i$ knows $\varphi$".
Let $M$ be an epistemic model in which the accessibility relation $R_i$ of agent $i$ is
transitive. Then for every formula $\varphi$, the formula $K_i \varphi \to K_i K_i \varphi$ is
valid in $M$. -/
theorem valid_know_pos
    (htrans : ∀ {a b c}, M.rel i a b → M.rel i b c → M.rel i a c) :
    Valid M (.imp (.know i φ) (.know i (.know i φ))) := by
  intro w hK v hvw u huv
  exact hK u (htrans hvw huv)

/-- **Negative introspection axiom 5.** Write $K_i \varphi$ for "agent $i$ knows $\varphi$".
Let $M$ be an epistemic model in which the accessibility relation $R_i$ of agent $i$ is
euclidean: for all worlds $a$, $b$, $c$, if $a \mathrel{R_i} b$ and $a \mathrel{R_i} c$ then
$b \mathrel{R_i} c$. Then for every formula $\varphi$, the formula
$\neg K_i \varphi \to K_i \neg K_i \varphi$ is valid in $M$. -/
theorem valid_know_neg
    (heucl : ∀ {a b c}, M.rel i a b → M.rel i a c → M.rel i b c) :
    Valid M (.imp (.not (.know i φ)) (.know i (.not (.know i φ)))) := by
  intro w hNot v hvw hK
  apply hNot
  intro u hwu
  exact hK u (heucl hvw hwu)

/-- **The two-agent coin model.** The epistemic model whose worlds are the two booleans, with
$\mathrm{true}$ read as heads and $\mathrm{false}$ as tails, with a single atom $p$ true exactly
at the heads world, and with two agents $0$ and $1$: agent $0$ sees the coin, so its
accessibility relation is equality of worlds, and agent $1$ does not, so its accessibility
relation relates every pair of worlds. -/
def muddy : Model Bool Unit (Fin 2) where
  rel := fun i w v => if i = 0 then w = v else True
  valuation := fun w _ => w = true
  nonempty_world := ⟨true⟩

/-- **Agent 0 knows the coin is heads exactly at heads.** Let $p$ be the atom "the coin is heads"
of the two-agent coin model. At a world $v$ of that model, the formula $K_0 p$ holds if and only
if $v$ is the heads world: agent $0$ sees the coin. -/
theorem sat_know_zero_atom (v : Bool) :
    Sat muddy (.know 0 (.atom ())) v ↔ v = true := by
  constructor
  · intro h
    exact h v (by simp [muddy])
  · intro hv u hu
    simp [muddy] at hu
    rw [← hu]
    exact hv

/-- **Agent 0 knows the coin is tails exactly at tails.** Let $p$ be the atom "the coin is heads"
of the two-agent coin model. At a world $v$ of that model, the formula $K_0 \neg p$ holds if and
only if $v$ is the tails world. -/
theorem sat_know_zero_not_atom (v : Bool) :
    Sat muddy (.know 0 (.not (.atom ()))) v ↔ v = false := by
  constructor
  · intro h
    cases v with
    | false => rfl
    | true =>
        exact False.elim (h true (by simp [muddy]) rfl)
  · intro hv u hu
    simp [muddy] at hu
    intro htu
    rw [← hu, hv] at htu
    exact Bool.false_ne_true htu

/-- **Agent 1 does not know that the coin is heads.** Let $p$ be the atom "the coin is heads" of
the two-agent coin model. The formula $K_1 p$ is false at the heads world: agent $1$ considers
the tails world possible. -/
theorem muddy_not_know_one_p_true :
    ¬ Sat muddy (.know 1 (.atom ())) true := by
  intro h
  have hfalse := h false (by simp [muddy])
  exact Bool.false_ne_true hfalse

/-- **Agent 1 knows that agent 0 knows whether the coin is heads.** Let $p$ be the atom "the coin
is heads" of the two-agent coin model. At every world of that model the formula
$K_1(K_0 p \lor K_0 \neg p)$ holds: agent $1$ knows that agent $0$ either knows $p$ or knows
$\neg p$. -/
theorem muddy_know_one_knows_whether (w : Bool) :
    Sat muddy (.know 1 (.or (.know 0 (.atom ()))
      (.know 0 (.not (.atom ()))))) w := by
  intro v _
  rw [sat_or]
  cases v with
  | false => exact Or.inr ((sat_know_zero_not_atom false).mpr rfl)
  | true => exact Or.inl ((sat_know_zero_atom true).mpr rfl)

end Epistemic
end Cslib
