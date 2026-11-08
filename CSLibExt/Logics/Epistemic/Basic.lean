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

/-- An epistemic model: one accessibility relation per agent, and an
atom valuation. The world set is nonempty, as in
`Cslib.Modal.KripkeModel`: with an empty world set, validity would hold
vacuously and even `⊥` would be valid. -/
structure Model (World : Type u) (Atom : Type v) (Agent : Type w) where
  /-- One accessibility relation per agent. -/
  rel : Agent → World → World → Prop
  /-- The atoms true at each world. -/
  valuation : World → Atom → Prop
  /-- There is at least one world. -/
  nonempty_world : Nonempty World

/-- Formulas of epistemic logic: atoms, falsity, implication, and
`Kᵢ φ`. -/
inductive Formula (Atom : Type v) (Agent : Type w) where
  | atom (a : Atom) : Formula Atom Agent
  | bot : Formula Atom Agent
  | imp (φ ψ : Formula Atom Agent) : Formula Atom Agent
  | know (i : Agent) (φ : Formula Atom Agent) : Formula Atom Agent

namespace Formula

/-- Negation as implication into falsity. -/
def not {Atom : Type*} {Agent : Type*} (φ : Formula Atom Agent) : Formula Atom Agent := .imp φ .bot

/-- Disjunction via implication. -/
def or {Atom : Type*} {Agent : Type*} (φ ψ : Formula Atom Agent) : Formula Atom Agent :=
  .imp (.not φ) ψ

end Formula

/-- Satisfaction of an epistemic formula at a world. -/
def Sat {World Atom Agent : Type*} (M : Model World Atom Agent) :
    Formula Atom Agent → World → Prop
  | .atom a, w => M.valuation w a
  | .bot, _ => False
  | .imp φ ψ, w => Sat M φ w → Sat M ψ w
  | .know i φ, w => ∀ v, M.rel i w v → Sat M φ v

/-- A formula is valid in a model when it holds at every world. -/
def Valid {World Atom Agent : Type*} (M : Model World Atom Agent) (φ : Formula Atom Agent) : Prop :=
  ∀ w, Sat M φ w

/-- Falsity is not valid: the nonempty world set rules out vacuous
validity. -/
theorem not_valid_bot {World Atom Agent : Type*} (M : Model World Atom Agent) :
    ¬ Valid M .bot := by
  intro h
  obtain ⟨w⟩ := M.nonempty_world
  exact h w

variable {World Atom Agent : Type*} (M : Model World Atom Agent)
  {i : Agent} {φ ψ : Formula Atom Agent} {w : World}

/-- Disjunction unfolds to the classical case split. -/
theorem sat_or :
    Sat M (.or φ ψ) w ↔ Sat M φ w ∨ Sat M ψ w := by
  constructor
  · intro h
    exact Classical.byCases (fun hφ => Or.inl hφ) (fun hφ => Or.inr (h hφ))
  · rintro (hφ | hψ) hnot
    · exact (hnot hφ).elim
    · exact hψ

/-- K axiom: knowledge distributes over implication. -/
theorem valid_know_dist :
    Valid M (.imp (.know i (.imp φ ψ)) (.imp (.know i φ) (.know i ψ))) := by
  intro w hK hφ v hv
  exact hK v hv (hφ v hv)

/-- T axiom: knowledge is true, on reflexive relations. -/
theorem valid_know_truth (hrefl : ∀ v, M.rel i v v) :
    Valid M (.imp (.know i φ) φ) := by
  intro w hK
  exact hK w (hrefl w)

/-- 4 axiom: positive introspection, on transitive relations. -/
theorem valid_know_pos
    (htrans : ∀ {a b c}, M.rel i a b → M.rel i b c → M.rel i a c) :
    Valid M (.imp (.know i φ) (.know i (.know i φ))) := by
  intro w hK v hvw u huv
  exact hK u (htrans hvw huv)

/-- 5 axiom: negative introspection, on euclidean relations. -/
theorem valid_know_neg
    (heucl : ∀ {a b c}, M.rel i a b → M.rel i a c → M.rel i b c) :
    Valid M (.imp (.not (.know i φ)) (.know i (.not (.know i φ)))) := by
  intro w hNot v hvw hK
  apply hNot
  intro u hwu
  exact hK u (heucl hvw hwu)

/-- The two-agent coin model: agent `0` sees the coin (identity
relation), agent `1` does not (total relation). `p` means the coin is
heads (`true`). -/
def muddy : Model Bool Unit (Fin 2) where
  rel := fun i w v => if i = 0 then w = v else True
  valuation := fun w _ => w = true
  nonempty_world := ⟨true⟩

/-- Agent `0` knows `p` exactly at heads-worlds: `0` sees the coin. -/
theorem sat_know_zero_atom (v : Bool) :
    Sat muddy (.know 0 (.atom ())) v ↔ v = true := by
  constructor
  · intro h
    exact h v (by simp [muddy])
  · intro hv u hu
    simp [muddy] at hu
    rw [← hu]
    exact hv

/-- Agent `0` knows `¬p` exactly at tails-worlds. -/
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

/-- Agent `1` does not know `p` at heads: `tails` is possible for `1`. -/
theorem muddy_not_know_one_p_true :
    ¬ Sat muddy (.know 1 (.atom ())) true := by
  intro h
  have hfalse := h false (by simp [muddy])
  exact Bool.false_ne_true hfalse

/-- Agent `1` knows that agent `0` knows whether `p`: from `1`'s
viewpoint, every world has `0` knowing `p` or knowing `¬p`. -/
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
