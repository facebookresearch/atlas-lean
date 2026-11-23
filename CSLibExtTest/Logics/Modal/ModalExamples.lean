/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Kripke

/-!
# Modal logic: worked examples on a two-world model

Concrete usage of the Kripke semantics in `CSLibExt/Logics/Modal/Kripke.lean`.
The running example is the two-world frame `false → true`: the only
accessibility edge goes from `false` to `true`. The single atom `p` is true
exactly at `true`.

The frame is transitive but not reflexive, not serial, and not symmetric, so
it separates the standard axioms: `K` and `4` hold, `T` and `D` fail, and
`◇⊤` fails at the dead end `true`. These are the textbook calculations that
the axiom-validity theorems (`KripkeModel.valid_axiomK`, `valid_axiomFour`,
...) are about, made explicit on one model.
-/

@[expose] public section

namespace Cslib
namespace Modal
namespace Examples

/-- The two-world frame `false → true`, with `p` true only at `true`. -/
def twoWorld : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = false ∧ v = true
  valuation := fun w _ => w = true

/-- The frame is transitive: the only chain is `false → true`, and `true`
has no successors. -/
theorem twoWorld_transitive {a b c : Bool} :
    twoWorld.rel a b → twoWorld.rel b c → twoWorld.rel a c := by
  rintro ⟨rfl, rfl⟩ ⟨h, -⟩
  exact absurd h (by decide)

/-- The frame is not reflexive: `false` does not see itself. -/
theorem twoWorld_not_reflexive : ¬ twoWorld.rel false false := by
  intro h
  exact Bool.false_ne_true h.2

/-- `p` is false at `false` and true at `true`. -/
theorem twoWorld_atom_iff (w : Bool) :
    twoWorld.Satisfies w (.atom ()) ↔ w = true := Iff.rfl

/-- `□p` holds at `false`: its only successor `true` satisfies `p`. -/
theorem twoWorld_box_atom_false :
    twoWorld.Satisfies false (.box (.atom ())) := by
  intro v h
  obtain ⟨-, rfl⟩ := h
  rfl

/-- `◇p` holds at `false`, witnessed by the successor `true`. -/
theorem twoWorld_dia_atom_false :
    twoWorld.Satisfies false (.dia (.atom ())) := by
  rw [KripkeModel.satisfies_dia]
  exact ⟨true, ⟨rfl, rfl⟩, rfl⟩

/-- `◇p` fails at `true`: it has no successors. -/
theorem twoWorld_not_dia_atom_true :
    ¬ twoWorld.Satisfies true (.dia (.atom ())) := by
  rw [KripkeModel.satisfies_dia]
  rintro ⟨v, ⟨h, -⟩, -⟩
  exact absurd h (by decide)

/-- The K axiom holds on the two-world model (as on every model). -/
theorem twoWorld_valid_axiomK (φ ψ : Formula Unit) :
    twoWorld.Valid (Formula.axiomK φ ψ) :=
  KripkeModel.valid_axiomK twoWorld φ ψ

/-- The 4 axiom holds: the frame is transitive. -/
theorem twoWorld_valid_axiomFour (φ : Formula Unit) :
    twoWorld.Valid (Formula.axiomFour φ) := by
  apply KripkeModel.valid_axiomFour twoWorld _ φ
  intro a b c hab hbc
  exact twoWorld_transitive hab hbc

/-- The T axiom fails: `□p` holds at `false` but `p` does not. -/
theorem twoWorld_not_valid_axiomT :
    ¬ twoWorld.Valid (Formula.axiomT (.atom ())) := by
  intro h
  exact Bool.false_ne_true (h false twoWorld_box_atom_false)

/-- The D axiom fails: `□p` holds at the dead end `true`, but `◇p` does not. -/
theorem twoWorld_not_valid_axiomD :
    ¬ twoWorld.Valid (Formula.axiomD (.atom ())) := by
  intro h
  have hbox : twoWorld.Satisfies true (.box (.atom ())) := by
    intro v h
    exact absurd h.1 (by decide)
  exact twoWorld_not_dia_atom_true (h true hbox)

/-- `◇⊤` is not valid: it fails at the dead-end world `true`. -/
theorem twoWorld_not_valid_dia_top :
    ¬ twoWorld.Valid (Formula.dia Formula.top) := by
  intro h
  have hdia := h true
  rw [KripkeModel.satisfies_dia] at hdia
  obtain ⟨v, ⟨hv, -⟩, -⟩ := hdia
  exact absurd hv (by decide)

end Examples
end Modal
end Cslib
