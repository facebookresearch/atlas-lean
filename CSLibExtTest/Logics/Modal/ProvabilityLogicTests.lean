/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.FixedPoint
public import CSLibExt.Logics.Modal.ProvabilityLogic.ArithmeticalSoundness

@[expose] public section

/-! # Tests for the provability logic GL -/

namespace Cslib.Modal.ProvabilityLogicTests

open Formula

inductive Atom where
  | p
  | q
  | r
  deriving DecidableEq

/-- Axiom 4 for an atom is a GL theorem. -/
example : Derivable Axioms.GL (axiomFour (.atom Atom.p)) :=
  Derivable.axiomFour_GL _

/-- Löb's axiom is a GL theorem, and so is its necessitation. -/
example : Derivable Axioms.GL (.box (axiomLob (.atom Atom.p))) :=
  .nec (.extra (Axioms.axiomLob_mem_GL _))

/-- The modal second incompleteness theorem and the Gödel sentence. -/
example : Derivable Axioms.GL
    (.imp (Formula.box (.bot : Formula Atom)).neg
      (Formula.box (Formula.box (.bot : Formula Atom)).neg).neg) :=
  Derivable.godel_second_GL

/-- The hypotheses of GL soundness are satisfiable by a model with a nonempty relation: the
three-element chain `0 < 1 < 2` on `Fin 3`. -/
def chain : KripkeModel (Fin 3) Atom where
  nonempty_world := ⟨0⟩
  rel a b := a < b
  valuation _ _ := True

example : chain.rel 0 1 ∧ chain.rel 1 2 ∧ chain.rel 0 2 := by
  simp only [chain]
  decide

/-- On the chain, every GL theorem is valid; here axiom 4 and Löb's axiom. -/
example : chain.Valid (axiomLob (.atom Atom.p)) :=
  Derivable.valid_GL_of_finite (fun h₁ h₂ ↦ lt_trans h₁ h₂) (fun w ↦ lt_irrefl w)
    (.extra (Axioms.axiomLob_mem_GL _))

/-- The same through the conversely well-founded form of soundness. -/
example : chain.Valid (axiomFour (.atom Atom.q)) :=
  Derivable.valid_GL (fun h₁ h₂ ↦ lt_trans h₁ h₂) (wellFounded_gt (α := Fin 3))
    (Derivable.axiomFour_GL _)

/-- Reflection `□⊥ → ⊥` fails at the last world of the chain, so GL proves no reflection. -/
example : ¬chain.Satisfies 2 (axiomT .bot) := by
  intro h
  apply h
  intro v hv
  exact absurd (show (2 : Fin 3) < v from hv) (Fin.not_lt.mpr (Fin.le_last v))

/-- K4 proves axiom 4, and GL contains K4. -/
example : Derivable Axioms.GL (axiomFour (axiomFour (.atom Atom.p))) :=
  Derivable.GL_of_K4 (.extra (Axioms.axiomFour_mem_K4 _))

/-- `p` is modalised in `¬□p` and in `□(p → q)`, but not in `p → □p`. -/
example : (Formula.box (.atom Atom.p)).neg.Modalised Atom.p := by
  simp [Formula.neg, Formula.Modalised]

example : (Formula.box (.imp (.atom Atom.p) (.atom Atom.q))).Modalised Atom.p := by
  simp [Formula.Modalised]

example : ¬(Formula.imp (.atom Atom.p) (.box (.atom Atom.p))).Modalised Atom.p := by
  simp [Formula.Modalised]

/-- The fixed point of `¬□p`, from the one-box theorem with `B = ¬r` and `C = p`, is `¬□¬⊤`. -/
example : Derivable Axioms.GL
    ((Formula.box (Formula.top : Formula Atom).neg).neg.iff
      ((Formula.box (.atom Atom.p)).neg.subst Atom.p
        (Formula.box (Formula.top : Formula Atom).neg).neg)) :=
  Derivable.fixedPoint_GL_of_box (B := (Formula.atom Atom.r).neg) (C := .atom Atom.p)
    (p := Atom.p) (r := Atom.r) (by simp [Formula.neg, Formula.atoms])

/-- The fixed point of `□(p → q)` is `□(⊤ → q)` (equivalent to `□q`), from the one-box theorem
with `B = r` and `C = p → q`: GL proves `□(⊤ → q) ↔ □(□(⊤ → q) → q)`. -/
example : Derivable Axioms.GL
    ((Formula.box (.imp .top (.atom Atom.q))).iff
      (.box (.imp (.box (.imp .top (.atom Atom.q))) (.atom Atom.q)))) :=
  Derivable.fixedPoint_GL_of_box (B := .atom Atom.r) (C := .imp (.atom Atom.p) (.atom Atom.q))
    (p := Atom.p) (r := Atom.r) (by simp [Formula.atoms])

/-- Uniqueness of the fixed point of `¬□p`. -/
example (psi chi : Formula Atom) : Derivable Axioms.GL
    (.imp (psi.iff ((Formula.box (.atom Atom.p)).neg.subst Atom.p psi))
      (.imp (.box (psi.iff ((Formula.box (.atom Atom.p)).neg.subst Atom.p psi)))
        (.imp (chi.iff ((Formula.box (.atom Atom.p)).neg.subst Atom.p chi))
          (.imp (.box (chi.iff ((Formula.box (.atom Atom.p)).neg.subst Atom.p chi)))
            (psi.iff chi))))) :=
  Derivable.fixedPoint_unique_GL (by simp [Formula.neg, Formula.Modalised]) psi chi

/-- The Hilbert–Bernays–Löb hypotheses are jointly satisfiable, with the diagonal property: true
propositions as theorems, and a provability operator that holds of everything (a theory that
proves its own inconsistency, such as `PA + ¬Con(PA)`). Falsity is not a theorem. -/
def trivialHBL : HilbertBernaysLobStructure Prop where
  imp a b := a → b
  falsum := False
  prov _ := True
  Thm a := a
  mp h ha := h ha
  ax1 _ _ := fun ha _ ↦ ha
  ax2 _ _ _ := fun h₁ h₂ ha ↦ h₁ ha (h₂ ha)
  dne _ := fun h ↦ Classical.byContradiction h
  d1 _ := trivial
  d2 _ _ := fun _ _ ↦ trivial
  d3 _ := fun _ ↦ trivial

theorem trivialHBL_diag (a : Prop) : ∃ b, trivialHBL.Thm (trivialHBL.imp b
    (trivialHBL.imp (trivialHBL.prov b) a)) ∧
    trivialHBL.Thm (trivialHBL.imp (trivialHBL.imp (trivialHBL.prov b) a) b) :=
  ⟨a, fun ha _ ↦ ha, fun h ↦ h trivial⟩

example : ¬trivialHBL.Thm trivialHBL.falsum := id

/-- Löb's theorem in the trivial structure. -/
example (a : Prop) (h : trivialHBL.Thm (trivialHBL.imp (trivialHBL.prov a) a)) :
    trivialHBL.Thm a :=
  trivialHBL.lob_theorem trivialHBL_diag h

/-- Arithmetical soundness: realizations of GL theorems are theorems. -/
example (f : Atom → Prop) :
    trivialHBL.Thm (trivialHBL.realize f (axiomFour (.atom Atom.p))) :=
  trivialHBL.thm_realize_GL trivialHBL_diag f (Derivable.axiomFour_GL _)

end Cslib.Modal.ProvabilityLogicTests
