/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Canonical

@[expose] public section

/-! # Tests for canonical-model completeness of K, T, S4 and S5 -/

namespace Cslib.Modal.CanonicalTests

open Formula

inductive Atom where
  | p
  | q
  deriving DecidableEq

/-- Completeness at work: `□(p ∧ q) → □p` is a K-theorem because it is valid in every model. -/
example : Derivable Axioms.K (.imp (.box ((atom Atom.p).and (atom .q))) (.box (atom .p))) :=
  derivable_K_iff.mpr fun _ M w h next hnext ↦ by
    simpa using (KripkeModel.satisfies_and M next _ _).mp (h next hnext) |>.1

/-- `□p → ◇p` is a T-theorem (axiom D follows from T): it holds in every reflexive model. -/
example : Derivable Axioms.T (axiomD (atom Atom.p)) :=
  derivable_T_iff.mpr fun _ M hrefl w h ↦
    (KripkeModel.satisfies_dia M w _).mpr ⟨w, hrefl w, h w (hrefl w)⟩

/-- `◇□p → □p` is an S5-theorem: it holds whenever the relation is an equivalence. -/
example : Derivable Axioms.S5 (.imp (atom Atom.p).box.dia (atom .p).box) :=
  derivable_S5_iff.mpr fun _ M hequiv w h next hnext ↦ by
    obtain ⟨other, hother, hbox⟩ := (KripkeModel.satisfies_dia M w _).mp h
    exact hbox next (hequiv.trans (hequiv.symm hother) hnext)

/-- The preorder `false ≤ true` with `p` true only at `true`. -/
def chain : KripkeModel Bool Atom where
  nonempty_world := ⟨false⟩
  rel w w' := w ≤ w'
  valuation w _ := w = true

/-- The equivalence hypothesis of `derivable_S5_iff` cannot be weakened to a preorder: the
S5-theorem `◇□p → □p` fails at `false` in a reflexive transitive model. -/
example : Derivable Axioms.S5 (.imp (atom Atom.p).box.dia (atom .p).box) ∧
    ¬chain.Valid (.imp (atom Atom.p).box.dia (atom .p).box) := by
  refine ⟨derivable_S5_iff.mpr fun _ M hequiv w h next hnext ↦ ?_, fun hval ↦ ?_⟩
  · obtain ⟨other, hother, hbox⟩ := (KripkeModel.satisfies_dia M w _).mp h
    exact hbox next (hequiv.trans (hequiv.symm hother) hnext)
  · have hdia : chain.Satisfies false (atom Atom.p).box.dia :=
      (KripkeModel.satisfies_dia chain false _).mpr ⟨true, Bool.false_le _, fun w hw ↦ by
        simpa [chain] using le_antisymm (by simpa [chain] using hw) (Bool.le_true w)⟩
    exact absurd (hval false hdia false (le_refl false)) (by simp [chain])

/-- `◇◇p → ◇p` is an S4-theorem: it holds in every reflexive transitive model. -/
example : Derivable Axioms.S4 (.imp (atom Atom.p).dia.dia (atom .p).dia) :=
  derivable_S4_iff.mpr fun _ M _ htrans w h ↦ by
    obtain ⟨v, hwv, hv⟩ := (KripkeModel.satisfies_dia M w _).mp h
    obtain ⟨x, hvx, hx⟩ := (KripkeModel.satisfies_dia M v _).mp hv
    exact (KripkeModel.satisfies_dia M w _).mpr ⟨x, htrans hwv hvx, hx⟩

/-- Strong completeness with an infinite set of hypotheses `□ⁿp`. -/
example : Deduces Axioms.K (Set.range fun n : ℕ ↦ (Formula.box)^[n] (atom Atom.p))
    (atom Atom.p).box.box :=
  completeness_K fun _ _ _ _ hΓ ↦ hΓ _ ⟨2, rfl⟩

/-- Satisfiability form: the K-consistent set `{p}` is satisfiable. -/
example : ∃ (W : Type) (M : KripkeModel W Atom) (w : W),
    ∀ psi ∈ ({atom Atom.p} : Set (Formula Atom)), M.Satisfies w psi := by
  refine satisfiable_K fun hbot ↦ ?_
  have := hbot.satisfies (M := chain) (fun _ h ↦ absurd h (Set.notMem_empty _))
    (world := true) (by simp [chain])
  exact this

/-- Strong completeness: from the hypothesis `□p`, `p` is a T-consequence. -/
example : Deduces Axioms.T {(atom Atom.p).box} (atom .p) :=
  completeness_T fun _ _ _ hrefl hΓ ↦ hΓ _ rfl _ (hrefl _)

/-- Completeness for CSLib's own cube: CSLib's semantic validity of `φ → ◇φ` in every reflexive
model makes its translation a T-theorem. -/
example : Derivable Axioms.T (ofProposition
    (.or (.not (.atom Atom.p))
      (Logic.HasDynamicDiamond.dynDiamond default (.atom .p)))) :=
  derivable_ofProposition_T_iff.mpr fun _ ↦ Logic.Modal.Unimodal.T.t_valid

/-- Completeness for CSLib's K: non-contradiction, checked in CSLib's own semantics, has a
K-derivable translation. -/
example : Derivable Axioms.K (ofProposition
    (Logic.Modal.Proposition.not (.and (.atom Atom.p) (.not (.atom .p))))) :=
  derivable_ofProposition_K_iff.mpr fun _ _ _ _ h ↦ by
    obtain ⟨h₁, h₂⟩ := Logic.Modal.Satisfies.and_iff_and.mp h
    exact h₂ h₁

end Cslib.Modal.CanonicalTests
