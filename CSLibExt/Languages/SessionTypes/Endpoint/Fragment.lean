/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Finite linear π fragment and structural closure

The finite ownership fragment permits restrictions and arbitrary parallel
composition, but no choice or linear replication. This is a syntactic
restriction, not a reduction or progress witness.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Existing π terms without choice or replication, including their bodies. -/
def FiniteLinear : Proc → Prop
  | .nil => True
  | .out _ _ p | .inp _ p | .nu p => FiniteLinear p
  | .par p q => FiniteLinear p ∧ FiniteLinear q
  | .repl _ | .sum _ _ => False

/-- Lifting cannot add or remove unsupported process constructors. -/
theorem finiteLinear_lift (k : Nat) (p : Proc) :
    FiniteLinear (liftProc k p) ↔ FiniteLinear p := by
  induction p generalizing k <;> simp_all [liftProc, FiniteLinear]

/-- Swapping restrictions cannot add or remove choice or replication. -/
theorem finiteLinear_swap (k : Nat) (p : Proc) :
    FiniteLinear (swapProc k p) ↔ FiniteLinear p := by
  induction p generalizing k <;> simp_all [swapProc, FiniteLinear]

/-- All existing structural congruences preserve the finite linear
fragment. In particular, folding replication cannot introduce it. -/
theorem finiteLinear_cong {p q : Proc} (h : Cong p q) :
    FiniteLinear p ↔ FiniteLinear q := by
  induction h <;> simp_all [FiniteLinear, finiteLinear_lift,
    finiteLinear_swap, and_assoc, and_comm]

/-- Substitution changes names, not the finite fragment's process shape. -/
theorem finiteLinear_subst (b : Name) (k : Nat) (p : Proc) :
    FiniteLinear (substProc b k p) ↔ FiniteLinear p := by
  induction p generalizing b k <;> simp_all [substProc, FiniteLinear]

/-- Selection cannot discard a branch of a term in the choice-free fragment. -/
theorem finiteLinear_select_eq {p q : Proc} (h : Select p q)
    (hp : FiniteLinear p) : p = q := by
  induction h with
  | refl => rfl
  | left => cases hp
  | right => cases hp
  | trans h₁ h₂ ih₁ ih₂ =>
    have he := ih₁ hp
    exact he.trans (ih₂ (he ▸ hp))

/-- All existing π reduction constructors preserve the finite fragment,
including arbitrary pre/post structural congruence and selection. -/
theorem finiteLinear_step {p q : Proc} (h : Step p q)
    (hp : FiniteLinear p) : FiniteLinear q := by
  induction h with
  | commSelect hs ht =>
    have he := finiteLinear_select_eq hs hp.1
    have hf := finiteLinear_select_eq ht hp.2
    rw [he, hf] at hp
    exact ⟨hp.1, (finiteLinear_subst _ _ _).mpr hp.2⟩
  | parL h ih => exact ⟨ih hp.1, hp.2⟩
  | parR h ih => exact ⟨hp.1, ih hp.2⟩
  | nu h ih => exact ih hp
  | cong hc h hd ih =>
    exact (finiteLinear_cong hd).mp (ih ((finiteLinear_cong hc).mp hp))

end Cslib.SessionTypes.Endpoint
