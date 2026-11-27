/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ContextualEquivalence
public import CSLibExt.Languages.OperationalSemantics

/-!
# Contextual equivalence toy tests

Toy instance for generic contextual equivalence: a single judgment with natural-number terms,
hole-only contexts, countdown anchor semantics, and outcomes equated with final
configurations. States the reflexivity, approximation, and distinct-equivalence examples for
the toy instance.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalenceTests

open Cslib.Languages.ContextualEquivalence
open Cslib.Languages.OperationalSemantics

/-- Toy context algebra: natural-number terms with hole-only contexts. -/
def toyAlgebra : CtxAlgebra Unit where
  Tm := fun _ => Nat
  Ctx := fun _ _ => Unit
  plug := fun {_ _} _ t => t
  hole := fun {_} => ()
  comp := fun {_ _ _} _ _ => ()
  plug_hole := fun {_} t => Eq.refl t
  plug_comp := fun {_ _ _} _ _ t => Eq.refl t

/-- Toy anchor semantics: countdown steps with zero final. -/
def toySem : OpSem Nat Unit where
  lts := ⟨fun n _ m => n = m + 1⟩
  Final := fun n => n = 0
  final_terminal := by
    intro c hc μ s' h
    change c = s' + 1 at h
    change c = 0 at hc
    grind

/-- Toy observations over the toy algebra. -/
def toyObs : CtxObs toyAlgebra where
  Prog := fun _ => True
  Outcome := Nat
  Label := fun _ => Unit
  sem := fun {_} _ => toySem
  outcome := fun {_} q o => q = o

/-- Toy reflexivity example: zero is equivalent to itself. -/
theorem toy_equiv_refl_example : CtxEquiv toyObs (j := ()) (0 : Nat) (0 : Nat) := by
  exact ctxEquiv_refl toyObs _

/-- Toy approximation example between distinct numerals. -/
theorem toy_approx_example : CtxApprox toyObs (j := ()) (3 : Nat) (5 : Nat) := by
  have hCount : ∀ n : Nat, toySem.Steps n 0 := by
    intro n
    induction n with
    | zero => exact ⟨[], Cslib.LTS.MTr.refl⟩
    | succ n ih =>
      obtain ⟨μs, hm⟩ := ih
      have htr : toySem.lts.Tr (n + 1) () n := rfl
      exact ⟨() :: μs, Cslib.LTS.MTr.stepL htr hm⟩
  intro _ hk C o hy
  obtain ⟨q, _, hFinal, hOut⟩ := hy
  have hFin : q = (0 : Nat) := hFinal
  have hEq : q = o := hOut
  have ho : o = (0 : Nat) := Eq.trans (Eq.symm hEq) hFin
  subst ho
  exact ⟨(0 : Nat), hCount 5, rfl, rfl⟩

/-- Toy equivalence between distinct numerals (all toy terms coincide). -/
theorem toy_distinct_equiv_example : CtxEquiv toyObs (j := ()) (2 : Nat) (7 : Nat) := by
  have hCount : ∀ n : Nat, toySem.Steps n 0 := by
    intro n
    induction n with
    | zero => exact ⟨[], Cslib.LTS.MTr.refl⟩
    | succ n ih =>
      obtain ⟨μs, hm⟩ := ih
      have htr : toySem.lts.Tr (n + 1) () n := rfl
      exact ⟨() :: μs, Cslib.LTS.MTr.stepL htr hm⟩
  have hY : ∀ (k : Unit) (hk : toyObs.Prog k) (p o : Nat),
      Yields toyObs hk p o ↔ o = 0 := by
    intro k hk p o
    constructor
    · rintro ⟨q, _, hFinal, hOut⟩
      have hFin : q = (0 : Nat) := hFinal
      have hEq : q = o := hOut
      exact Eq.trans (Eq.symm hEq) hFin
    · intro ho
      subst ho
      exact ⟨(0 : Nat), hCount p, rfl, rfl⟩
  intro _ hk C o
  have hL := hY _ hk (toyAlgebra.plug C (2 : Nat)) o
  have hR := hY _ hk (toyAlgebra.plug C (7 : Nat)) o
  exact hL.trans hR.symm

end Cslib.Languages.ContextualEquivalenceTests
