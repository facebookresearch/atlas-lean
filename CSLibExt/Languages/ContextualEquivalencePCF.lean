/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ContextualEquivalence
public import CSLibExt.Languages.LambdaCalculus.PCF.ContextualEquivalence
public import CSLibExt.Languages.LambdaCalculus.PCF.SmallStep
public import CSLibExt.Languages.OperationalSemantics

/-!
# PCF instance of contextual equivalence

The PCF instance of generic contextual equivalence with bridges to the existing PCF relations.
Contexts and plugging come from the PCF one-hole contexts; programs are closed ground terms
observed through the anchor operational semantics with numerals as outcomes. No STLC
work appears here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalence.PCF

open Cslib.Languages.OperationalSemantics
open Cslib.Languages.LambdaCalculus.PCF

/-- Anchor adapter on closed ground PCF terms with unit labels. -/
def pcfSem : OpSem (Tm [] Ty.nat) Unit where
  lts := { Tr := fun x _ y => Tm.Step x y }
  Final := Tm.Value
  final_terminal := by
    intro c hv μ s' h
    exact Tm.Value.not_step hv h

/-- Context algebra from PCF terms and one-hole contexts. -/
def pcfAlgebra : CtxAlgebra (List Ty × Ty) where
  Tm := fun j => Tm j.1 j.2
  Ctx := fun j k => Ctx j.1 j.2 k.1 k.2
  plug := fun C t => Ctx.plug C t
  hole := Ctx.hole
  comp := fun D C => Ctx.comp D C
  plug_hole := fun t => Ctx.plug_hole t
  plug_comp := fun D C t => Ctx.plug_comp D C t

/-- Observations for PCF: closed ground programs with numeral outcomes. -/
def pcfObs : CtxObs pcfAlgebra where
  Prog := fun j => j = ([], Ty.nat)
  Outcome := Nat
  Label := fun _ => Unit
  sem := fun {k} hk => by cases hk; exact pcfSem
  outcome := fun {k} q o =>
    match k, q with
    | ([], .base ()), q => q = Tm.numeral o
    | _, _ => False

/-- Generic yields coincides with PCF evaluation to a numeral. -/
theorem yields_iff_eval {p : Tm [] Ty.nat} {n : Nat} :
    Yields pcfObs rfl p n ↔ Tm.Eval p (Tm.numeral n) := by
  have _hStep : ∀ {x y : Tm [] Ty.nat}, pcfSem.Step x y ↔ Tm.Step x y := by
    intro x y
    constructor
    · rintro ⟨_, _h⟩
      exact _h
    · intro _h
      exact ⟨(), _h⟩
  have _hSteps : ∀ {x y : Tm [] Ty.nat}, pcfSem.Steps x y ↔ Tm.Steps x y := by
    intro x y; rw [OpSem.steps_iff_reflTransGen pcfSem]
    constructor
    · intro _h; induction _h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ _s _i => exact Relation.ReflTransGen.tail _i (_hStep.mp _s)
    · intro _h; induction _h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ _s _i => exact Relation.ReflTransGen.tail _i (_hStep.mpr _s)
  change (∃ q, pcfSem.Steps p q ∧ Tm.Value q ∧ q = Tm.numeral n) ↔ Tm.Eval p (Tm.numeral n)
  constructor
  · rintro ⟨q, _hsteps, _hval, _heq⟩
    subst _heq
    exact Tm.eval_iff_steps.mpr ⟨_hSteps.mp _hsteps, _hval⟩
  · intro _h
    obtain ⟨_hsteps, _hval⟩ := Tm.eval_iff_steps.mp _h
    exact ⟨Tm.numeral n, _hSteps.mpr _hsteps, _hval, rfl⟩

/-- Generic approximation coincides with PCF approximation. -/
theorem pcf_ctxApprox_iff {Γ : List Ty} {A : Ty} {t u : Tm Γ A} :
    CtxApprox pcfObs (j := (Γ, A)) t u ↔ Tm.CtxApprox t u := by
  constructor
  · intro _h C n _heval
    exact yields_iff_eval.mp (_h rfl C n (yields_iff_eval.mpr _heval))
  · intro _h k hk C o _hy
    obtain rfl : k = ([], Ty.nat) := hk
    exact yields_iff_eval.mpr (_h C o (yields_iff_eval.mp _hy))

/-- Generic equivalence coincides with PCF equivalence. -/
theorem pcf_ctxEquiv_iff {Γ : List Ty} {A : Ty} {t u : Tm Γ A} :
    CtxEquiv pcfObs (j := (Γ, A)) t u ↔ Tm.CtxEquiv t u := by
  constructor
  · intro _h C n
    exact yields_iff_eval.symm.trans ((_h rfl C n).trans yields_iff_eval)
  · intro _h k hk C o
    obtain rfl : k = ([], Ty.nat) := hk
    exact yields_iff_eval.trans ((_h C o).trans yields_iff_eval.symm)

end Cslib.Languages.ContextualEquivalence.PCF
