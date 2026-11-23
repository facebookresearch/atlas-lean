/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Security.Noninterference.Typing

/-!
# Termination-insensitive noninterference

Unwinding combines agreement on public expressions with confinement under secret
control. The theorem compares final stores only when both runs terminate; it makes
no assertion that termination or the number of execution steps is public.
-/

@[expose] public section

namespace Cslib.Security.Noninterference

/-- Two confined runs preserve agreement even if their control paths differ. -/
theorem LowEquiv.of_confined {Γ : Policy} {s t s' t' : Store}
    (hst : LowEquiv Γ s t) (hs : LowEquiv Γ s s') (ht : LowEquiv Γ t t') :
    LowEquiv Γ s' t' := hs.symm.trans (hst.trans ht)

/-- Unwinding for two terminating executions of a secure command, at any pc. -/
theorem BigStepUnwinding {Γ : Policy} {c : IMP.Cmd} {s s' t t' : Store}
    {pc : Level} (hs : IMP.BigStep c s s') (hc : CmdSecure Γ pc c)
    (ht : IMP.BigStep c t t') (hst : LowEquiv Γ s t) : LowEquiv Γ s' t' := by
  induction hs generalizing pc t t' with
  | skip => cases ht; exact hst
  | assign =>
    cases ht
    cases hc with
    | assign _ he =>
      exact hst.update (fun hx => (by
        exact (hx ▸ he).eval_eq hst))
  | seq ha hb iha ihb =>
    cases hc with
    | seq hca hcb =>
      cases ht with
      | seq hta htb => exact ihb hcb htb (iha hca hta hst)
  | iteTrue he ha ih =>
    cases hc with
    | @ite _ l _ _ _ hce hca hcb =>
      cases l with
      | false =>
        have heq := hce.eval_eq hst
        cases ht with
        | iteTrue _ hta => exact ih hca hta hst
        | iteFalse ht0 _ =>
          exact Bool.noConfusion (he.symm.trans (heq.trans ht0))
      | true =>
        have hsconf := BigStepConfinement ha (by simpa using hca)
        cases ht with
        | iteTrue _ hta =>
          exact hst.of_confined hsconf (BigStepConfinement hta (by simpa using hca))
        | iteFalse _ htb =>
          exact hst.of_confined hsconf (BigStepConfinement htb (by simpa using hcb))
  | iteFalse he hb ih =>
    cases hc with
    | @ite _ l _ _ _ hce hca hcb =>
      cases l with
      | false =>
        have heq := hce.eval_eq hst
        cases ht with
        | iteTrue ht0 _ =>
          exact Bool.noConfusion (he.symm.trans (heq.trans ht0))
        | iteFalse _ htb => exact ih hcb htb hst
      | true =>
        have hsconf := BigStepConfinement hb (by simpa using hcb)
        cases ht with
        | iteTrue _ hta =>
          exact hst.of_confined hsconf (BigStepConfinement hta (by simpa using hca))
        | iteFalse _ htb =>
          exact hst.of_confined hsconf (BigStepConfinement htb (by simpa using hcb))
  | whileFalse he =>
    cases hc with
    | @loop _ l _ _ hce hca =>
      cases l with
      | false =>
        have heq := hce.eval_eq hst
        cases ht with
        | whileFalse => exact hst
        | whileTrue ht0 _ _ =>
          exact Bool.noConfusion (he.symm.trans (heq.trans ht0))
      | true =>
        exact hst.trans (BigStepConfinement ht (.loop hce (by simpa using hca)))
  | whileTrue he ha hl iha ihl =>
    cases hc with
    | @loop _ l _ _ hce hca =>
      cases l with
      | false =>
        have heq := hce.eval_eq hst
        cases ht with
        | whileFalse ht0 =>
          exact Bool.noConfusion (he.symm.trans (heq.trans ht0))
        | whileTrue _ hta htl =>
          exact ihl (.loop hce hca) htl (iha hca hta hst)
      | true =>
        have hloop : CmdSecure Γ true (IMP.Cmd.while _ _) :=
          .loop hce (by simpa using hca)
        exact hst.of_confined
          (BigStepConfinement (IMP.BigStep.whileTrue he ha hl) hloop)
          (BigStepConfinement ht hloop)

/-- Secure programs preserve low observations whenever both executions terminate. -/
theorem termination_insensitive_noninterference {Γ : Policy} {c : IMP.Cmd}
    {s s' t t' : Store} (hc : CmdSecure Γ false c) (hst : LowEquiv Γ s t)
    (hs : IMP.BigStep c s s') (ht : IMP.BigStep c t t') : LowEquiv Γ s' t' :=
  BigStepUnwinding hs hc ht hst

end Cslib.Security.Noninterference
