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

public import CSLibExt.Security.Noninterference.Basic

/-!
# Security judgments and confinement

The program counter prevents writes to low variables under secret control. Expression
judgments bound every variable read. Branches and loops join the guard level into the pc.
-/

@[expose] public section

namespace Cslib.Security.Noninterference

/-- An expression reads only variables at or below its assigned level. -/
inductive AExpSecure (Γ : Policy) : IMP.AExp → Level → Prop where
  | const (n l) : AExpSecure Γ (.const n) l
  | var {x l} : Γ x ≤ l → AExpSecure Γ (.var x) l
  | add {a b l} : AExpSecure Γ a l → AExpSecure Γ b l → AExpSecure Γ (.add a b) l
  | sub {a b l} : AExpSecure Γ a l → AExpSecure Γ b l → AExpSecure Γ (.sub a b) l
  | mul {a b l} : AExpSecure Γ a l → AExpSecure Γ b l → AExpSecure Γ (.mul a b) l

/-- Low expressions cannot distinguish low-equivalent stores. -/
theorem AExpSecure.eval_eq {Γ : Policy} {e : IMP.AExp} {s t : Store}
    (he : AExpSecure Γ e false) (hst : LowEquiv Γ s t) : e.eval s = e.eval t := by
  generalize hl : false = l at he
  induction he with
  | const => rfl
  | var hx => exact hst _ (le_antisymm (hl ▸ hx) bot_le)
  | add ha hb iha ihb => exact congrArg₂ (· + ·) (iha hl) (ihb hl)
  | sub ha hb iha ihb => exact congrArg₂ (· - ·) (iha hl) (ihb hl)
  | mul ha hb iha ihb => exact congrArg₂ (· * ·) (iha hl) (ihb hl)

/-- A Boolean expression reads only variables at or below its assigned level. -/
inductive BExpSecure (Γ : Policy) : IMP.BExp → Level → Prop where
  | truth (b l) : BExpSecure Γ (.truth b) l
  | eq {a b l} : AExpSecure Γ a l → AExpSecure Γ b l → BExpSecure Γ (.eq a b) l
  | le {a b l} : AExpSecure Γ a l → AExpSecure Γ b l → BExpSecure Γ (.le a b) l
  | not {b l} : BExpSecure Γ b l → BExpSecure Γ (.not b) l
  | and {a b l} : BExpSecure Γ a l → BExpSecure Γ b l → BExpSecure Γ (.and a b) l

/-- Low Boolean expressions cannot distinguish low-equivalent stores. -/
theorem BExpSecure.eval_eq {Γ : Policy} {e : IMP.BExp} {s t : Store}
    (he : BExpSecure Γ e false) (hst : LowEquiv Γ s t) : e.eval s = e.eval t := by
  generalize hl : false = l at he
  induction he with
  | truth => rfl
  | eq ha hb =>
      have haeq := (hl ▸ ha).eval_eq hst
      have hbeq := (hl ▸ hb).eval_eq hst
      simp only [IMP.BExp.eval, haeq, hbeq]
  | le ha hb =>
      have haeq := (hl ▸ ha).eval_eq hst
      have hbeq := (hl ▸ hb).eval_eq hst
      simp only [IMP.BExp.eval, haeq, hbeq]
  | not h ih => simp only [IMP.BExp.eval, ih hl]
  | and ha hb iha ihb => simp only [IMP.BExp.eval, iha hl, ihb hl]

/-- A syntax-directed security judgment with an explicit program-counter level. -/
inductive CmdSecure (Γ : Policy) : Level → IMP.Cmd → Prop where
  | skip (pc) : CmdSecure Γ pc .skip
  | assign {pc x e} : pc ≤ Γ x → AExpSecure Γ e (Γ x) → CmdSecure Γ pc (.assign x e)
  | seq {pc a b} : CmdSecure Γ pc a → CmdSecure Γ pc b → CmdSecure Γ pc (.seq a b)
  | ite {pc l e a b} : BExpSecure Γ e l → CmdSecure Γ (pc ⊔ l) a →
      CmdSecure Γ (pc ⊔ l) b → CmdSecure Γ pc (.ite e a b)
  | loop {pc l e a} : BExpSecure Γ e l → CmdSecure Γ (pc ⊔ l) a →
      CmdSecure Γ pc (.while e a)

/-- A high assignment preserves every low observation. -/
theorem LowEquiv.update_high {Γ : Policy} {s : Store} {x n : Nat}
    (hx : Γ x = true) : LowEquiv Γ s (Function.update s x n) := by
  intro y hy
  have hne : y ≠ x := by intro h; subst y; simp [hx] at hy
  simp [Function.update_of_ne hne]

/-- Matched assignments preserve low equivalence; high writes may use different values. -/
theorem LowEquiv.update {Γ : Policy} {s t : Store} {x m n : Nat}
    (hst : LowEquiv Γ s t) (hv : Γ x = false → m = n) :
    LowEquiv Γ (Function.update s x m) (Function.update t x n) := by
  intro y hy
  by_cases h : y = x
  · subst y
    simpa using hv hy
  · simpa [Function.update_of_ne h] using hst y hy

/-- A well-typed command under a high pc cannot change a low variable. -/
theorem BigStepConfinement {Γ : Policy} {c : IMP.Cmd} {s t : Store}
    (h : IMP.BigStep c s t) (hc : CmdSecure Γ true c) : LowEquiv Γ s t := by
  induction h with
  | skip => exact .refl _ _
  | assign =>
    cases hc with
    | assign hpc _ => exact LowEquiv.update_high (le_antisymm le_top hpc)
  | seq ha hb iha ihb =>
    cases hc with
    | seq hca hcb => exact (iha hca).trans (ihb hcb)
  | iteTrue he ha ih =>
    cases hc with
    | ite _ hca _ => exact ih (by simpa using hca)
  | iteFalse he hb ih =>
    cases hc with
    | ite _ _ hcb => exact ih (by simpa using hcb)
  | whileFalse => exact .refl _ _
  | whileTrue he ha hl iha ihl =>
    cases hc with
    | loop hce hca =>
      exact (iha (by simpa using hca)).trans (ihl (.loop hce hca))

end Cslib.Security.Noninterference
