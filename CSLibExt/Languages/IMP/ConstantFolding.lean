/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Canonical constant folding for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep
public import CSLibExt.Languages.IMP.StackMachineReflection

/-!
# Canonical constant folding for IMP

Conservative constant folding and propagation over canonical
`Cslib.IMP` syntax. Folding preserves `BigStep` executions
whenever the constant table approximates the initial state.

Counted in table operations with unit-cost arithmetic, each `ite` join
materializes its assigned variables by querying both branch tables, giving
quadratic structural work per join level in the worst case for deeply nested
distinct-variable branches. A finite-map representation would remove that
factor and is future work. No bound is claimed on total time or output size,
since folded `Nat` literals can be exponentially large.
-/

@[expose] public section

namespace Cslib.IMP

/-- Known constant values for variables, by identifier. -/
abbrev ConstTable := Nat → Option Nat

/-- A table approximates a state when entries agree with it. -/
def ConstApprox (t : ConstTable) (s : State) : Prop :=
  ∀ x n, t x = some n → s x = n

/-- The table that knows no constants. -/
def emptyTable : ConstTable := fun _ => none

/-- The empty table approximates every state. -/
theorem emptyTable_approx (s : State) :
    ConstApprox emptyTable s := by
  intro x n h
  simp [emptyTable] at h

/-- Constant value of an arithmetic expression, when it is a literal. -/
private def litVal : AExp → Option Nat
  | .const n => some n
  | _ => none

private theorem litVal_eq_some {e : AExp} {n : Nat}
    (h : litVal e = some n) : e = .const n := by
  cases e <;> simp_all [litVal]

private theorem zero_sub_nat (n : Nat) : 0 - n = 0 := by
  omega

/-- Fold arithmetic expressions using known constants. -/
def afold : ConstTable → AExp → AExp
  | _, .const v => .const v
  | t, .var x =>
      match t x with
      | some n => .const n
      | none => .var x
  | t, .add l r =>
      match afold t l, afold t r with
      | .const m, .const n => .const (m + n)
      | l', r' => .add l' r'
  | t, .sub l r =>
      match afold t l, afold t r with
      | .const m, .const n => .const (m - n)
      | .const m, r' =>
          if m = 0 then .const 0 else .sub (.const m) r'
      | l', r' => .sub l' r'
  | t, .mul l r =>
      match afold t l, afold t r with
      | .const m, .const n => .const (m * n)
      | l', r' => .mul l' r'

/-- Folded arithmetic evaluates like the original expression when the table agrees with the
state. -/
theorem afold_eval (t : ConstTable) (a : AExp) (s : State)
    (h : ConstApprox t s) :
    (afold t a).eval s = a.eval s := by
  induction a with
  | const _v => rfl
  | var x =>
      have hxx : ∀ n, t x = some n →
          (afold t (.var x)).eval s = s x := by
        intro n hn
        have hsn : s x = n := h x n hn
        simp [afold, hn, hsn]
      cases htx : t x with
      | none => simp [afold, htx]
      | some n => exact hxx n htx
  | add l r ihl ihr =>
      cases hl : afold t l with
      | const _m =>
          cases hr : afold t r with
          | const _n => simp_all [afold]
          | var _x => simp_all [afold]
          | add _a _b => simp_all [afold]
          | sub _a _b => simp_all [afold]
          | mul _a _b => simp_all [afold]
      | var _x => cases hr : afold t r <;> simp_all [afold]
      | add _a _b => cases hr : afold t r <;> simp_all [afold]
      | sub _a _b => cases hr : afold t r <;> simp_all [afold]
      | mul _a _b => cases hr : afold t r <;> simp_all [afold]
  | sub l r ihl ihr =>
      cases hl : afold t l with
      | const m =>
          cases hr : afold t r with
          | const _n => simp_all [afold]
          | var _x =>
              cases Decidable.em (m = 0) with
              | inl hm =>
                  subst hm
                  have hl0 : l.eval s = 0 := by
                    have hh := ihl
                    rw [hl] at hh
                    simp only [AExp.eval_const] at hh
                    exact hh.symm
                  simp [afold, hl, hr, hl0]
              | inr _hm => simp_all [afold]
          | add _a _b =>
              cases Decidable.em (m = 0) with
              | inl hm =>
                  subst hm
                  have hl0 : l.eval s = 0 := by
                    have hh := ihl
                    rw [hl] at hh
                    simp only [AExp.eval_const] at hh
                    exact hh.symm
                  simp [afold, hl, hr, hl0]
              | inr _hm => simp_all [afold]
          | sub _a _b =>
              cases Decidable.em (m = 0) with
              | inl hm =>
                  subst hm
                  have hl0 : l.eval s = 0 := by
                    have hh := ihl
                    rw [hl] at hh
                    simp only [AExp.eval_const] at hh
                    exact hh.symm
                  simp [afold, hl, hr, hl0]
              | inr _hm => simp_all [afold]
          | mul _a _b =>
              cases Decidable.em (m = 0) with
              | inl hm =>
                  subst hm
                  have hl0 : l.eval s = 0 := by
                    have hh := ihl
                    rw [hl] at hh
                    simp only [AExp.eval_const] at hh
                    exact hh.symm
                  simp [afold, hl, hr, hl0]
              | inr _hm => simp_all [afold]
      | var _x => cases hr : afold t r <;> simp_all [afold]
      | add _a _b => cases hr : afold t r <;> simp_all [afold]
      | sub _a _b => cases hr : afold t r <;> simp_all [afold]
      | mul _a _b => cases hr : afold t r <;> simp_all [afold]
  | mul l r ihl ihr =>
      cases hl : afold t l with
      | const _m =>
          cases hr : afold t r with
          | const _n => simp_all [afold]
          | var _x => simp_all [afold]
          | add _a _b => simp_all [afold]
          | sub _a _b => simp_all [afold]
          | mul _a _b => simp_all [afold]
      | var _x => cases hr : afold t r <;> simp_all [afold]
      | add _a _b => cases hr : afold t r <;> simp_all [afold]
      | sub _a _b => cases hr : afold t r <;> simp_all [afold]
      | mul _a _b => cases hr : afold t r <;> simp_all [afold]

/-- Fold boolean expressions using known constants. -/
def bfold : ConstTable → BExp → BExp
  | _, .truth v => .truth v
  | t, .eq l r =>
      match afold t l, afold t r with
      | .const m, .const n => .truth (decide (m = n))
      | l', r' => .eq l' r'
  | t, .le l r =>
      match afold t l, afold t r with
      | .const m, .const n => .truth (decide (m ≤ n))
      | l', r' => .le l' r'
  | t, .not b =>
      match bfold t b with
      | .truth v => .truth (!v)
      | b' => .not b'
  | t, .and l r =>
      match bfold t l, bfold t r with
      | .truth a, .truth b => .truth (a && b)
      | l', r' => .and l' r'

/-- Folded booleans evaluate like the original expression when the table agrees with the
state. -/
theorem bfold_eval (t : ConstTable) (b : BExp) (s : State)
    (h : ConstApprox t s) :
    (bfold t b).eval s = b.eval s := by
  induction b with
  | truth _v => rfl
  | eq l r =>
      have hal : (afold t l).eval s = l.eval s :=
        afold_eval t l s h
      have har : (afold t r).eval s = r.eval s :=
        afold_eval t r s h
      cases hl : afold t l with
      | const _m =>
          cases hr : afold t r with
          | const _n => simp_all [bfold, BExp.eval]
          | var _x => simp_all [bfold, BExp.eval]
          | add _a _b => simp_all [bfold, BExp.eval]
          | sub _a _b => simp_all [bfold, BExp.eval]
          | mul _a _b => simp_all [bfold, BExp.eval]
      | var _x =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | add _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | sub _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | mul _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
  | le l r =>
      have hal : (afold t l).eval s = l.eval s :=
        afold_eval t l s h
      have har : (afold t r).eval s = r.eval s :=
        afold_eval t r s h
      cases hl : afold t l with
      | const _m =>
          cases hr : afold t r with
          | const _n => simp_all [bfold, BExp.eval]
          | var _x => simp_all [bfold, BExp.eval]
          | add _a _b => simp_all [bfold, BExp.eval]
          | sub _a _b => simp_all [bfold, BExp.eval]
          | mul _a _b => simp_all [bfold, BExp.eval]
      | var _x =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | add _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | sub _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
      | mul _a _b =>
          cases hr : afold t r <;> simp_all [bfold, BExp.eval]
  | not b ih =>
      cases hb : bfold t b with
      | truth _v => simp_all [bfold, BExp.eval]
      | eq _l _r => simp_all [bfold, BExp.eval]
      | le _l _r => simp_all [bfold, BExp.eval]
      | not _c => simp_all [bfold, BExp.eval]
      | and _l _r => simp_all [bfold, BExp.eval]
  | and l r ihl ihr =>
      cases hl : bfold t l with
      | truth _a =>
          cases hr : bfold t r with
          | truth _b => simp_all [bfold, BExp.eval]
          | eq _l _r => simp_all [bfold, BExp.eval]
          | le _l _r => simp_all [bfold, BExp.eval]
          | not _c => simp_all [bfold, BExp.eval]
          | and _l _r => simp_all [bfold, BExp.eval]
      | eq _l _r =>
          cases hr : bfold t r <;> simp_all [bfold, BExp.eval]
      | le _l _r =>
          cases hr : bfold t r <;> simp_all [bfold, BExp.eval]
      | not _c =>
          cases hr : bfold t r <;> simp_all [bfold, BExp.eval]
      | and _l _r =>
          cases hr : bfold t r <;> simp_all [bfold, BExp.eval]

/-- Variables that a command may assign. -/
private def assignedVars : Cmd → List Nat
  | .skip => []
  | .assign x _ => [x]
  | .seq c1 c2 => assignedVars c1 ++ assignedVars c2
  | .ite _ c1 c2 => assignedVars c1 ++ assignedVars c2
  | .while _ b => assignedVars b

/-- Table restricted to variables a command never assigns. -/
private def stableTable (t : ConstTable) (b : Cmd) :
    ConstTable :=
  fun x => if x ∈ assignedVars b then none else t x

private theorem stableTable_approx {t : ConstTable} {b : Cmd}
    {s : State} (h : ConstApprox t s) :
    ConstApprox (stableTable t b) s := by
  intro x n hx
  have hx' : (if x ∈ assignedVars b then none else t x) =
      some n := hx
  cases Decidable.em (x ∈ assignedVars b) with
  | inl hm =>
      simp [hm] at hx'
  | inr hm =>
      simp only [hm, ↓reduceIte] at hx'
      exact h x n hx'

private theorem stableTable_idem (t : ConstTable) (b : Cmd) :
    stableTable (stableTable t b) b = stableTable t b := by
  apply funext
  intro x
  cases Decidable.em (x ∈ assignedVars b) with
  | inl hm => simp [stableTable, hm]
  | inr hm => simp [stableTable, hm]

private theorem not_mem_append_left {x : Nat} {l1 l2 : List Nat}
    (h : x ∉ l1 ++ l2) : x ∉ l1 := by
  simp only [List.mem_append] at h
  exact fun hm => h (Or.inl hm)

private theorem not_mem_append_right {x : Nat} {l1 l2 : List Nat}
    (h : x ∉ l1 ++ l2) : x ∉ l2 := by
  simp only [List.mem_append] at h
  exact fun hm => h (Or.inr hm)

private theorem bigStep_unchanged_of_not_mem {c : Cmd}
    {s f : State} {x : Nat} (h : BigStep c s f)
    (hx : x ∉ assignedVars c) : f x = s x := by
  induction h with
  | skip => rfl
  | assign =>
      simp only [assignedVars] at hx
      simp at hx
      unfold Function.update
      simp [hx]
  | seq _h1 _h2 ih1 ih2 =>
      have hx1 := not_mem_append_left hx
      have hx2 := not_mem_append_right hx
      exact (ih2 hx2).trans (ih1 hx1)
  | iteTrue _gT _bS ih =>
      have hx1 := not_mem_append_left hx
      exact ih hx1
  | iteFalse _gF _bS ih =>
      have hx2 := not_mem_append_right hx
      exact ih hx2
  | whileFalse _gF => rfl
  | whileTrue _gT _bS _lS ihB ihL =>
      exact (ihL hx).trans (ihB hx)

private theorem stableTable_approx_of_step {t : ConstTable}
    {b : Cmd} {s m : State} (h : ConstApprox t s)
    (hstep : BigStep b s m) :
    ConstApprox (stableTable t b) m := by
  intro x n hx
  have hx' : (if x ∈ assignedVars b then none else t x) =
      some n := hx
  cases Decidable.em (x ∈ assignedVars b) with
  | inl hm =>
      simp [hm] at hx'
  | inr hm =>
      simp only [hm, ↓reduceIte] at hx'
      have hxm : m x = s x :=
        bigStep_unchanged_of_not_mem hstep hm
      have hsx : s x = n := h x n hx'
      rw [hxm, hsx]

private theorem stableTable_approx_of_step_stable {t : ConstTable}
    {b : Cmd} {s m : State}
    (h : ConstApprox (stableTable t b) s)
    (hstep : BigStep b s m) :
    ConstApprox (stableTable t b) m := by
  have h1 := stableTable_approx_of_step h hstep
  rw [stableTable_idem] at h1
  exact h1

/-- Fold a command, threading through known constants. -/
private def foldCmd : ConstTable → Cmd → Cmd × ConstTable
  | t, .skip => (.skip, t)
  | t, .assign x a =>
      let a' := afold t a
      (.assign x a', fun y => if y = x then litVal a' else t y)
  | t, .seq c1 c2 =>
      let (c1', t1) := foldCmd t c1
      let (c2', t2) := foldCmd t1 c2
      (.seq c1' c2', t2)
  | t, .ite g c1 c2 =>
      let (c1', t1) := foldCmd t c1
      let (c2', t2) := foldCmd t c2
      let joined : List (Nat × Option Nat) :=
        (assignedVars c1 ++ assignedVars c2).map
          (fun y => (y, if t1 y = t2 y then t1 y else none))
      (.ite (bfold t g) c1' c2',
        fun x => match joined.lookup x with | some v => v | none => t x)
  | t, .while g b =>
      let ts := stableTable t b
      (.while (bfold ts g) (foldCmd ts b).1, ts)

private theorem foldCmd_fst_skip (t : ConstTable) :
    (foldCmd t .skip).1 = .skip := rfl

private theorem foldCmd_snd_skip (t : ConstTable) :
    (foldCmd t .skip).2 = t := rfl

private theorem foldCmd_fst_assign (t : ConstTable) (x : Nat)
    (a : AExp) :
    (foldCmd t (.assign x a)).1 = .assign x (afold t a) :=
  rfl

private theorem foldCmd_snd_assign (t : ConstTable) (x : Nat)
    (a : AExp) :
    (foldCmd t (.assign x a)).2 =
      fun y => if y = x then litVal (afold t a) else t y :=
  rfl

private theorem foldCmd_fst_seq (t : ConstTable) (c1 c2 : Cmd) :
    (foldCmd t (.seq c1 c2)).1 =
      .seq (foldCmd t c1).1 (foldCmd (foldCmd t c1).2 c2).1 :=
  rfl

private theorem foldCmd_snd_seq (t : ConstTable) (c1 c2 : Cmd) :
    (foldCmd t (.seq c1 c2)).2 =
      (foldCmd (foldCmd t c1).2 c2).2 :=
  rfl

private theorem foldCmd_fst_ite (t : ConstTable) (g : BExp)
    (c1 c2 : Cmd) :
    (foldCmd t (.ite g c1 c2)).1 =
      .ite (bfold t g) (foldCmd t c1).1 (foldCmd t c2).1 :=
  rfl

private theorem foldCmd_snd_ite (t : ConstTable) (g : BExp)
    (c1 c2 : Cmd) :
    (foldCmd t (.ite g c1 c2)).2 =
      fun x => match (((assignedVars c1 ++ assignedVars c2).map
          (fun y => (y, if (foldCmd t c1).2 y = (foldCmd t c2).2 y then
            (foldCmd t c1).2 y else none)))).lookup x with
        | some v => v | none => t x := rfl

private theorem foldCmd_fst_while (t : ConstTable) (g : BExp)
    (b : Cmd) :
    (foldCmd t (.while g b)).1 =
      .while (bfold (stableTable t b) g)
        (foldCmd (stableTable t b) b).1 :=
  rfl

private theorem foldCmd_snd_while (t : ConstTable) (g : BExp)
    (b : Cmd) :
    (foldCmd t (.while g b)).2 = stableTable t b := rfl

private theorem lookup_map_mem {l : List Nat} {f : Nat → Option Nat}
    {x : Nat} (h : x ∈ l) :
    (l.map (fun y => (y, f y))).lookup x = some (f x) := by
  induction l with
  | nil =>
      simp at h
  | cons hd tl ih =>
      simp only [List.map_cons, List.mem_cons] at h ⊢
      by_cases hdx : hd = x
      · subst hdx
        have hself : (hd == hd) = true := beq_iff_eq.mpr rfl
        rw [List.lookup.eq_2, hself]
      · have hmem : x ∈ tl := by
          cases h with
          | inl he => exact absurd he (Ne.symm hdx)
          | inr hm => exact hm
        have hbeq : (x == hd) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm hdx)
        rw [List.lookup.eq_2, hbeq]
        exact ih hmem

private theorem lookup_map_none {l : List Nat} {f : Nat → Option Nat}
    {x : Nat} (h : x ∉ l) :
    (l.map (fun y => (y, f y))).lookup x = none := by
  induction l with
  | nil =>
      simp
  | cons hd tl ih =>
      simp only [List.map_cons] at ⊢
      simp only [List.mem_cons, not_or] at h
      obtain ⟨hne, hmem⟩ := h
      have hbeq : (x == hd) = false :=
        beq_eq_false_iff_ne.mpr hne
      rw [List.lookup.eq_2, hbeq]
      exact ih hmem

private theorem ConstApprox_congr {tNew tOld : ConstTable} {f : State}
    (heq : ∀ x, tNew x = tOld x) (h : ConstApprox tOld f) :
    ConstApprox tNew f := by
  intro x n hx
  exact h x n ((heq x).symm.trans hx)

private theorem materialized_join_apply {t t1 t2 : ConstTable} {c1 c2 : Cmd}
    (x : Nat) :
    (fun x => match (((assignedVars c1 ++ assignedVars c2).map
        (fun y => (y, if t1 y = t2 y then t1 y else none)))).lookup x with
      | some v => v | none => t x) x
    = (fun x => if x ∈ assignedVars c1 ++ assignedVars c2 then
        (if t1 x = t2 x then t1 x else none) else t x) x := by
  cases Decidable.em (x ∈ assignedVars c1 ++ assignedVars c2) with
  | inl hm =>
      have hlook := lookup_map_mem
        (l := assignedVars c1 ++ assignedVars c2)
        (f := fun y => if t1 y = t2 y then t1 y else none) hm
      simp only [hm, hlook, ↓reduceIte]
  | inr hm =>
      have hlook := lookup_map_none
        (l := assignedVars c1 ++ assignedVars c2)
        (f := fun y => if t1 y = t2 y then t1 y else none) hm
      simp only [hm, hlook, ↓reduceIte]

private theorem foldCmd_snd_of_not_mem {t : ConstTable} {c : Cmd} {x : Nat}
    (hx : x ∉ assignedVars c) : (foldCmd t c).2 x = t x := by
  induction c generalizing t with
  | skip => rfl
  | assign y a =>
      simp only [assignedVars] at hx
      simp at hx
      rw [foldCmd_snd_assign]
      simp [hx]
  | seq c1 c2 ih1 ih2 =>
      simp only [assignedVars] at hx
      have hx1 := not_mem_append_left hx
      have hx2 := not_mem_append_right hx
      rw [foldCmd_snd_seq]
      exact (ih2 (t := (foldCmd t c1).2) hx2).trans (ih1 (t := t) hx1)
  | ite g c1 c2 _ih1 _ih2 =>
      simp only [assignedVars] at hx
      rw [foldCmd_snd_ite]
      have hnone := lookup_map_none
        (l := assignedVars c1 ++ assignedVars c2)
        (f := fun y => if (foldCmd t c1).2 y = (foldCmd t c2).2 y then
          (foldCmd t c1).2 y else none) hx
      simp only [hnone]
  | «while» g b _ih =>
      simp only [assignedVars] at hx
      rw [foldCmd_snd_while]
      simp [stableTable, hx]

private theorem assignTable_approx {t : ConstTable} {s : State}
    {x : Nat} {a : AExp} (h : ConstApprox t s) :
    ConstApprox
      (fun y => if y = x then litVal (afold t a) else t y)
      (Function.update s x (a.eval s)) := by
  intro y n hy
  have hy' : (if y = x then litVal (afold t a) else t y) =
      some n := hy
  cases Decidable.em (y = x) with
  | inl heq =>
      simp only [heq, ↓reduceIte] at hy'
      have hav := litVal_eq_some hy'
      have he := afold_eval t a s h
      rw [hav] at he
      simp only [AExp.eval_const] at he
      rw [heq]
      unfold Function.update
      simp only [↓reduceDIte]
      exact he.symm
  | inr heq =>
      simp only [heq, ↓reduceIte] at hy'
      unfold Function.update
      simp only [heq, ↓reduceDIte]
      exact h y n hy'

private theorem merge_approx {t t1 t2 : ConstTable} {f : State} {c1 c2 : Cmd}
    (h1 : ConstApprox t1 f)
    (heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 → t1 x = t x) :
    ConstApprox
      (fun x => if x ∈ assignedVars c1 ++ assignedVars c2 then
        (if t1 x = t2 x then t1 x else none) else t x) f := by
  intro x n hx
  have hx' : (if x ∈ assignedVars c1 ++ assignedVars c2 then
      (if t1 x = t2 x then t1 x else none) else t x) =
      some n := hx
  cases Decidable.em (x ∈ assignedVars c1 ++ assignedVars c2) with
  | inl hm =>
      simp only [hm, ↓reduceIte] at hx'
      cases Decidable.em (t1 x = t2 x) with
      | inl heq2 =>
          simp only [heq2, ↓reduceIte] at hx'
          have hx2 : t2 x = some n := hx'
          have hx1 : t1 x = some n := by
            rw [heq2]
            exact hx2
          exact h1 x n hx1
      | inr heq2 =>
          simp only [heq2, ↓reduceIte] at hx'
          cases hx'
  | inr hm =>
      simp only [hm, ↓reduceIte] at hx'
      exact h1 x n ((heq x hm).trans hx')

private theorem merge_approx_right {t t1 t2 : ConstTable} {f : State} {c1 c2 : Cmd}
    (h2 : ConstApprox t2 f)
    (heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 → t2 x = t x) :
    ConstApprox
      (fun x => if x ∈ assignedVars c1 ++ assignedVars c2 then
        (if t1 x = t2 x then t1 x else none) else t x) f := by
  intro x n hx
  have hx' : (if x ∈ assignedVars c1 ++ assignedVars c2 then
      (if t1 x = t2 x then t1 x else none) else t x) =
      some n := hx
  cases Decidable.em (x ∈ assignedVars c1 ++ assignedVars c2) with
  | inl hm =>
      simp only [hm, ↓reduceIte] at hx'
      cases Decidable.em (t1 x = t2 x) with
      | inl heq2 =>
          simp only [heq2, ↓reduceIte] at hx'
          have hx2 : t2 x = some n := hx'
          have _hx1 : t1 x = some n := by
            rw [heq2]
            exact hx2
          exact h2 x n hx2
      | inr heq2 =>
          simp only [heq2, ↓reduceIte] at hx'
          cases hx'
  | inr hm =>
      simp only [hm, ↓reduceIte] at hx'
      exact h2 x n ((heq x hm).trans hx')

private theorem forward_skip (t : ConstTable) (s : State)
    (h : ConstApprox t s) :
    BigStep (foldCmd t .skip).1 s s ∧
      ConstApprox (foldCmd t .skip).2 s := by
  rw [foldCmd_fst_skip, foldCmd_snd_skip]
  exact ⟨.skip _, h⟩

private theorem forward_assign (t : ConstTable) (s : State)
    (x : Nat) (a : AExp) (h : ConstApprox t s) :
    BigStep (foldCmd t (.assign x a)).1 s
        (Function.update s x (a.eval s)) ∧
      ConstApprox (foldCmd t (.assign x a)).2
        (Function.update s x (a.eval s)) := by
  have he : (afold t a).eval s = a.eval s :=
    afold_eval t a s h
  rw [foldCmd_fst_assign, foldCmd_snd_assign]
  refine ⟨?_, ?_⟩
  · rw [BigStep.assign_iff, he]
  · exact assignTable_approx h

private theorem forward_seq (t : ConstTable) (c1 c2 : Cmd)
    (s m f : State) (h : ConstApprox t s)
    (ih1 : ∀ t', ConstApprox t' s →
      BigStep (foldCmd t' c1).1 s m ∧
        ConstApprox (foldCmd t' c1).2 m)
    (ih2 : ∀ t', ConstApprox t' m →
      BigStep (foldCmd t' c2).1 m f ∧
        ConstApprox (foldCmd t' c2).2 f) :
    BigStep (foldCmd t (.seq c1 c2)).1 s f ∧
      ConstApprox (foldCmd t (.seq c1 c2)).2 f := by
  rw [foldCmd_fst_seq, foldCmd_snd_seq]
  obtain ⟨h1, a1⟩ := ih1 t h
  obtain ⟨h2, a2⟩ := ih2 _ a1
  exact ⟨.seq h1 h2, a2⟩

private theorem forward_iteTrue (t : ConstTable) (g : BExp)
    (c1 c2 : Cmd) (s f : State) (h : ConstApprox t s)
    (gT : g.eval s = true)
    (ih : ∀ t', ConstApprox t' s →
      BigStep (foldCmd t' c1).1 s f ∧
        ConstApprox (foldCmd t' c1).2 f) :
    BigStep (foldCmd t (.ite g c1 c2)).1 s f ∧
      ConstApprox (foldCmd t (.ite g c1 c2)).2 f := by
  rw [foldCmd_fst_ite, foldCmd_snd_ite]
  have hg : (bfold t g).eval s = true := by
    rw [bfold_eval t g s h]
    exact gT
  obtain ⟨hb, ab⟩ := ih t h
  have heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 →
      (foldCmd t c1).2 x = t x := by
    intro x hx
    exact foldCmd_snd_of_not_mem (not_mem_append_left hx)
  have hmerge := merge_approx (t := t) (t1 := (foldCmd t c1).2)
    (t2 := (foldCmd t c2).2) ab heq
  refine ⟨.iteTrue hg hb, ConstApprox_congr ?_ hmerge⟩
  intro x
  exact materialized_join_apply (t := t) (t1 := (foldCmd t c1).2)
    (t2 := (foldCmd t c2).2) (c1 := c1) (c2 := c2) x

private theorem forward_iteFalse (t : ConstTable) (g : BExp)
    (c1 c2 : Cmd) (s f : State) (h : ConstApprox t s)
    (gF : g.eval s = false)
    (ih : ∀ t', ConstApprox t' s →
      BigStep (foldCmd t' c2).1 s f ∧
        ConstApprox (foldCmd t' c2).2 f) :
    BigStep (foldCmd t (.ite g c1 c2)).1 s f ∧
      ConstApprox (foldCmd t (.ite g c1 c2)).2 f := by
  rw [foldCmd_fst_ite, foldCmd_snd_ite]
  have hg : (bfold t g).eval s = false := by
    rw [bfold_eval t g s h]
    exact gF
  obtain ⟨hb, ab⟩ := ih t h
  have heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 →
      (foldCmd t c2).2 x = t x := by
    intro x hx
    exact foldCmd_snd_of_not_mem (not_mem_append_right hx)
  have hmerge := merge_approx_right (t := t) (t1 := (foldCmd t c1).2)
    (t2 := (foldCmd t c2).2) ab heq
  refine ⟨.iteFalse hg hb, ConstApprox_congr ?_ hmerge⟩
  intro x
  exact materialized_join_apply (t := t) (t1 := (foldCmd t c1).2)
    (t2 := (foldCmd t c2).2) (c1 := c1) (c2 := c2) x

private theorem forward_whileFalse (t : ConstTable) (g : BExp)
    (b : Cmd) (s : State) (h : ConstApprox t s)
    (gF : g.eval s = false) :
    BigStep (foldCmd t (.while g b)).1 s s ∧
      ConstApprox (foldCmd t (.while g b)).2 s := by
  rw [foldCmd_fst_while, foldCmd_snd_while]
  have hts : ConstApprox (stableTable t b) s :=
    stableTable_approx h
  have hg : (bfold (stableTable t b) g).eval s = false := by
    rw [bfold_eval _ g _ hts]
    exact gF
  exact ⟨.whileFalse hg, hts⟩

private theorem forward_whileTrue (t : ConstTable) (g : BExp)
    (b : Cmd) (s m f : State) (h : ConstApprox t s)
    (gT : g.eval s = true) (bStep : BigStep b s m)
    (ihB : ∀ t', ConstApprox t' s →
      BigStep (foldCmd t' b).1 s m ∧
        ConstApprox (foldCmd t' b).2 m)
    (ihL : ∀ t', ConstApprox t' m →
      BigStep (foldCmd t' (.while g b)).1 m f ∧
        ConstApprox (foldCmd t' (.while g b)).2 f) :
    BigStep (foldCmd t (.while g b)).1 s f ∧
      ConstApprox (foldCmd t (.while g b)).2 f := by
  rw [foldCmd_fst_while, foldCmd_snd_while]
  have hts : ConstApprox (stableTable t b) s :=
    stableTable_approx h
  have hg : (bfold (stableTable t b) g).eval s = true := by
    rw [bfold_eval _ g _ hts]
    exact gT
  obtain ⟨hb, _ab⟩ := ihB (stableTable t b) hts
  have htsm : ConstApprox (stableTable t b) m :=
    stableTable_approx_of_step h bStep
  obtain ⟨hl, al⟩ := ihL (stableTable t b) htsm
  rw [foldCmd_fst_while, stableTable_idem] at hl
  rw [foldCmd_snd_while, stableTable_idem] at al
  exact ⟨.whileTrue hg hb hl, al⟩

private theorem foldCmd_forward {t : ConstTable} {c : Cmd}
    {s f : State} (h : ConstApprox t s)
    (hf : BigStep c s f) :
    BigStep (foldCmd t c).1 s f ∧
      ConstApprox (foldCmd t c).2 f := by
  have hall : ∀ (t' : ConstTable), ConstApprox t' s →
      BigStep (foldCmd t' c).1 s f ∧
        ConstApprox (foldCmd t' c).2 f := by
    clear h
    induction hf with
    | skip =>
        intro t' h'
        exact forward_skip t' _ h'
    | assign =>
        intro t' h'
        exact forward_assign t' _ _ _ h'
    | seq _h1 _h2 ih1 ih2 =>
        intro t' h'
        exact forward_seq t' _ _ _ _ _ h' ih1 ih2
    | iteTrue gT _bS ih =>
        intro t' h'
        exact forward_iteTrue t' _ _ _ _ _ h' gT ih
    | iteFalse gF _bS ih =>
        intro t' h'
        exact forward_iteFalse t' _ _ _ _ _ h' gF ih
    | whileFalse gF =>
        intro t' h'
        exact forward_whileFalse t' _ _ _ h' gF
    | whileTrue gT bS _lS ihB ihL =>
        intro t' h'
        exact forward_whileTrue t' _ _ _ _ _ h' gT bS ihB ihL
  exact hall t h

private theorem backward_skip (t : ConstTable) (s f : State)
    (h : ConstApprox t s)
    (hf : BigStep (foldCmd t .skip).1 s f) :
    BigStep .skip s f ∧
      ConstApprox (foldCmd t .skip).2 f := by
  rw [foldCmd_fst_skip] at hf
  rw [foldCmd_snd_skip]
  cases hf
  exact ⟨.skip _, h⟩

private theorem backward_assign (t : ConstTable) (s f : State)
    (x : Nat) (a : AExp) (h : ConstApprox t s)
    (hf : BigStep (foldCmd t (.assign x a)).1 s f) :
    BigStep (.assign x a) s f ∧
      ConstApprox (foldCmd t (.assign x a)).2 f := by
  have he : (afold t a).eval s = a.eval s :=
    afold_eval t a s h
  rw [foldCmd_fst_assign] at hf
  rw [BigStep.assign_iff] at hf
  rw [foldCmd_snd_assign, BigStep.assign_iff]
  refine ⟨?_, ?_⟩
  · rw [hf, he]
  · rw [hf, he]
    exact assignTable_approx h

private theorem backward_seq (t : ConstTable) (c1 c2 : Cmd)
    (s f : State) (h : ConstApprox t s)
    (hf : BigStep (foldCmd t (.seq c1 c2)).1 s f)
    (ih1 : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t c1).1 s f →
        BigStep c1 s f ∧ ConstApprox (foldCmd t c1).2 f)
    (ih2 : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t c2).1 s f →
        BigStep c2 s f ∧ ConstApprox (foldCmd t c2).2 f) :
    BigStep (.seq c1 c2) s f ∧
      ConstApprox (foldCmd t (.seq c1 c2)).2 f := by
  rw [foldCmd_fst_seq] at hf
  rw [BigStep.seq_iff] at hf
  obtain ⟨m, h1, h2⟩ := hf
  obtain ⟨e1, a1⟩ := ih1 t s m h h1
  obtain ⟨e2, a2⟩ := ih2 _ m f a1 h2
  rw [foldCmd_snd_seq]
  exact ⟨.seq e1 e2, a2⟩

private theorem backward_ite (t : ConstTable) (g : BExp)
    (c1 c2 : Cmd) (s f : State) (h : ConstApprox t s)
    (hf : BigStep (foldCmd t (.ite g c1 c2)).1 s f)
    (ih1 : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t c1).1 s f →
        BigStep c1 s f ∧ ConstApprox (foldCmd t c1).2 f)
    (ih2 : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t c2).1 s f →
        BigStep c2 s f ∧ ConstApprox (foldCmd t c2).2 f) :
    BigStep (.ite g c1 c2) s f ∧
      ConstApprox (foldCmd t (.ite g c1 c2)).2 f := by
  rw [foldCmd_fst_ite] at hf
  rw [BigStep.ite_iff] at hf
  rw [foldCmd_snd_ite]
  cases hf with
  | inl hT =>
      obtain ⟨gT, b1⟩ := hT
      have gT' : g.eval s = true := by
        rw [← bfold_eval t g s h]
        exact gT
      obtain ⟨e1, a1⟩ := ih1 t s f h b1
      have heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 →
          (foldCmd t c1).2 x = t x := by
        intro x hx
        exact foldCmd_snd_of_not_mem (not_mem_append_left hx)
      have hmerge := merge_approx (t := t) (t1 := (foldCmd t c1).2)
        (t2 := (foldCmd t c2).2) a1 heq
      refine ⟨.iteTrue gT' e1, ConstApprox_congr ?_ hmerge⟩
      intro x
      exact materialized_join_apply (t := t) (t1 := (foldCmd t c1).2)
        (t2 := (foldCmd t c2).2) (c1 := c1) (c2 := c2) x
  | inr hF =>
      obtain ⟨gF, b2⟩ := hF
      have gF' : g.eval s = false := by
        rw [← bfold_eval t g s h]
        exact gF
      obtain ⟨e2, a2⟩ := ih2 t s f h b2
      have heq : ∀ x, x ∉ assignedVars c1 ++ assignedVars c2 →
          (foldCmd t c2).2 x = t x := by
        intro x hx
        exact foldCmd_snd_of_not_mem (not_mem_append_right hx)
      have hmerge := merge_approx_right (t := t) (t1 := (foldCmd t c1).2)
        (t2 := (foldCmd t c2).2) a2 heq
      refine ⟨.iteFalse gF' e2, ConstApprox_congr ?_ hmerge⟩
      intro x
      exact materialized_join_apply (t := t) (t1 := (foldCmd t c1).2)
        (t2 := (foldCmd t c2).2) (c1 := c1) (c2 := c2) x

private theorem backward_while_aux (t : ConstTable) (g : BExp)
    (b : Cmd)
    (ihB : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t b).1 s f →
        BigStep b s f ∧ ConstApprox (foldCmd t b).2 f) :
    ∀ (s f : State) (c : Cmd)
      (_p : ConstApprox (stableTable t b) s ∧
        (c = .while (bfold (stableTable t b) g)
          (foldCmd (stableTable t b) b).1))
      (_hf : BigStep c s f),
      BigStep (.while g b) s f ∧
        ConstApprox (stableTable t b) f := by
  intro s f c p hf
  revert p
  induction hf with
  | skip =>
      intro p
      have heq := p.2
      simp at heq
  | assign =>
      intro p
      have heq := p.2
      simp at heq
  | seq _h1 _h2 _ih1 _ih2 =>
      intro p
      have heq := p.2
      simp at heq
  | iteTrue _gT _bS _ih =>
      intro p
      have heq := p.2
      simp at heq
  | iteFalse _gF _bS _ih =>
      intro p
      have heq := p.2
      simp at heq
  | whileFalse gF =>
      intro p
      obtain ⟨hts, heq⟩ := p
      simp only [Cmd.while.injEq] at heq
      obtain ⟨hg, hb⟩ := heq
      rw [hg] at gF
      have hbe := bfold_eval _ g _ hts
      rw [hbe] at gF
      exact ⟨.whileFalse gF, hts⟩
  | whileTrue gT bS _lS _ihB ihL =>
      intro p
      obtain ⟨hts, heq⟩ := p
      simp only [Cmd.while.injEq] at heq
      obtain ⟨hg, hb⟩ := heq
      rw [hg] at gT
      rw [hb] at bS
      have hbe := bfold_eval _ g _ hts
      rw [hbe] at gT
      obtain ⟨bodyOrig, _ab⟩ := ihB _ _ _ hts bS
      obtain ⟨loopOrig, al⟩ := ihL
        ⟨stableTable_approx_of_step_stable hts bodyOrig,
          by rw [hg, hb]⟩
      exact ⟨.whileTrue gT bodyOrig loopOrig, al⟩

private theorem backward_while (t : ConstTable) (g : BExp)
    (b : Cmd) (s f : State) (h : ConstApprox t s)
    (ih : ∀ t s f, ConstApprox t s →
      BigStep (foldCmd t b).1 s f →
        BigStep b s f ∧ ConstApprox (foldCmd t b).2 f)
    (hf : BigStep (foldCmd t (.while g b)).1 s f) :
    BigStep (.while g b) s f ∧
      ConstApprox (foldCmd t (.while g b)).2 f := by
  rw [foldCmd_snd_while]
  have hts : ConstApprox (stableTable t b) s :=
    stableTable_approx h
  have hf' : BigStep
      (.while (bfold (stableTable t b) g)
        (foldCmd (stableTable t b) b).1) s f := by
    rw [← foldCmd_fst_while]
    exact hf
  exact backward_while_aux t g b ih s f _ ⟨hts, rfl⟩ hf'

private theorem foldCmd_backward (c : Cmd) :
    ∀ (t : ConstTable) (s f : State) (_h : ConstApprox t s)
      (_hf : BigStep (foldCmd t c).1 s f),
      BigStep c s f ∧ ConstApprox (foldCmd t c).2 f := by
  induction c
  next =>
    intro t s f h hf
    exact backward_skip t s f h hf
  next x a =>
    intro t s f h hf
    exact backward_assign t s f x a h hf
  next c1 c2 ih1 ih2 =>
    intro t s f h hf
    exact backward_seq t c1 c2 s f h hf ih1 ih2
  next g c1 c2 ih1 ih2 =>
    intro t s f h hf
    exact backward_ite t g c1 c2 s f h hf ih1 ih2
  next g b ih =>
    intro t s f h hf
    exact backward_while t g b s f h ih hf

end Cslib.IMP
end

public section

namespace Cslib.IMP

/-- Fold a command using known constants. -/
def fold (t : ConstTable) (c : Cmd) : Cmd := (foldCmd t c).1

end Cslib.IMP
end

@[expose] public section

namespace Cslib.IMP

/-- Folded commands terminate exactly like the originals when the table agrees with the
initial state. -/
theorem fold_equiv (t : ConstTable) (c : Cmd) (s f : State)
    (h : ConstApprox t s) :
    BigStep (fold t c) s f ↔ BigStep c s f := by
  constructor
  · intro hf
    have hf' : BigStep (foldCmd t c).1 s f := hf
    exact (foldCmd_backward c t s f h hf').1
  · intro ho
    have ho' : BigStep (foldCmd t c).1 s f :=
      (foldCmd_forward h ho).1
    exact ho'

/-- Empty-table folding preserves all executions. -/
theorem fold_equiv_empty (c : Cmd) (s f : State) :
    BigStep (fold emptyTable c) s f ↔ BigStep c s f :=
  fold_equiv emptyTable c s f (emptyTable_approx s)

/-- Code compiled from commands constant-folded from the empty table reflects source
executions. -/
theorem compile_fold_correct (c : Cmd) (s s' : State) :
    StackMachine.Steps
        (StackMachine.compile (fold emptyTable c) 0) (0, [], s)
        (StackMachine.codeLength (fold emptyTable c), [], s') ↔
      BigStep c s s' := by
  rw [StackMachine.compile_correct_iff, fold_equiv_empty]

end Cslib.IMP
