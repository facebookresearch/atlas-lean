/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Exec
public import Cslib.Algorithms.Lean.TimeM

/-!
# Operational successful-read cost

`execReads` instruments `exec` with canonical `TimeM Nat`, outside `Option`
so that a later failure retains the cost of the executed prefix. Exactly one
unit is charged per successful bounds-checked array read. Invalid reads and
zero fuel cost zero; arithmetic, guards, assignments and control flow are free.
This is neither instruction count nor wall time, space cost or RAM adequacy.
-/

@[expose] public section

namespace CSLibExt.Languages.MiniImp

open Cslib.Algorithms.Lean

/-- The existing fuel interpreter, instrumented for successful array reads.
Annotations remain ghost data. `TimeM` retains costs even when `ret = none`. -/
def execReads : Nat → Stmt → State → TimeM Nat (Option State)
  | 0, _, _ => pure none
  | fuel + 1, c, s =>
    match c with
    | .skip => pure (some s)
    | .assign x e => pure (some (s.update x (evalA e s)))
    | .read x xs e =>
        if h : evalA e s < xs.size then do
          TimeM.tick 1
          pure (some (s.update x xs[evalA e s]))
        else pure none
    | .seq a b => do
        let t ← execReads fuel a s
        match t with
        | none => pure none
        | some u => execReads fuel b u
    | .if_ b a c =>
        if beval b s then execReads fuel a s else execReads fuel c s
    | .while b I c =>
        if beval b s then do
          let t ← execReads fuel c s
          match t with
          | none => pure none
          | some u => execReads fuel (.while b I c) u
        else pure (some s)

/-- Instrumentation erases to the original interpreter, including failure. -/
@[simp] theorem execReads_ret (fuel : Nat) (c : Stmt) (s : State) :
    (execReads fuel c s).ret = exec fuel c s := by
  induction fuel generalizing c s with
  | zero => rfl
  | succ fuel ih =>
      cases c with
      | skip => rfl
      | assign x e => rfl
      | read x xs e => simp [execReads, exec]; split <;> rfl
      | seq a b =>
          simp only [execReads, TimeM.ret_bind, ih, exec]
          cases exec fuel a s <;> simp [ih]
      | if_ b a c => simp only [execReads, exec]; split <;> exact ih _ _
      | «while» b I c =>
          simp only [execReads, exec]
          split
          · simp only [TimeM.ret_bind, ih]
            cases exec fuel c s <;> simp [ih]
          · rfl

/-- Count actual read transitions in the successful big-step semantics.
The read rule requires the evaluated index bound; ghost annotations add no
cost. Counts compose only through executed subderivations. -/
inductive ReadSteps : Stmt → State → State → Nat → Prop where
  | skip {s : State} : ReadSteps .skip s s 0
  | assign {x : String} {e : AExp} {s : State} :
      ReadSteps (.assign x e) s (s.update x (evalA e s)) 0
  | read {x : String} {xs : Array Nat} {e : AExp} {s : State}
      (h : evalA e s < xs.size) :
      ReadSteps (.read x xs e) s (s.update x xs[evalA e s]) 1
  | seq {a b : Stmt} {s u t : State} {n m : Nat} :
      ReadSteps a s u n → ReadSteps b u t m → ReadSteps (.seq a b) s t (n + m)
  | ifTrue {b : BExp} {a c : Stmt} {s t : State} {n : Nat} :
      beval b s → ReadSteps a s t n → ReadSteps (.if_ b a c) s t n
  | ifFalse {b : BExp} {a c : Stmt} {s t : State} {n : Nat} :
      ¬ beval b s → ReadSteps c s t n → ReadSteps (.if_ b a c) s t n
  | whileTrue {b : BExp} {I : State → Prop} {c : Stmt}
      {s u t : State} {n m : Nat} :
      beval b s → ReadSteps c s u n → ReadSteps (.while b I c) u t m →
        ReadSteps (.while b I c) s t (n + m)
  | whileFalse {b : BExp} {I : State → Prop} {c : Stmt} {s : State} :
      ¬ beval b s → ReadSteps (.while b I c) s s 0

/-- Forgetting the count gives the existing semantics, including its read
safety condition. -/
theorem ReadSteps.erase {c : Stmt} {s t : State} {n : Nat}
    (h : ReadSteps c s t n) : BigStep c s t := by
  induction h with
  | skip => exact .skip
  | assign => exact .assign
  | read hb => exact .read hb
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifTrue hb _ ih => exact .ifTrue hb ih
  | ifFalse hb _ ih => exact .ifFalse hb ih
  | whileTrue hb _ _ ih₁ ih₂ => exact .whileTrue hb ih₁ ih₂
  | whileFalse hb => exact .whileFalse hb

/-- Every existing successful derivation admits a read count. This is an
existence statement in Prop, not an oracle extracting data from a proof. -/
theorem BigStep.exists_readSteps {c : Stmt} {s t : State}
    (h : BigStep c s t) : ∃ n, ReadSteps c s t n := by
  induction h with
  | skip => exact ⟨0, .skip⟩
  | assign => exact ⟨0, .assign⟩
  | read hb => exact ⟨1, .read hb⟩
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨n, hn⟩ := ih₁
      obtain ⟨m, hm⟩ := ih₂
      exact ⟨n + m, .seq hn hm⟩
  | ifTrue hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, .ifTrue hb hn⟩
  | ifFalse hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, .ifFalse hb hn⟩
  | whileTrue hb _ _ ih₁ ih₂ =>
      obtain ⟨n, hn⟩ := ih₁
      obtain ⟨m, hm⟩ := ih₂
      exact ⟨n + m, .whileTrue hb hn hm⟩
  | whileFalse hb => exact ⟨0, .whileFalse hb⟩

/-- Every successful instrumented run has exactly its charged number of
actual successful read transitions. -/
theorem execReads_sound {fuel : Nat} {c : Stmt} {s t : State}
    (h : (execReads fuel c s).ret = some t) :
    ReadSteps c s t (execReads fuel c s).time := by
  induction fuel generalizing c s t with
  | zero => simp [execReads] at h
  | succ fuel ih =>
      cases c with
      | skip => cases h; exact .skip
      | assign x e => cases h; exact .assign
      | read x xs e =>
          by_cases hb : evalA e s < xs.size
          · simp [execReads, hb] at h
            subst t
            simpa [execReads, hb] using ReadSteps.read hb
          · simp [execReads, hb] at h
      | seq a b =>
          simp only [execReads, TimeM.ret_bind] at h
          cases ha : (execReads fuel a s).ret with
          | none => simp only [ha, TimeM.ret_pure, reduceCtorEq] at h
          | some u =>
              have hb : (execReads fuel b u).ret = some t := by
                simpa only [ha] using h
              simpa only [execReads, TimeM.time_bind, ha] using
                ReadSteps.seq (ih ha) (ih hb)
      | if_ b a c =>
          by_cases hb : beval b s
          · simp only [execReads, ite_eq_left hb] at h ⊢
            exact .ifTrue hb (ih h)
          · simp only [execReads, ite_eq_right hb] at h ⊢
            exact .ifFalse hb (ih h)
      | «while» b I c =>
          by_cases hb : beval b s
          · simp only [execReads, ite_eq_left hb, TimeM.ret_bind] at h
            cases hc : (execReads fuel c s).ret with
            | none => simp only [hc, TimeM.ret_pure, reduceCtorEq] at h
            | some u =>
                have hw : (execReads fuel (.while b I c) u).ret = some t := by
                  simpa only [hc] using h
                simpa only
                  [execReads, ite_eq_left hb, TimeM.time_bind, hc] using
                  ReadSteps.whileTrue hb (ih hc) (ih hw)
          · simp only [execReads, ite_eq_right hb, TimeM.ret_pure] at h
            cases h
            simpa only [execReads, ite_eq_right hb, TimeM.time_pure] using
              ReadSteps.whileFalse (I := I) (c := c) hb

/-- An invalid read performs no array access, at every fuel. -/
theorem execReads_read_invalid (fuel : Nat) {x : String} {xs : Array Nat}
    {e : AExp} {s : State} (h : ¬ evalA e s < xs.size) :
    execReads fuel (.read x xs e) s = pure none := by
  cases fuel <;> simp [execReads, h]

/-- Failure retains the entire executed left prefix and skips the right
command, including when that prefix itself contains successful reads. -/
theorem execReads_seq_failed {fuel : Nat} {a b : Stmt} {s : State}
    (h : (execReads fuel a s).ret = none) :
    execReads (fuel + 1) (.seq a b) s = execReads fuel a s := by
  apply TimeM.ext
  · simp only [execReads, TimeM.ret_bind, h, TimeM.ret_pure]
  · simp only [execReads, TimeM.time_bind, h, TimeM.time_pure, Nat.add_zero]

end CSLibExt.Languages.MiniImp
