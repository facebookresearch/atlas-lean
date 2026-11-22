/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
public meta import CSLibExt.Computability.Complexity.Host

/-! Tests for the generic reduction and verifier hosts: two tiny components (reverse a bit list,
leaving a junk copy behind; compare two lengths), their run lemmas, the resulting `IsPolyTime`
results, and fuelled runs of the two host machines. -/

@[expose] public section

namespace Cslib.Complexity.Host.Tests

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT
  Cslib.Complexity.Host

/-- Stacks of the test components. -/
inductive TK | X | Y | Z
  deriving DecidableEq

/-- Finitely many test stacks. -/
instance : Fintype TK where
  elems := ⟨↑[TK.X, .Y, .Z], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Labels of the test components. -/
inductive TL | lp | yes | no
  deriving DecidableEq

/-- Finitely many test labels. -/
instance : Fintype TL where
  elems := ⟨↑[TL.lp, .yes, .no], by decide⟩
  complete := fun l => by cases l <;> decide

/-- All three stacks. -/
def st (a b z : List Bool) : TK → List Bool
  | .X => a
  | .Y => b
  | .Z => z

@[simp] theorem update_st_X (a b z l : List Bool) : update (st a b z) .X l = st l b z := by
  funext k; cases k <;> rfl
@[simp] theorem update_st_Y (a b z l : List Bool) : update (st a b z) .Y l = st a l z := by
  funext k; cases k <;> rfl
@[simp] theorem update_st_Z (a b z l : List Bool) : update (st a b z) .Z l = st a b l := by
  funext k; cases k <;> rfl

/-! ### Reduction host: reverse a bit list -/

/-- Pop `X` until it is empty, pushing every bit on `Y` and a junk copy on `Z`; exit at `yes`. -/
def revProg : TL → TM2.Stmt (fun _ : TK => Bool) TL Bool
  | .lp => .peek .X (fun _ o => o.isSome) <| .branch id
      (.pop .X (fun _ o => o.getD false) <| .push .Y id <| .push .Z id <| .goto fun _ => .lp)
      (.goto fun _ => .yes)
  | _ => .halt

/-- The reversal component. -/
abbrev revComp : Comp where
  K := TK
  Γ := fun _ => Bool
  L := TL
  prog := revProg
  ks := [.X, .Y, .Z]
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

theorem revProg_run : ∀ (a b z : List Bool) (v : Bool),
    Run revProg (a.length + 1) ⟨some .lp, v, st a b z⟩
      ⟨some .yes, false, st [] (a.reverse ++ b) (a.reverse ++ z)⟩
  | [], b, z, v => Run.single (by simp [revProg, TM2.stepAux, st])
  | a₀ :: a, b, z, v => by
      have h := revProg_run a (a₀ :: b) (a₀ :: z) a₀
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      exact Run.head (by simp [TM2.step, revProg, TM2.stepAux, st]) h

theorem rev_hrun (x : List Bool) :
    ∃ v S', RunLe revComp.prog ((Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval x.length)
      ⟨some TL.lp, false, update (fun _ => []) (TK.X : revComp.K) (x.map id)⟩
      ⟨some TL.yes, v, S'⟩ ∧ S' (TK.Y : revComp.K) = x.reverse.map (Equiv.refl Bool).symm := by
  have h0 : update (fun _ => []) (TK.X : revComp.K) (x.map id) = st x [] [] := by
    funext k; cases k <;> simp [st]
  refine ⟨false, st [] x.reverse x.reverse, ?_, by simp [st]⟩
  rw [h0]
  exact (by simpa using revProg_run x [] [] false : Run revProg _ _ _).le (by simp)

/-- **`List.reverse` is polynomial-time**, through the reduction host. -/
theorem isPolyTime_reverse : ComplexityTheory.IsPolyTime (List.reverse : List Bool → List Bool) :=
  isPolyTime_reduction (c := revComp) (cX := TK.X) (cO := TK.Y) (gX := id) (start := TL.lp)
    (done := TL.yes) (Equiv.refl Bool) List.reverse (Polynomial.X + Polynomial.C 1) rfl rev_hrun

/-- The reduction host for reversal. -/
def revTM : FinTM2 := rtm revComp TK.X TK.Y id TL.lp TL.yes

/-- Run a `FinTM2` for at most `n` steps. -/
def runF (M : FinTM2) : ℕ → M.Cfg → M.Cfg
  | 0, cfg => cfg
  | n + 1, cfg =>
      match M.step cfg with
      | some cfg' => runF M n cfg'
      | none => cfg

/-- The number of steps until `M` halts, if that happens within `n` steps. -/
def haltSteps (M : FinTM2) : ℕ → M.Cfg → Option ℕ
  | 0, cfg => if cfg.l.isNone then some 0 else none
  | n + 1, cfg =>
      if cfg.l.isNone then some 0
      else (M.step cfg).bind fun cfg' => (haltSteps M n cfg').map (· + 1)

/-- The reversal host after a fuelled run on `x`: halted in state `false`?, the output stack
`comp Y`, and are all other stacks (`inp`, `X1`, `W1`, `out`, `comp X`, `comp Z`) empty? -/
def revRes (x : List Bool) : Bool × List Bool × Bool :=
  let c := runF revTM 200 (initList revTM x)
  (c.l.isNone && !c.var, c.stk (HK.comp TK.Y),
    (c.stk HK.inp).isEmpty && (c.stk HK.X1).isEmpty && (c.stk HK.W1).isEmpty &&
      (c.stk HK.out).isEmpty && (c.stk (HK.comp TK.X)).isEmpty && (c.stk (HK.comp TK.Z)).isEmpty)

-- The output stack holds the reversal; the junk copy on `Z` and every other stack are emptied.
#guard revRes [true, false, false] = (true, [false, false, true], true)
#guard revRes [] = (true, [], true)
#guard revRes [false, true, true, true, false] = (true, [false, true, true, true, false], true)
-- Too little fuel: still running, junk left.
#guard (runF revTM 10 (initList revTM [true, false, false])).l.isSome

-- Exact step counts: `2 n + 2` (phase 0), `1` (reset), `n + 1` (component), `n + 1` cleanup
-- rounds (the junk on `Z`), `1` (halt).
#guard haltSteps revTM 200 (initList revTM [true, false, false]) = some (4 * 3 + 6)
#guard haltSteps revTM 200 (initList revTM []) = some 6
#guard haltSteps revTM 200 (initList revTM [true, true, false, true, false, false]) =
  some (4 * 6 + 6)

/-! ### Verifier host: equal lengths -/

/-- Pop `X` and `Y` together; answer `yes` if both run out at the same time, `no` otherwise
(leaving the rest of the longer one behind). -/
def eqProg : TL → TM2.Stmt (fun _ : TK => Bool) TL Bool
  | .lp => .pop .X (fun _ o => o.isSome) <| .branch id
      (.pop .Y (fun _ o => o.isSome) <| .branch id (.goto fun _ => .lp) (.goto fun _ => .no))
      (.pop .Y (fun _ o => o.isSome) <| .branch id (.goto fun _ => .no) (.goto fun _ => .yes))
  | _ => .halt

/-- The length-comparison component. -/
abbrev eqComp : Comp where
  K := TK
  Γ := fun _ => Bool
  L := TL
  prog := eqProg
  ks := [.X, .Y, .Z]
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

theorem eqProg_run : ∀ (a b z : List Bool) (v : Bool), ∃ v' S',
    RunLe eqProg (a.length + 1) ⟨some .lp, v, st a b z⟩
      ⟨some (if a.length == b.length then .yes else .no), v', S'⟩
  | [], [], z, v =>
      ⟨false, st [] [] z, Run.le (Run.single (by simp [eqProg, TM2.stepAux, st])) le_rfl⟩
  | [], _ :: b, z, v =>
      ⟨true, st [] b z, Run.le (Run.single (by simp [eqProg, TM2.stepAux, st])) le_rfl⟩
  | _ :: a, [], z, v =>
      ⟨false, st a [] z, Run.le (Run.single (by simp [eqProg, TM2.stepAux, st])) (by omega)⟩
  | a₀ :: a, b₀ :: b, z, v => by
      obtain ⟨v', S', n, hn, r⟩ := eqProg_run a b z true
      have hs : TM2.step eqProg ⟨some .lp, v, st (a₀ :: a) (b₀ :: b) z⟩ =
          some ⟨some .lp, true, st a b z⟩ := by
        simp [TM2.step, eqProg, TM2.stepAux, st]
      have e : ((a₀ :: a).length == (b₀ :: b).length) = (a.length == b.length) := by simp
      refine ⟨v', S', n + 1, by simp; omega, ?_⟩
      rw [e]
      exact Run.head hs r

theorem eq_hrun (x w : List Bool) :
    ∃ v S', RunLe eqComp.prog
      ((Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval (x.length + w.length))
      ⟨some TL.lp, false,
        update (update (fun _ => []) (TK.X : eqComp.K) (x.map id)) (TK.Y : eqComp.K)
          (w.map id)⟩
      ⟨some (if x.length == w.length then TL.yes else TL.no), v, S'⟩ := by
  have h0 : update (update (fun _ => []) (TK.X : eqComp.K) (x.map id)) (TK.Y : eqComp.K)
      (w.map id) = st x w [] := by
    funext k; cases k <;> simp [st]
  obtain ⟨v', S', r⟩ := eqProg_run x w [] false
  exact ⟨v', S', by rw [h0]; exact r.mono (by simp)⟩

/-- **Equal lengths is polynomial-time**, through the verifier host. -/
theorem isPolyTime_eqLength :
    ComplexityTheory.IsPolyTime fun q : List Bool × List Bool => q.1.length == q.2.length :=
  isPolyTime_verifier (c := eqComp) (cX := TK.X) (cW := TK.Y) (gX := id) (gW := id)
    (start := TL.lp) (yes := TL.yes) (no := TL.no) (fun x w => x.length == w.length)
    (Polynomial.X + Polynomial.C 1) (by decide) (by decide) rfl rfl eq_hrun

/-- The verifier host for equal lengths. -/
def eqTM : FinTM2 := vtm eqComp TK.X TK.Y id id TL.lp TL.yes TL.no

/-- The verifier host after a fuelled run on `x # w`: halted in state `false`?, the output stack,
and are all other stacks (`inp`, `X1`, `W1`, `comp X`, `comp Y`, `comp Z`) empty? -/
def eqRes (x w : List Bool) : Bool × List Bool × Bool :=
  let c := runF eqTM 500 (initList eqTM (Verifier.pairEncode (x, w)))
  (c.l.isNone && !c.var, c.stk HK.out,
    (c.stk HK.inp).isEmpty && (c.stk HK.X1).isEmpty && (c.stk HK.W1).isEmpty &&
      (c.stk (HK.comp TK.X)).isEmpty && (c.stk (HK.comp TK.Y)).isEmpty &&
        (c.stk (HK.comp TK.Z)).isEmpty)

-- Accepted and rejected inputs; when the lengths differ, the component leaves the rest of the
-- longer list behind and the cleanup removes it.
#guard eqRes [true, false, true] [false, false, true] = (true, [true], true)
#guard eqRes [] [] = (true, [true], true)
#guard eqRes [true, false, true] [true] = (true, [false], true)
#guard eqRes [] [false, true, true, false] = (true, [false], true)
#guard eqRes [true] [] = (true, [false], true)

-- Exact step counts: `2 |x| + 2`, `1`, `2 |w| + 2`, `1` (phase 0), `min + 1` (component),
-- cleanup rounds (one more than the longest leftover), `1` (push the answer).
#guard haltSteps eqTM 500 (initList eqTM (Verifier.pairEncode ([true, false], [false, true]))) =
  some ((2 * 2 + 2) + 1 + (2 * 2 + 2) + 1 + 3 + 1 + 1)
#guard haltSteps eqTM 500 (initList eqTM (Verifier.pairEncode ([true, false, true], []))) =
  some ((2 * 3 + 2) + 1 + 2 + 1 + 1 + 3 + 1)

end Cslib.Complexity.Host.Tests
