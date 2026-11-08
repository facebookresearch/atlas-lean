/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.StackEmbedding

namespace MetaMathlibExt

open Turing TM2Program TM2Embedding Function

/-! A concrete unary adder built from the library: stacks `0, 1` hold the inputs `m, n`,
stack `2` receives `m + n`, stack `3` is scratch. Labels `0`-`3` are the four `xfer` loops of
`add_run`; label `4` halts. -/

/-- Four `xfer` loops computing `c += a + b` with `a = 0`, `b = 1`, `c = 2`, scratch `t = 3`. -/
def adder : Fin 5 → TM2.Stmt (fun _ : Fin 4 => Unit) (Fin 5) Bool
  | 0 => xfer 0 [⟨2, ()⟩, ⟨3, ()⟩] 0 1
  | 1 => xfer 3 [⟨0, ()⟩] 1 2
  | 2 => xfer 1 [⟨2, ()⟩, ⟨3, ()⟩] 2 3
  | 3 => xfer 3 [⟨1, ()⟩] 3 4
  | 4 => .halt

/-- Inputs `m` and `n` in unary on stacks `0` and `1`; the other stacks empty. -/
def adderInit (m n : ℕ) : ∀ _ : Fin 4, List Unit
  | 0 => cnt () m
  | 1 => cnt () n
  | _ => []

/-- `add_run` gives the exact step count `2m + 2n + 4` and the output `m + n`. -/
example (m n : ℕ) : Run adder (2 * m + 2 * n + 4) ⟨some 0, false, adderInit m n⟩
    ⟨some 4, Flag.tag false, update (adderInit m n) 2 (cnt () (m + n + 0))⟩ :=
  add_run (M := adder) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) m n 0 false (adderInit m n) rfl rfl rfl rfl

/-- The kernel agrees on `m = 2`, `n = 3`: after `14` steps the adder is at label `4` with `5`
units on stack `2`, the inputs restored, and the scratch stack empty. -/
example : ((flip bind (TM2.step adder))^[14] (some ⟨some 0, false, adderInit 2 3⟩)).map
    (fun c => (c.l, (c.stk 0).length, (c.stk 1).length, (c.stk 2).length, (c.stk 3).length)) =
    some (some 4, 2, 3, 5, 0) :=
  rfl

/-- One step earlier it is still in the last loop. -/
example : ((flip bind (TM2.step adder))^[13] (some ⟨some 0, false, adderInit 2 3⟩)).map
    (·.l) = some (some 3) :=
  rfl

/-! The same adder embedded in a host with one extra stack (`Fin.castSucc`); `run_embed`
transports the run, and the extra stack is untouched. -/

/-- The stack embedding `Fin 4 ↪ Fin 5` with identical unit alphabets. -/
def castSuccEmb : SEmb (fun _ : Fin 4 => Unit) (fun _ : Fin 5 => Unit) :=
  ⟨Fin.castSucc, Fin.castSucc_injective 4, fun _ => Equiv.refl Unit⟩

/-- The host machine: the embedded adder on labels `0`-`4`. -/
def hostAdder : Fin 5 → TM2.Stmt (fun _ : Fin 5 => Unit) (Fin 5) Bool :=
  fun l => mapS castSuccEmb id (adder l)

example (m n : ℕ) (S' : ∀ _ : Fin 5, List Unit) (hA : Agree castSuccEmb (adderInit m n) S') :
    ∃ T', Run hostAdder (2 * m + 2 * n + 4) ⟨some 0, false, S'⟩
        ⟨some 4, Flag.tag false, T'⟩ ∧
      Agree castSuccEmb (update (adderInit m n) 2 (cnt () (m + n + 0))) T' ∧
      T' 4 = S' 4 := by
  obtain ⟨T', hrun, hagree, hframe⟩ :=
    run_embed (E := castSuccEmb) (φ := id) (M := adder) (M' := hostAdder)
      (fun _ => Or.inl rfl) _ (some 0) false (adderInit m n) 4 (Flag.tag false) _ S'
      (add_run (M := adder) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by decide) m n 0 false (adderInit m n) rfl rfl rfl rfl) hA
  exact ⟨T', hrun, hagree, hframe 4 fun k hk => (Fin.castSucc_lt_last k).ne hk⟩

/-! ### Comparison: `cmp_run` on a concrete comparator

Counters on stacks `0`, `1`, scratch stacks `2`, `3`. The run ends at `out (compare m n)` with
every stack restored, in `3 · min m n + 3 + [m ≠ n]` steps. -/

/-- Labels of the comparator: the comparison loop, the two restore loops per outcome, and one
halting label per outcome. -/
inductive CmpLab
  | loop
  | restoreA (o : Ordering)
  | restoreB (o : Ordering)
  | out (o : Ordering)

/-- The comparator machine. -/
def comparator : CmpLab → TM2.Stmt (fun _ : Fin 4 => Unit) CmpLab Bool
  | .loop => cmpStep 0 1 2 3 () () .loop (.restoreA .lt) (.restoreA .eq) (.restoreA .gt)
  | .restoreA o => xfer 2 [⟨0, ()⟩] (.restoreA o) (.restoreB o)
  | .restoreB o => xfer 3 [⟨1, ()⟩] (.restoreB o) (.out o)
  | .out _ => .halt

example (m n : ℕ) :
    Run comparator (3 * min m n + 3 + (if m = n then 0 else 1))
      ⟨some .loop, false, adderInit m n⟩ ⟨some (.out (compare m n)), Flag.tag false,
        adderInit m n⟩ :=
  cmp_run (M := comparator) (r := CmpLab.restoreA) (rB := CmpLab.restoreB) (out := CmpLab.out)
    rfl (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m n false (adderInit m n) rfl rfl rfl rfl

/-- Run the comparator on `(m, n)` for `k` steps; report the label and all stack heights. -/
def cmpRun (m n k : ℕ) :=
  ((flip bind (TM2.step comparator))^[k] (some ⟨some .loop, false, adderInit m n⟩)).map
    fun c => (c.l, (c.stk 0).length, (c.stk 1).length, (c.stk 2).length, (c.stk 3).length)

/-- Both counters zero: `eq` after `3` steps. -/
example : cmpRun 0 0 3 = some (some (.out .eq), 0, 0, 0, 0) := rfl
/-- Zero against nonzero: `lt` after `4` steps, the nonzero counter restored. -/
example : cmpRun 0 2 4 = some (some (.out .lt), 0, 2, 0, 0) := rfl
/-- `gt` after `3 · 1 + 4 = 7` steps; not yet halted after `6`. -/
example : cmpRun 3 1 7 = some (some (.out .gt), 3, 1, 0, 0) := rfl
example : (cmpRun 3 1 6).map (·.1) = some (some (.restoreB .gt)) := rfl
/-- Equal nonzero counters: `eq` after `3 · 2 + 3 = 9` steps. -/
example : cmpRun 2 2 9 = some (some (.out .eq), 2, 2, 0, 0) := rfl

/-! ### For-loops: `mul_run` on a concrete multiplier, including the empty loop -/

/-- `c += a · b` with `a = 0`, index `ad = 1`, `b = 2`, `c = 3`, scratch `t = 4`; labels
`0` head, `1` body, `2` restore `b`, `3` restore `a`, `4` halt. -/
def multiplier : Fin 5 → TM2.Stmt (fun _ : Fin 5 => Unit) (Fin 5) Bool
  | 0 => forHead 0 1 () 1 3
  | 1 => xfer 2 [⟨3, ()⟩, ⟨4, ()⟩] 1 2
  | 2 => xfer 4 [⟨2, ()⟩] 2 0
  | 3 => xfer 1 [⟨0, ()⟩] 3 4
  | 4 => .halt

/-- Inputs `m` on stack `0` and `n` on stack `2`. -/
def mulInit (m n : ℕ) : ∀ _ : Fin 5, List Unit
  | 0 => cnt () m
  | 2 => cnt () n
  | _ => []

example (m n : ℕ) : Run multiplier (m * (2 * n + 3) + m + 2) ⟨some 0, false, mulInit m n⟩
    ⟨some 4, Flag.tag false, update (mulInit m n) 3 (cnt () (m * n + 0))⟩ :=
  mul_run (M := multiplier) rfl rfl rfl rfl (by decide) m n 0 false (mulInit m n) rfl rfl rfl
    rfl rfl

/-- Run the multiplier on `(m, n)` for `k` steps; report the label and all stack heights. -/
def mulRun (m n k : ℕ) :=
  ((flip bind (TM2.step multiplier))^[k] (some ⟨some 0, false, mulInit m n⟩)).map
    fun c => (c.l, (c.stk 0).length, (c.stk 1).length, (c.stk 2).length, (c.stk 3).length,
      (c.stk 4).length)

/-- The empty loop (`m = 0`) takes `2` steps and leaves `c = 0`. -/
example : mulRun 0 3 2 = some (some 4, 0, 0, 3, 0, 0) := rfl
/-- `2 · 3`: `2 · 9 + 2 + 2 = 22` steps, `c = 6`, inputs restored, index and scratch empty. -/
example : mulRun 2 3 22 = some (some 4, 2, 0, 3, 6, 0) := rfl
example : (mulRun 2 3 21).map (·.1) = some (some 3) := rfl

/-! ### Gap emission: `emitDiff_run` with a two-symbol block -/

/-- Labels of the gap emitter. -/
inductive GapLab
  | dec | cmpL | emitL | ifZero | done
  | restoreA (o : Ordering)
  | restoreB (o : Ordering)

/-- Decrement `P = 0` while it differs from `Q = 1`, prepending `[true, false]` to stack `4`
each round; scratch stacks `2`, `3`. -/
def gapEmitter : GapLab → TM2.Stmt (fun _ : Fin 5 => Bool) GapLab Bool
  | .dec => decr 0 .ifZero .cmpL
  | .cmpL => cmpStep 0 1 2 3 true true .cmpL (.restoreA .lt) (.restoreA .eq) (.restoreA .gt)
  | .restoreA o => xfer 2 [⟨0, true⟩] (.restoreA o) (.restoreB o)
  | .restoreB o => xfer 3 [⟨1, true⟩] (.restoreB o) (if o = .eq then .done else .emitL)
  | .emitL => emitR 4 [true, false] .dec
  | .ifZero => .halt
  | .done => .halt

/-- `P = q + gap + 1` units and `Q = q` units. -/
def gapInit (q gap : ℕ) : ∀ _ : Fin 5, List Bool
  | 0 => cnt true (q + gap + 1)
  | 1 => cnt true q
  | _ => []

example (q gap : ℕ) : Run gapEmitter (gap * (3 * q + 6) + 3 * q + 4)
    ⟨some .dec, false, gapInit q gap⟩
    ⟨some .done, Flag.tag false,
      update (update (gapInit q gap) 0 (cnt true q)) 4 (rep [true, false] gap ++ [])⟩ :=
  emitDiff_run (M := gapEmitter) (r := GapLab.restoreA) (rB := GapLab.restoreB)
    (out := fun o => if o = .eq then .done else .emitL) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl (by decide) q gap false (gapInit q gap) rfl rfl rfl rfl

/-- `q = 1`, `gap = 2`: `2 · 9 + 3 + 4 = 25` steps, two copies of the block, `P = Q = 1`. -/
example : ((flip bind (TM2.step gapEmitter))^[25] (some ⟨some .dec, false, gapInit 1 2⟩)).map
    (fun c => (c.l, (c.stk 0).length, (c.stk 1).length, (c.stk 4 : List Bool))) =
    some (some .done, 1, 1, [true, false, true, false]) := rfl

/-- `gap = 0`: nothing is emitted (`3 · 1 + 4 = 7` steps). -/
example : ((flip bind (TM2.step gapEmitter))^[7] (some ⟨some .dec, false, gapInit 1 0⟩)).map
    (fun c => (c.l, (c.stk 4 : List Bool))) = some (some .done, []) := rfl

/-! ### Bounded runs -/

/-- An exact run is a bounded run for any larger budget, and bounded runs compose. -/
example : RunLe adder 30 ⟨some 0, false, adderInit 2 3⟩
    ⟨some 4, Flag.tag false, update (adderInit 2 3) 2 (cnt () (2 + 3 + 0))⟩ :=
  ((add_run (M := adder) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) 2 3 0 false (adderInit 2 3) rfl rfl rfl rfl).le (B := 14) (by omega)).trans
    (RunLe.refl 16 _)

/-! ### Embedding with `peek` and a nontrivial alphabet bijection

The host stores the negation of every sub-machine symbol (`ι` is Boolean negation). A block that
peeks the top symbol into the state and pushes it again is run on the host: the state sees the
sub-machine's symbol and the host stack receives its negation. -/

/-- One stack, stored negated on the host. -/
def notEmb : SEmb (fun _ : Unit => Bool) (fun _ : Unit => Bool) :=
  ⟨id, injective_id, fun _ => ⟨not, not, Bool.not_not, Bool.not_not⟩⟩

/-- Peek the top symbol into the state, push it back, halt. -/
def peekPush : TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  .peek () (fun _ o => o.getD false) (.push () (fun s => s) .halt)

example : (TM2.stepAux peekPush false fun _ => [true]).var = true := rfl
example : (TM2.stepAux peekPush false fun _ => [true]).stk () = [true, true] := rfl

/-- On the host, whose stack holds `[false]` (the negation of `[true]`): the state is the
sub-machine's `true`, and the host stack is `[false, false]`. -/
example : (TM2.stepAux (mapS notEmb id peekPush) false fun _ => [false]).var = true := rfl
example : (TM2.stepAux (mapS notEmb id peekPush) false fun _ => [false]).stk () =
    [false, false] := rfl

/-- `stepAux_mapS` predicts exactly this. -/
example : ∃ T', TM2.stepAux (mapS notEmb id peekPush) false (fun _ => [false]) =
      ⟨(TM2.stepAux peekPush false fun _ => [true]).l.map id,
        (TM2.stepAux peekPush false fun _ => [true]).var, T'⟩ ∧
    Agree notEmb (TM2.stepAux peekPush false fun _ => [true]).stk T' ∧
    Frame notEmb (fun _ => [false]) T' :=
  stepAux_mapS (E := notEmb) id peekPush false _ _ fun _ => rfl

end MetaMathlibExt
