/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.TuringMachine.ExactStackEmbedding
public meta import Mathlib.Computability.TuringMachine.StackTuringMachine

@[expose] public section

set_option autoImplicit false

open MetaMathlibExt.TM2Embedding MetaMathlibExt.TM2Program Turing

namespace ExactStackEmbeddingTest

private def notEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

private def middle : SEmb (fun _ : Fin 1 => Bool) (fun _ : Fin 3 => Bool) where
  e _ := 1
  inj _ _ _ := Subsingleton.elim _ _
  ι _ := notEquiv

private def emptySource : Fin 1 → List Bool := fun _ => []

private def hostStart (k : Fin 3) : List Bool :=
  if k = 0 then [true, true] else if k = 1 then [] else [false, true, false]

private def sourceOne : Unit → TM2.Stmt (fun _ : Fin 1 => Bool) Unit Bool :=
  fun _ => .push 0 (fun _ => true) .halt

private def hostOne : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit Bool :=
  fun _ => .push 1 (fun _ => false) .halt

private theorem one_matches (l : Unit) : hostOne l = mapS middle id (sourceOne l) := rfl

private def sourceAfter : Fin 1 → List Bool :=
  Function.update emptySource 0 [true]

private def hostAfter : Fin 3 → List Bool :=
  Function.update hostStart 1 [false]

private theorem initial_agree : Agree middle emptySource hostStart := by
  intro k
  rfl

private theorem source_one :
    Run sourceOne 1 ⟨some (), false, emptySource⟩ ⟨none, false, sourceAfter⟩ :=
  Run.single rfl

-- This importing client requires the new supplied-endpoint theorem.
example : Run hostOne 1 ⟨some (), false, hostStart⟩ ⟨none, false, hostAfter⟩ := by
  apply run_embed_exact_of_agree_frame middle id one_matches source_one initial_agree
  · intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rfl
  · intro k hk
    exact Function.update_of_ne (hk 0).symm _ _

#eval let c := TM2.stepAux (hostOne ()) false hostStart
  (c.l, c.var, [c.stk 0, c.stk 1, c.stk 2])

-- The existential adapter must determine the three literal host-stack outputs.
example : ∃ T', Run hostOne 1 ⟨some (), false, hostStart⟩ ⟨none, false, T'⟩ ∧
    T' 0 = [true, true] ∧ T' 1 = [false] ∧ T' 2 = [false, true, false] := by
  obtain ⟨T', hr, hA, hF⟩ := run_embed_exact middle id one_matches source_one initial_agree
  exact ⟨T', hr, hF 0 (fun _ => (by decide : (1 : Fin 3) ≠ 0)), hA 0,
    hF 2 (fun _ => (by decide : (1 : Fin 3) ≠ 2))⟩

private def sourceTwo (l : Bool) : TM2.Stmt (fun _ : Fin 1 => Bool) Bool Bool :=
  if l then .pop 0 (fun _ o => o.getD false) .halt
  else .push 0 (fun _ => true) (.goto fun _ => true)

private def hostTwo (l : Bool) : TM2.Stmt (fun _ : Fin 3 => Bool) Bool Bool :=
  if l then .push 1 (fun _ => false) (.goto fun _ => false)
  else .pop 1 (fun _ o => (o.map Bool.not).getD false) .halt

private theorem two_matches (l : Bool) :
    hostTwo (Bool.not l) = mapS middle Bool.not (sourceTwo l) := by
  cases l <;> rfl

private theorem source_live :
    Run sourceTwo 1 ⟨some false, false, emptySource⟩ ⟨some true, false, sourceAfter⟩ :=
  Run.single rfl

private theorem source_two :
    Run sourceTwo 2 ⟨some false, false, emptySource⟩ ⟨none, true, emptySource⟩ := by
  apply Run.head (d := ⟨some true, false, sourceAfter⟩) rfl
  apply Run.single
  simp [sourceTwo, sourceAfter, emptySource, TM2.stepAux]

-- Swapped labels and the inverse alphabet map recover the popped source symbol as state.
example : Run hostTwo 2 ⟨some true, false, hostStart⟩ ⟨none, true, hostStart⟩ :=
  run_embed_exact_of_agree_frame middle Bool.not two_matches source_two initial_agree
    initial_agree (Frame.refl hostStart)

private def hostTwoFirst := TM2.step hostTwo ⟨some true, false, hostStart⟩
private def hostTwoResult := hostTwoFirst.bind (TM2.step hostTwo)

#guard hostTwoFirst.map (fun c => (c.l, c.var, [c.stk 0, c.stk 1, c.stk 2])) =
  some (some false, false, [[true, true], [false], [false, true, false]])
#guard hostTwoResult.map (fun c => (c.l, c.var, [c.stk 0, c.stk 1, c.stk 2])) =
  some (none, true, [[true, true], [], [false, true, false]])
#guard (hostTwoResult.bind (TM2.step hostTwo)).map TM2.Cfg.l = none
#eval hostTwoResult.map (fun c => (c.l, c.var, [c.stk 0, c.stk 1, c.stk 2]))

-- A tight budget and one spare step preserve the same populated endpoint.
example : ∃ T', RunLe hostTwo 2 ⟨some true, false, hostStart⟩ ⟨none, true, T'⟩ ∧
    Agree middle emptySource T' ∧ Frame middle hostStart T' :=
  runLe_embed_exact middle Bool.not two_matches ⟨2, by decide, source_two⟩ initial_agree

example : ∃ T', RunLe hostTwo 3 ⟨some true, false, hostStart⟩ ⟨none, true, T'⟩ ∧
    Agree middle emptySource T' ∧ Frame middle hostStart T' :=
  runLe_embed_exact middle Bool.not two_matches ⟨2, by decide, source_two⟩ initial_agree


-- Halted inputs, zero budget, and compatibility with the existing live-endpoint adapter.
example : Run hostOne 0 ⟨none, false, hostStart⟩ ⟨none, false, hostStart⟩ :=
  run_embed_exact_of_agree_frame middle id one_matches
    (Run.zero ⟨none, false, emptySource⟩) initial_agree initial_agree (Frame.refl hostStart)

example {n : ℕ} {c : TM2.Cfg (fun _ : Fin 1 => Bool) Unit Bool} :
    ¬ Run sourceOne (n + 1) ⟨none, false, emptySource⟩ c := by
  intro h
  unfold Run at h
  rw [Function.iterate_succ_apply] at h
  change (flip bind (TM2.step sourceOne))^[n] none = some c at h
  rw [iter_none] at h
  cases h

example : ∃ T', RunLe hostOne 0 ⟨none, false, hostStart⟩ ⟨none, false, T'⟩ ∧
    Agree middle emptySource T' ∧ Frame middle hostStart T' :=
  runLe_embed_exact middle id one_matches (RunLe.refl 0 ⟨none, false, emptySource⟩) initial_agree

#guard (TM2.step hostOne ⟨none, false, hostStart⟩).map TM2.Cfg.l = none

example : ∃ T', Run hostTwo 1 ⟨some true, false, hostStart⟩ ⟨some false, false, T'⟩ ∧
    Agree middle sourceAfter T' ∧ Frame middle hostStart T' :=
  run_embed_exact middle Bool.not two_matches source_live initial_agree

example : ∃ T', Run hostTwo 1 ⟨some true, false, hostStart⟩ ⟨some false, false, T'⟩ ∧
    Agree middle sourceAfter T' ∧ Frame middle hostStart T' :=
  run_embed Bool.not (show Embeds middle Bool.not sourceTwo hostTwo from
    fun l => Or.inl (two_matches l)) 1 (some false) false emptySource true false
      sourceAfter hostStart source_live initial_agree

-- Exact matching does not require label injectivity.
private def collapsedSource : Bool → TM2.Stmt (fun _ : Fin 1 => Bool) Bool Bool :=
  fun _ => .push 0 (fun _ => true) .halt
private def collapse : Bool → Unit := fun _ => ()
private theorem collapsed_matches (l : Bool) :
    hostOne (collapse l) = mapS middle collapse (collapsedSource l) := rfl

example : ¬ Function.Injective collapse := by
  intro h
  have hf : false = true := h rfl
  cases hf

example : Run hostOne 1 ⟨some (), false, hostStart⟩ ⟨none, false, hostAfter⟩ := by
  apply run_embed_exact_of_agree_frame middle collapse collapsed_matches
    (Run.single (M := collapsedSource) (l := true) rfl) initial_agree
  · intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rfl
  · intro k hk
    exact Function.update_of_ne (hk 0).symm _ _

-- With no source stacks, the frame preserves the entire populated host.
private def noStacks : SEmb (fun _ : Fin 0 => Bool) (fun _ : Fin 3 => Bool) where
  e := Fin.elim0
  inj a := Fin.elim0 a
  ι := Fin.elim0
private def noSource : Fin 0 → List Bool := Fin.elim0
private def noProgram : Unit → TM2.Stmt (fun _ : Fin 0 => Bool) Unit Bool :=
  fun _ => .load Bool.not .halt
private def noHostProgram : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit Bool :=
  fun _ => .load Bool.not .halt
private theorem no_matches (l : Unit) :
    noHostProgram l = mapS noStacks id (noProgram l) := rfl

example : Run noHostProgram 1 ⟨some (), false, hostStart⟩ ⟨none, true, hostStart⟩ :=
  run_embed_exact_of_agree_frame noStacks id no_matches
    (Run.single (M := noProgram) (l := ()) (v := false) (S := noSource) rfl)
    (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) (Frame.refl hostStart)

#eval let c := TM2.stepAux (noHostProgram ()) false hostStart
  (c.l, c.var, [c.stk 0, c.stk 1, c.stk 2])

-- Swapped stack indices carry different Nat and Bool alphabets.
private abbrev depAlphabet : Bool → Type
  | false => ℕ
  | true => Bool
private abbrev depHostAlphabet : Bool → Type
  | false => Bool
  | true => ℕ
private def depEmbed : SEmb depAlphabet depHostAlphabet where
  e := Bool.not
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases k <;> exact Equiv.refl _
private def depSource : ∀ k, List (depAlphabet k)
  | false => [7, 9]
  | true => [true, false]
private def depHost : ∀ k, List (depHostAlphabet k)
  | false => [true, false]
  | true => [7, 9]
private def depProgram : Unit → TM2.Stmt depAlphabet Unit Bool :=
  fun _ => .push false (fun _ => 11) (.peek true (fun _ o => o.getD false) .halt)
private def depHostProgram : Unit → TM2.Stmt depHostAlphabet Unit Bool :=
  fun _ => .push true (fun _ => 11) (.peek false (fun _ o => (o.map id).getD false) .halt)
private theorem dep_matches (l : Unit) :
    depHostProgram l = mapS depEmbed id (depProgram l) := rfl
private theorem dep_run :
    Run depProgram 1 ⟨some (), false, depSource⟩
      ⟨none, true, Function.update depSource false [11, 7, 9]⟩ := Run.single rfl

example : Run depHostProgram 1 ⟨some (), false, depHost⟩
    ⟨none, true, Function.update depHost true [11, 7, 9]⟩ :=
  run_embed_exact_of_agree_frame depEmbed id dep_matches dep_run
    (by
      intro k
      cases k <;> rfl)
    (by
      intro k
      cases k <;> rfl)
    (by
      intro k hk
      cases k
      · exact False.elim (hk true rfl)
      · exact False.elim (hk false rfl))

#guard (TM2.stepAux (depHostProgram ()) false depHost).stk true = [11, 7, 9]
#guard (TM2.stepAux (depHostProgram ()) false depHost).stk false = [true, false]
#eval let c := TM2.stepAux (depHostProgram ()) false depHost
  (c.l, c.var, c.stk true, c.stk false)

-- Old Embeds accepts source halt versus host goto-self; exact matching excludes it.
private def sourceHalt : Unit → TM2.Stmt (fun _ : Fin 1 => Bool) Unit Bool := fun _ => .halt
private def hostLoop : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit Bool :=
  fun _ => .goto (fun _ => ())

example : Embeds middle id sourceHalt hostLoop := fun _ => Or.inr rfl

example : Run sourceHalt 1 ⟨some (), false, emptySource⟩ ⟨none, false, emptySource⟩ :=
  Run.single rfl

example : Run hostLoop 1 ⟨some (), false, hostStart⟩ ⟨some (), false, hostStart⟩ :=
  Run.single rfl

example : ¬ Run hostLoop 1 ⟨some (), false, hostStart⟩ ⟨none, false, hostStart⟩ := by
  intro h
  change some (⟨some (), false, hostStart⟩ : TM2.Cfg (fun _ : Fin 3 => Bool) Unit Bool) =
    some ⟨none, false, hostStart⟩ at h
  have hl := congrArg (fun c => c.map TM2.Cfg.l) h
  cases hl

example : ¬ (∀ l, hostLoop (id l) = mapS middle id (sourceHalt l)) := by
  intro h
  have hl := congrArg (fun q => (TM2.stepAux q false hostStart).l) (h ())
  cases hl

#guard (TM2.stepAux (sourceHalt ()) false emptySource).l = none
#guard (TM2.stepAux (hostLoop ()) false hostStart).l = some ()
#eval ((TM2.stepAux (sourceHalt ()) false emptySource).l,
  (TM2.stepAux (hostLoop ()) false hostStart).l)

end ExactStackEmbeddingTest
