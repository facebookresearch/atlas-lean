/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.IMPBridge
public import CSLibExt.Languages.MiniImp.Exec
public meta import CSLibExt.Languages.MiniImp.IMPBridge
public meta import CSLibExt.Languages.MiniImp.Exec

open CSLibExt.Languages.MiniImp
open CSLibExt.Languages.MiniImp.IMPBridge

-- Variable 0 maps to "v", variable 1 to "vv", and so on, never to "".
private def rename (n : Nat) : String :=
  String.ofList (List.replicate (n + 1) 'v')

private theorem rename_injective : Function.Injective rename := by
  intro n m h
  have hl := congrArg String.length h
  simpa [rename] using hl

private theorem empty_unmapped (n : Nat) : "" ≠ rename n := by
  intro h
  have hl := congrArg String.length h
  simp [rename] at hl

private def factorial : Cslib.IMP.Cmd :=
  .seq (.assign 1 (.const 1))
    (.while (.not (.eq (.var 0) (.const 0)))
      (.seq (.assign 1 (.mul (.var 1) (.var 0)))
        (.assign 0 (.sub (.var 0) (.const 1)))))

private def initial (n : Nat) : State :=
  State.update (fun _ => 99) (rename 0) n

private def observe (s : State) : Nat × Nat × Nat :=
  (s (rename 0), s (rename 1), s "")

-- A real translated loop: four iterations, result 4! = 24, frame value 99.
#eval (exec 20 (command rename factorial) (initial 4)).map observe
example : (exec 20 (command rename factorial) (initial 4)).map observe =
    some (0, 24, 99) := by decide
example : (exec 20 (command rename factorial) (initial 0)).map observe =
    some (0, 1, 99) := by decide

-- The runtime witness reflects to the actual canonical BigStep relation.
example : ∃ t,
    BigStep (command rename factorial) (initial 4) t ∧
    Cslib.IMP.BigStep factorial (project rename (initial 4))
      (project rename t) ∧ observe t = (0, 24, 99) := by
  have hr : (exec 20 (command rename factorial) (initial 4)).map observe =
      some (0, 24, 99) := by decide
  obtain ⟨t, ht, hv⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨t, exec_sound ht, reflect_execution rename_injective (exec_sound ht),
    hv⟩

-- The forward direction constructs a target state for a canonical assignment.
example (s : State) : ∃ t,
    BigStep (command rename (.assign 1 (.mul (.var 0) (.const 3)))) s t ∧
      project rename t = Function.update (project rename s) 1
        ((project rename s) 0 * 3) :=
  lift_execution rename_injective
    (Cslib.IMP.BigStep.assign (project rename s) 1
      (.mul (.var 0) (.const 3))) s rfl

example {t : State} (h : BigStep (command rename factorial) (initial 4) t) :
    t "" = 99 := by
  have hf := unmapped_preserved rename_injective h "" empty_unmapped
  simpa [initial, State.update, rename] using hf

private def branch : Cslib.IMP.Cmd :=
  .ite (.and (.le (.var 0) (.const 3))
      (.eq (.add (.var 0) (.const 1)) (.const 4)))
    (.assign 1 (.mul (.var 0) (.const 3))) (.assign 1 (.const 7))

#eval [(exec 5 (command rename branch) (initial 3)).map observe,
  (exec 5 (command rename branch) (initial 4)).map observe]
example : (exec 5 (command rename branch) (initial 3)).map observe =
    some (3, 9, 99) := by decide
example : (exec 5 (command rename branch) (initial 4)).map observe =
    some (4, 7, 99) := by decide
example : (exec 3 (command rename
    (.ite (.truth false) (.assign 0 (.const 0)) .skip)) (initial 4)).map
    observe = some (4, 99, 99) := by decide
example : beval (boolean rename (.truth true)) (initial 4) := by decide

-- Transfer a real canonical assignment triple, not a caller-supplied bridge.
example : Hoare (fun s => (project rename s) 0 * 3 = 12)
    (command rename (.assign 1 (.mul (.var 0) (.const 3))))
    (fun t => (project rename t) 1 = 12) := by
  have h := valid_to_hoare rename_injective
    (Cslib.IMP.Valid.assign (fun t => t 1 = 12) 1
      (.mul (.var 0) (.const 3)))
  simpa [Cslib.IMP.Assertion.subst, Cslib.IMP.AExp.eval] using h

#print axioms arith
#print axioms boolean
#print axioms command
#print axioms eval_arith
#print axioms eval_boolean
#print axioms project_update
#print axioms lift_execution
#print axioms reflect_execution
#print axioms execution_iff
#print axioms unmapped_preserved
#print axioms valid_to_hoare
#print axioms rename_injective
