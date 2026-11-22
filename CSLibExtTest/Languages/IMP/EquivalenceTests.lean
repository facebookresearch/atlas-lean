/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.Equivalence

@[expose] public section

namespace Cslib.IMP.EquivalenceTests

def increment (name : Nat) : Cmd :=
  .assign name (.add (.var name) (.const 1))

def setThenIncrement : Cmd :=
  .seq (.assign 0 (.const 4)) (increment 0)

def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

example {s : State} (h : s 0 = 2) :
    ∃ s', Terminates countdown s s' ∧ s' 0 = 0 := by
  refine ⟨Function.update
      (Function.update s 0 ((AExp.sub (.var 0) (.const 1)).eval s)) 0
      ((AExp.sub (.var 0) (.const 1)).eval
        (Function.update s 0 ((AExp.sub (.var 0) (.const 1)).eval s))),
    terminates_iff_bigStep.mpr ?_, ?_⟩
  · show BigStep (.while (.not (.eq (.var 0) (.const 0)))
        (.assign 0 (.sub (.var 0) (.const 1)))) s _
    refine .whileTrue ?_ (.assign _ _ _) ?_
    · simp [BExp.eval, AExp.eval, h]
    · refine .whileTrue ?_ (.assign _ _ _) ?_
      · simp [BExp.eval, AExp.eval, Function.update, h]
      · refine .whileFalse ?_
        simp [BExp.eval, AExp.eval, Function.update, h]
  · simp [AExp.eval, Function.update, h]

example : ∃ s', BigStep setThenIncrement (fun _ => 0) s' ∧ s' 0 = 5 := by
  have hterm := Terminates.seq (Terminates.assign (fun _ => 0) 0 (.const 4))
    (Terminates.assign _ 0 (.add (.var 0) (.const 1)))
  exact ⟨_, terminates_iff_bigStep.mp hterm, by simp [AExp.eval]⟩

example {s s1 s2 : State} (h1 : Terminates setThenIncrement s s1)
    (h2 : BigStep setThenIncrement s s2) : s1 = s2 :=
  Terminates.deterministic h1 (Terminates.of_bigStep h2)

def factorial : Cmd :=
  .seq (.assign 1 (.const 1))
    (.while (.not (.eq (.var 0) (.const 0)))
      (.seq (.assign 1 (.mul (.var 1) (.var 0)))
        (.assign 0 (.sub (.var 0) (.const 1)))))

example {s : State} (h : s 0 = 3) :
    ∃ s', Terminates factorial s s' ∧ s' 1 = 6 := by
  refine ⟨?w, ?hterm, ?hval⟩
  case hterm =>
    apply terminates_iff_bigStep.mpr
    show BigStep (.seq (.assign 1 (.const 1))
          (.while (.not (.eq (.var 0) (.const 0)))
            (.seq (.assign 1 (.mul (.var 1) (.var 0)))
              (.assign 0 (.sub (.var 0) (.const 1)))))) s _
    refine .seq (.assign _ _ _) ?_
    refine .whileTrue ?_ (.seq (.assign _ _ _) (.assign _ _ _)) ?_
    · simp [BExp.eval, AExp.eval, Function.update, h]
    · refine .whileTrue ?_ (.seq (.assign _ _ _) (.assign _ _ _)) ?_
      · simp [BExp.eval, AExp.eval, Function.update, h]
      · refine .whileTrue ?_ (.seq (.assign _ _ _) (.assign _ _ _)) ?_
        · simp [BExp.eval, AExp.eval, Function.update, h]
        · refine .whileFalse ?_
          simp [BExp.eval, AExp.eval, Function.update, h]
  case hval =>
    simp [AExp.eval, Function.update, h]

#print axioms Cslib.IMP.terminates_iff_bigStep

end Cslib.IMP.EquivalenceTests
