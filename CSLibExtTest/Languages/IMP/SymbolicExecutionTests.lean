/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for bounded symbolic execution
-/
module

public import CSLibExt.Languages.IMP.SymbolicExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Cslib.IMP
open Cslib.IMP.Symbolic

private def prog1 : Cmd :=
  .assign 0 (.sub (.const 1) (.const 2))

private def prog2 : Cmd :=
  .seq (.assign 1 (.add (.var 0) (.const 1)))
    (.if_ (.le (.var 1) (.const 3))
      (.assign 2 (.mul (.var 1) (.const 2)))
      (.assign 2 (.const 0)))

private def prog3 : Cmd :=
  .while (.le (.const 1) (.var 0))
    (.assign 0 (.sub (.var 0) (.const 1)))

private def prog4 : Cmd :=
  .seq (.assign 3 (.const 2))
    (.while (.le (.const 1) (.var 3))
      (.seq (.assign 3 (.sub (.var 3) (.const 1)))
        (.seq (.assign 4 (.const 2))
          (.while (.le (.const 1) (.var 4))
            (.assign 4
              (.sub (.var 4) (.const 1)))))))

private def prog5a : Cmd :=
  .if_ (.eq (.mul (.var 0) (.var 0)) (.const 4))
    (.assign 1 (.const 1))
    (.assign 1 (.const 2))

private def prog5b : Cmd :=
  .if_ (.le (.const 1) (.const 0))
    (.assign 1 (.const 1))
    (.assign 1 (.const 2))

private def prog5c : Cmd :=
  .if_ (.eq (.mul (.var 0) (.var 0)) (.const 2))
    (.assign 1 (.const 1))
    (.assign 1 (.const 2))

private def bridgeTable : ConstTable :=
  fun x => match x with
  | 0 => some 3
  | _ => none

private def s2 : State := fun _ => 2
private def s3 : State := fun _ => 3
private def s4 : State := fun _ => 4
private def s0 : State := fun _ => 0

private theorem t1_a :
    (paths 0 prog1).length = 1 ∧
    ((paths 0 prog1).get? 0).map Path.guard =
      some (.truth true) ∧
    ((paths 0 prog1).get? 0).map
      (fun q => q.store 0) = some (.const 0) ∧
    ((paths 0 prog1).get? 0).map Path.cost =
      some 0 ∧
    (cutoffs 0 prog1).length = 0 := by
  decide

private theorem t1_b :
    (∀ sg s, (AExp.subst sg
        (.sub (.const 1) (.const 2))).eval s = 0) ∧
    (∀ sg s, (BExp.subst sg
        (.le (.const 1) (.const 2))).eval s = true) ∧
    (∀ s, Store.eval Store.init s = s) ∧
    (∀ sg x e s, Store.eval (Function.update sg x e) s =
      Function.update (Store.eval sg s) x (e.eval s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sg s
    have h := AExp.eval_subst sg _ s
    simp at h ⊢
    exact h
  · intro sg s
    have h := BExp.eval_subst sg _ s
    simp at h ⊢
    exact h
  · intro s
    exact Store.eval_init s
  · intro sg x e s
    exact Store.eval_update sg x e s

private theorem t1_c :
    (∀ s, ∃ f, BigStepCost prog1 s f 0 ∧
      f = Function.update s 0 0) ∧
    (∀ s q, q ∈ paths 0 prog1 →
      q.guard.eval s = true →
      BigStepCost prog1 s (Store.eval q.store s)
        q.cost) := by
  refine ⟨?_, ?_⟩
  · intro s
    refine ⟨_, BigStepCost.assign 0 _ s, ?_⟩
    simp [prog1]
  · intro s q hmem hguard
    have h := paths_sound 0 prog1 q s hmem hguard
    exact h.1

private theorem t2_a :
    (paths 0 prog2).length = 2 ∧
    ((paths 0 prog2).get? 0).map Path.guard =
      some (.and (.truth true)
        (.le (.add (.var 0) (.const 1)) (.const 3))) ∧
    ((paths 0 prog2).get? 1).map Path.guard =
      some (.and (.truth true)
        (.not (.le (.add (.var 0) (.const 1))
          (.const 3)))) ∧
    ((paths 0 prog2).get? 0).map
      (fun q => q.store 1) =
      some (.add (.var 0) (.const 1)) ∧
    ((paths 0 prog2).get? 1).map
      (fun q => q.store 1) =
      some (.add (.var 0) (.const 1)) ∧
    ((paths 0 prog2).get? 0).map
      (fun q => q.store 2) =
      some (.mul (.add (.var 0) (.const 1))
        (.const 2)) ∧
    ((paths 0 prog2).get? 1).map
      (fun q => q.store 2) = some (.const 0) ∧
    ((paths 0 prog2).get? 0).map Path.cost =
      some 0 ∧
    ((paths 0 prog2).get? 1).map Path.cost =
      some 0 ∧
    (cutoffs 0 prog2).length = 0 := by
  decide

private theorem t2_b :
    ∀ s, ∃ q, (Leaf.done q ∈ leaves 0 prog2 ∨
      Leaf.cut q ∈ leaves 0 prog2) ∧
      q.guard.eval s = true := by
  intro s
  exact leaves_cover 0 prog2 s

private theorem t2_c :
    (((paths 0 prog2).get? 0).map
        (fun q => q.guard.eval s2) = some true ∧
      ((paths 0 prog2).get? 0).map
        (fun q => (q.store 2).eval s2) = some 6 ∧
      ((paths 0 prog2).get? 1).map
        (fun q => q.guard.eval s3) = some true ∧
      ((paths 0 prog2).get? 1).map
        (fun q => (q.store 2).eval s3) = some 0) ∧
    (∀ q s, q ∈ paths 0 prog2 →
      q.guard.eval s = true →
      ∃ n, BigStepCost prog2 s
        (Store.eval q.store s) n) := by
  refine ⟨by decide, ?_⟩
  intro q s hmem hguard
  have h := paths_sound 0 prog2 q s hmem hguard
  exact ⟨_, h.1⟩

private theorem t3_a :
    (leaves 3 prog3).length = 5 ∧
    (((leaves 3 prog3).get? 0 >>= Leaf.done?).map
      Path.cost = some 0) ∧
    (((leaves 3 prog3).get? 1 >>= Leaf.done?).map
      Path.cost = some 1) ∧
    (((leaves 3 prog3).get? 2 >>= Leaf.done?).map
      Path.cost = some 2) ∧
    (((leaves 3 prog3).get? 3 >>= Leaf.done?).map
      Path.cost = some 3) ∧
    (((leaves 3 prog3).get? 4 >>= Leaf.cut?).map
      Path.cost = some 3) := by
  decide

private theorem t3_a_cut :
    ∀ q ∈ cutoffs 3 prog3, q.cost = 3 := by
  intro q hq
  exact cutoffs_cost 3 prog3 q hq

private theorem t3_b :
    ((((paths 3 prog3).get? 3).map
        (fun q => q.guard.eval s3) = some true) ∧
      (((paths 3 prog3).get? 3).map
        (fun q => (q.store 0).eval s3) = some 0)) ∧
    (∀ q s, q ∈ paths 3 prog3 →
      q.guard.eval s = true →
      ∃ n, BigStepCost prog3 s
        (Store.eval q.store s) n) := by
  refine ⟨by decide, ?_⟩
  intro q s hmem hguard
  have h := paths_sound 3 prog3 q s hmem hguard
  exact ⟨_, h.1⟩

private theorem t3_c :
    ((((paths 3 prog3).get? 0).map
        (fun q => q.guard.eval s4) = some false) ∧
      (((paths 3 prog3).get? 1).map
        (fun q => q.guard.eval s4) = some false) ∧
      (((paths 3 prog3).get? 2).map
        (fun q => q.guard.eval s4) = some false) ∧
      (((paths 3 prog3).get? 3).map
        (fun q => q.guard.eval s4) = some false) ∧
      (((cutoffs 3 prog3).get? 0).map
        (fun q => q.guard.eval s4) = some true)) ∧
    (∃ f, BigStepCost prog3 s4 f 4 ∧
      BigStep prog3 s4 f ∧ 3 < 4) := by
  refine ⟨by decide, ?_⟩
  · have g4 : (.le (.const 1) (.var 0)).eval s4
        = true := by decide
    have hcost : BigStepCost prog3 s4
        (Function.update s4 0 0) 4 := by
      let s3 := Function.update s4 0 3
      let s2 := Function.update s3 0 2
      let s1 := Function.update s2 0 1
      let s0 := Function.update s1 0 0
      have g3 : (.le (.const 1) (.var 0)).eval s3
          = true := by simp [s3, s4]
      have g2 : (.le (.const 1) (.var 0)).eval s2
          = true := by simp [s2, s3, s4]
      have g1 : (.le (.const 1) (.var 0)).eval s1
          = true := by simp [s1, s2, s3, s4]
      have g0 : (.le (.const 1) (.var 0)).eval s0
          = false := by simp [s0, s1, s2, s3, s4]
      have b4 := BigStepCost.assign 0
        (.sub (.var 0) (.const 1)) s4
      have b3 := BigStepCost.assign 0
        (.sub (.var 0) (.const 1)) s3
      have b2 := BigStepCost.assign 0
        (.sub (.var 0) (.const 1)) s2
      have b1 := BigStepCost.assign 0
        (.sub (.var 0) (.const 1)) s1
      have e3 : (Function.update s4 0
          ((.sub (.var 0) (.const 1)).eval s4)) = s3 := by
        simp [s3, s4]
      have e2 : (Function.update s3 0
          ((.sub (.var 0) (.const 1)).eval s3)) = s2 := by
        simp [s2, s3, s4]
      have e1 : (Function.update s2 0
          ((.sub (.var 0) (.const 1)).eval s2)) = s1 := by
        simp [s1, s2, s3, s4]
      have e0 : (Function.update s1 0
          ((.sub (.var 0) (.const 1)).eval s1)) = s0 := by
        simp [s0, s1, s2, s3, s4]
      rw [e3] at b4
      rw [e2] at b3
      rw [e1] at b2
      rw [e0] at b1
      have w0 := BigStepCost.while_false (g := _) g0
      have w1 := BigStepCost.while_true (g := _) g1 b1 w0
      have w2 := BigStepCost.while_true (g := _) g2 b2 w1
      have w3 := BigStepCost.while_true (g := _) g3 b3 w2
      have w4 := BigStepCost.while_true (g := _) g4 b4 w3
      have ef : s0 = Function.update s4 0 0 := by
        simp [s0, s1, s2, s3, s4]
      rw [ef] at w0 w1 w2 w3 w4
      simpa [prog3] using w4
    have hbig : BigStep prog3 s4 _ :=
      (bigStepCost_erase prog3 s4 _).mp ⟨4, hcost⟩
    have hno : ∀ q ∈ paths 3 prog3,
        q.guard.eval s4 = false := by
      intro q hmem
      have hlen : (paths 3 prog3).length = 4 := by decide
      have h0 : ((paths 3 prog3).get? 0).map
          (fun r => r.guard.eval s4) = some false := by
        decide
      have h1 : ((paths 3 prog3).get? 1).map
          (fun r => r.guard.eval s4) = some false := by
        decide
      have h2 : ((paths 3 prog3).get? 2).map
          (fun r => r.guard.eval s4) = some false := by
        decide
      have h3 : ((paths 3 prog3).get? 3).map
          (fun r => r.guard.eval s4) = some false := by
        decide
      simp [paths, prog3] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | _
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa …
### Outer final report
Step 1 — goal is authoring two frozen Lean modules for bounded symbolic execution with no fbsource edits, returning complete files first. Starting Step 2 context gathering.FILE:CSLibExt/Languages/IMP/SymbolicExecution.lean
