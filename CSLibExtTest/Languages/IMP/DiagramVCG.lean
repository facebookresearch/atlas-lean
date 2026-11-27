/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Languages.IMP.DiagramVCG

/-!
# Worked compiled verification conditions

Swap, division by repeated subtraction and nested loops use the existing IMP
generator. The tests check the compiled obligations, explicit diagram derivations
and actual executions, as well as false initial assertions, invariants and exits.
All statements are partial correctness; zero divisors and endless loops are not
silently given termination proofs.
-/

open CategoryTheory Cslib Cslib.IMP Cslib.IMP.DiagramCompiler
open scoped MonoidalCategory

namespace Cslib.IMP.DiagramVCGTests

example (c : ACmd) (P Q : Assertion) :
    (annotate c Q).vc interpret {s | P s} {s | Q s} ↔ P.Entails (c.pre Q) ∧ c.vc Q :=
  vc_annotate_iff c P Q

example (c : ACmd) (P Q : Assertion) (hP : P.Entails (c.pre Q)) (hvc : c.vc Q) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s | P s} (compile c.strip) {s | Q s} := annotated_derivable c P Q hP hvc

example {P Q : Assertion} {c : Cmd} (h : IMP.Derivable P c Q) :
    ∃ a : ACmd, a.strip = c ∧ (annotate a Q).vc interpret {s | P s} {s | Q s} :=
  exists_compiled_annotation h

-- The annotation index is exactly the existing compiler's result.
example (I : Assertion) (b : BExp) (c : ACmd) (Q : Assertion) :
    TracedHoare.Annotation PowersetVerification.verification (compile (.while b c.strip)) :=
  annotate (.while I b c) Q

private def swap : ACmd :=
  .seq (.assign 2 (.var 0)) (.seq (.assign 0 (.var 1)) (.assign 1 (.var 2)))

private theorem swap_conditions (a b : Nat) :
    (annotate swap (fun s => s 0 = b ∧ s 1 = a)).vc interpret
      {s : State | s 0 = a ∧ s 1 = b} {s | s 0 = b ∧ s 1 = a} := by
  apply (vc_annotate_iff _ _ _).mpr
  refine ⟨?_, by trivial⟩
  intro s hs
  simpa [swap, ACmd.pre, Assertion.subst, AExp.eval, Function.update] using hs.symm

example (a b : Nat) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s : State | s 0 = a ∧ s 1 = b} (compile swap.strip) {s | s 0 = b ∧ s 1 = a} :=
  (annotate swap _).vc_sound (swap_conditions a b)

-- Assignment updates are checked on arbitrary states, including unaffected variables.
example (s : State) : ∃ t, (s, t) ∈
    ((compile swap.strip).denote interpret SumRelCat.symmetricTrace).rel ∧
    t 0 = s 1 ∧ t 1 = s 0 ∧ t 3 = s 3 := by
  let u := Function.update s 2 (s 0)
  let v := Function.update u 0 (u 1)
  let t := Function.update v 1 (v 2)
  refine ⟨t, (execution_iff _ _ _).mpr (.seq (.assign s 2 _)
    (.seq (.assign u 0 _) (.assign v 1 _))), ?_, ?_, ?_⟩ <;>
    simp [t, v, u, Function.update]

private def divide (d n : Nat) : ACmd :=
  .while (fun s => s 0 + s 1 * d = n) (.le (.const d) (.var 0))
    (.seq (.assign 0 (.sub (.var 0) (.const d))) (.assign 1 (.add (.var 1) (.const 1))))

private theorem divide_vc (d n : Nat) :
    (divide d n).vc (fun s => s 0 + s 1 * d = n ∧ s 0 < d) := by
  refine ⟨?_, ?_, trivial, trivial⟩
  · intro s hs hg
    have hle : d ≤ s 0 := BExp.eval_le_eq_true.mp hg
    simp [ACmd.pre, Assertion.subst, AExp.eval, Function.update]
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_right_comm,
      Nat.sub_add_cancel hle]
    exact hs
  · intro s hs hg
    refine ⟨hs, ?_⟩
    have hn : ¬ d ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const d) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hle
      rw [hg] at ht
      contradiction
    omega

example (d n : Nat) :
    (annotate (divide d n) (fun s => s 0 + s 1 * d = n ∧ s 0 < d)).vc interpret
      {s : State | s 0 = n ∧ s 1 = 0} {s | s 0 + s 1 * d = n ∧ s 0 < d} := by
  apply (vc_annotate_iff _ _ _).mpr
  refine ⟨?_, divide_vc d n⟩
  intro s hs
  change s 0 + s 1 * d = n
  simp [hs.1, hs.2]

example (d n : Nat) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s : State | s 0 + s 1 * d = n} (compile (divide d n).strip)
      {s | s 0 + s 1 * d = n ∧ s 0 < d} :=
  annotated_derivable _ _ _ (Assertion.entails_refl _) (divide_vc d n)

private def initial (r q : Nat) : State := fun k => if k = 0 then r else if k = 1 then q else 0

example : (initial 2 0, initial 2 0) ∈
    ((compile (divide 5 2).strip).denote interpret SumRelCat.symmetricTrace).rel :=
  (execution_iff _ _ _).mpr (.whileFalse (by decide))

example : ∃ t, (initial 7 0, t) ∈
    ((compile (divide 5 7).strip).denote interpret SumRelCat.symmetricTrace).rel ∧
    t 0 = 2 ∧ t 1 = 1 := by
  let m := Function.update (initial 7 0) 0 2
  let t := Function.update m 1 1
  refine ⟨t, (execution_iff _ _ _).mpr ?_, by decide, by decide⟩
  exact .whileTrue (by decide) (.seq (.assign (initial 7 0) 0 _) (.assign m 1 _))
    (.whileFalse (by decide))

-- The arithmetic certificate itself assumes no positive divisor or termination.
example : (divide 0 7).vc (fun s => s 0 + s 1 * 0 = 7 ∧ s 0 < 0) := divide_vc 0 7

private def outerInvariant : Assertion := fun s => s 0 = 1 ∨ (s 0 = 0 ∧ s 1 = 0)

private def nested : ACmd := .while outerInvariant (.le (.const 1) (.var 0))
  (.seq (.while (fun s => s 0 = 1) (.le (.const 1) (.var 1)) (.assign 1 (.const 0)))
    (.assign 0 (.const 0)))

private theorem nested_vc : nested.vc (fun s => s 0 = 0 ∧ s 1 = 0) := by
  refine ⟨?_, ?_, ⟨?_, ?_, trivial⟩, trivial⟩
  · intro s hs hg
    have hle : 1 ≤ s 0 := BExp.eval_le_eq_true.mp hg
    change s 0 = 1
    rcases hs with hs | ⟨hs, _⟩ <;> omega
  · intro s hs hg
    have hn : ¬ 1 ≤ s 0 := of_decide_eq_false hg
    rcases hs with hs | hs
    · omega
    · exact hs
  · intro s hs _
    simpa [ACmd.pre, Assertion.subst, AExp.eval, Function.update] using hs
  · intro s _ hg
    have hn : ¬ 1 ≤ s 1 := of_decide_eq_false hg
    simp [ACmd.pre, Assertion.subst, AExp.eval, Function.update, outerInvariant]
    omega

example : (annotate nested (fun s => s 0 = 0 ∧ s 1 = 0)).vc interpret
    {s : State | s 0 = 1} {s | s 0 = 0 ∧ s 1 = 0} :=
  (vc_annotate_iff _ _ _).mpr ⟨fun _ h => Or.inl h, nested_vc⟩

example : ∃ t, (initial 1 3, t) ∈
    ((compile nested.strip).denote interpret SumRelCat.symmetricTrace).rel ∧
    t 0 = 0 ∧ t 1 = 0 := by
  let m := Function.update (initial 1 3) 1 0
  let t := Function.update m 0 0
  refine ⟨t, (execution_iff _ _ _).mpr ?_, by decide, by decide⟩
  exact .whileTrue (by decide)
    (.seq (.whileTrue (by decide) (.assign (initial 1 3) 1 _) (.whileFalse (by decide)))
      (.assign m 0 _)) (.whileFalse (by decide))

-- Both branches are annotated even when a constant guard makes one unreachable.
example : (annotate (.ite (.truth false) (.assign 0 (.const 7)) (.assign 0 (.const 9)))
    (fun s => s 0 = 9)).vc interpret Set.univ {s | s 0 = 9} := by
  apply (vc_annotate_iff _ _ _).mpr
  refine ⟨?_, trivial, trivial⟩
  intro s _
  simp [ACmd.pre, BExp.eval, Assertion.subst, AExp.eval, Function.update]

private def badInvariant : ACmd :=
  .while (fun s => s 0 = 0) (.le (.var 0) (.const 2)) (.assign 0 (.add (.var 0) (.const 1)))

-- The precondition satisfies the invariant, but the first body step destroys it.
example : ¬ (annotate badInvariant (fun s => s 0 = 3)).vc interpret
    {s : State | s 0 = 0} {s | s 0 = 3} := by
  intro h
  have hb := ((vc_annotate_iff _ _ _).mp h).2.1 (fun _ => 0) rfl (by decide)
  simp [ACmd.pre, Assertion.subst, AExp.eval, Function.update] at hb

-- A valid body cannot compensate for a false loop-exit obligation.
example : ¬ (annotate (.while (fun _ => True) (.truth false) .skip) (fun _ => False)).vc
    interpret Set.univ ∅ := by
  intro h
  exact ((vc_annotate_iff _ _ _).mp h).2.2.1 (fun _ => 0) trivial rfl

-- A vacuous invariant fails the initial-entry condition from a nonempty input.
example : ¬ (annotate (.while (fun _ => False) (.truth false) .skip) (fun _ => True)).vc
    interpret Set.univ Set.univ := by
  intro h
  exact ((vc_annotate_iff _ _ _).mp h).1 (state := fun _ => 0) trivial

-- Divergent partial correctness stays available without implying total correctness.
example : (annotate (.while (fun _ => True) (.truth true) .skip) (fun _ => False)).vc
    interpret Set.univ ∅ := by
  apply (vc_annotate_iff _ _ _).mpr
  refine ⟨fun _ _ => trivial, fun _ _ _ => trivial, ?_, trivial⟩
  intro s _ h
  simp [BExp.eval] at h

#print axioms vc_annotate_iff
#print axioms annotated_derivable
#print axioms exists_compiled_annotation

end Cslib.IMP.DiagramVCGTests
