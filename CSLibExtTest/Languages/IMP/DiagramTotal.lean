/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Languages.IMP.DiagramTotal

open CategoryTheory Cslib Cslib.IMP Cslib.IMP.DiagramCompiler
namespace Cslib.IMP.DiagramTotalTests
example (c : Cmd) (Q : Assertion) (s : State) :
    (∃ t, (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ∧ Q t) ↔
      wp c Q s := compiled_wp_iff c Q s

example (c : Cmd) (P Q : Assertion) :
    (∀ s, P s → ∃ t,
      (s, t) ∈ ((compile c).denote interpret SumRelCat.symmetricTrace).rel ∧ Q t) ↔
      TDerivable P c Q := compiled_tderivable_iff c P Q

example (b : BExp) (c : Cmd) (Q : Assertion) (s : State) :
    (∃ t, (s, t) ∈ ((compile (.while b c)).denote interpret
      SumRelCat.symmetricTrace).rel ∧ Q t) ↔ s ∈ (wp.whileStep b c Q).lfp :=
  compiled_while_iff_lfp b c Q s

-- The same repeated-subtraction fixture as the partial VCG tests, now with termination.
private def divide (d n : Nat) : ACmd :=
  .while (fun s => s 0 + s 1 * d = n) (.le (.const d) (.var 0))
    (.seq (.assign 0 (.sub (.var 0) (.const d))) (.assign 1 (.add (.var 1) (.const 1))))

private def answer (d n : Nat) : Assertion := fun s => s 0 = n % d ∧ s 1 = n / d

private theorem answer_of_bounds (d n : Nat) (s : State)
    (heq : s 0 + s 1 * d = n) (hlt : s 0 < d) : answer d n s := by
  have hd : 0 < d := by omega
  constructor
  · rw [← heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  · rw [← heq, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hlt, Nat.zero_add]

private theorem divide_vc (d n : Nat) : (divide d n).vc (answer d n) := by
  refine ⟨?_, ?_, trivial, trivial⟩
  · intro s hs hg
    have hle : d ≤ s 0 := BExp.eval_le_eq_true.mp hg
    simp [ACmd.pre, Assertion.subst, AExp.eval, Function.update]
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_right_comm,
      Nat.sub_add_cancel hle]
    exact hs
  · intro s hs hg
    apply answer_of_bounds d n s hs
    have hn : ¬ d ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const d) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hle
      rw [hg] at ht
      contradiction
    omega

private theorem divide_entry (d n : Nat) :
    Assertion.Entails (fun s => s 0 = n ∧ s 1 = 0) ((divide d n).pre (answer d n)) := by
  intro s hs
  change s 0 + s 1 * d = n
  simp [hs.1, hs.2]

-- A decreasing remainder proves termination; an unrelated variable is carried unchanged.
private theorem divide_total (d n k : Nat) (hd : 0 < d) :
    TValid (fun s => s 0 = n ∧ s 1 = 0 ∧ s 3 = k) (divide d n).strip
      (fun s => answer d n s ∧ s 3 = k) := by
  apply TValid.consequence (pre' := fun s => s 0 + s 1 * d = n ∧ s 3 = k)
    (post' := fun s => (s 0 + s 1 * d = n ∧ s 3 = k) ∧
      (BExp.le (.const d) (.var 0)).eval s = false) ?_
    (TValid.whileVariant (variant := fun s => s 0) ?_) ?_
  · intro s hs
    exact ⟨by simp [hs.1, hs.2.1], hs.2.2⟩
  · intro s hs hb
    have hle : d ≤ s 0 := BExp.eval_le_eq_true.mp hb
    let m := Function.update s 0 (s 0 - d)
    let t := Function.update m 1 (m 1 + 1)
    refine ⟨t, .seq (.assign s 0 _) (.assign m 1 _), ⟨?_, ?_⟩, ?_⟩
    · simp [t, m, Function.update]
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_right_comm,
        Nat.sub_add_cancel hle]
      exact hs.1
    · simpa [t, m, Function.update] using hs.2
    · simp [t, m, Function.update]
      omega
  · intro s hs
    refine ⟨answer_of_bounds d n s hs.1.1 ?_, hs.1.2⟩
    have hn : ¬ d ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const d) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hle
      rw [hs.2] at ht
      contradiction
    omega

-- The supplied annotation produces the partial proof; the variant supplies termination.
example (d n : Nat) (hd : 0 < d) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s : State | s 0 = n ∧ s 1 = 0} (compile (divide d n).strip) {s | answer d n s} ∧
    (∀ s, s 0 = n ∧ s 1 = 0 → ∃ t,
      (s, t) ∈ ((compile (divide d n).strip).denote interpret SumRelCat.symmetricTrace).rel ∧
        answer d n t) := by
  apply annotated_total (divide d n) _ _ (divide_entry d n) (divide_vc d n)
  intro s hs
  obtain ⟨t, ht, _⟩ := divide_total d n (s 3) hd (s := s) ⟨hs.1, hs.2, rfl⟩
  exact ⟨t, ht⟩

example (d n k : Nat) (hd : 0 < d) (s : State)
    (hs : s 0 = n ∧ s 1 = 0 ∧ s 3 = k) :
    ∃ t, (s, t) ∈ ((compile (divide d n).strip).denote interpret
      SumRelCat.symmetricTrace).rel ∧ t 0 = n % d ∧ t 1 = n / d ∧ t 3 = k := by
  obtain ⟨t, ht, ha, hk⟩ := divide_total d n k hd hs
  exact ⟨t, (execution_iff _ _ _).mpr ht, ha.1, ha.2, hk⟩

private def initial (n k : Nat) : State := fun x => if x = 0 then n else if x = 3 then k else 0

-- Multiple iterations and exact arithmetic results, including preservation of variable 3.
example : ∃ t, (initial 17 9, t) ∈ ((compile (divide 5 17).strip).denote
    interpret SumRelCat.symmetricTrace).rel ∧ t 0 = 2 ∧ t 1 = 3 ∧ t 3 = 9 := by
  obtain ⟨t, ht, ha, hk⟩ := divide_total 5 17 9 (by decide) (s := initial 17 9)
    ⟨by decide, by decide, by decide⟩
  exact ⟨t, (execution_iff _ _ _).mpr ht, ha.1, ha.2, hk⟩

example : ∃ t, BigStep (divide 5 2).strip (initial 2 9) t ∧ answer 5 2 t := by
  obtain ⟨t, ht, ha, _⟩ := divide_total 5 2 9 (by decide) (s := initial 2 9)
    ⟨by decide, by decide, by decide⟩
  exact ⟨t, ht, ha⟩

example : ¬ ∃ t, (initial 17 9, t) ∈ ((compile (divide 5 17).strip).denote
    interpret SumRelCat.symmetricTrace).rel ∧ t 0 = 1 := by
  rintro ⟨t, ht, hbad⟩
  have h := (divide_total 5 17 9 (by decide)).valid
    (initial := initial 17 9) ⟨by decide, by decide, by decide⟩ ((execution_iff _ _ _).mp ht)
  have hr : t 0 = 2 := h.1.1
  omega

-- Divisor zero still has a valid partial certificate.
example (n : Nat) : (annotate (divide 0 n) (answer 0 n)).vc interpret
    {s | s 0 = n ∧ s 1 = 0} {s | answer 0 n s} :=
  (vc_annotate_iff _ _ _).mpr ⟨divide_entry 0 n, divide_vc 0 n⟩

private theorem zero_divisor_no_run (n : Nat) (s t : State) :
    ¬ BigStep (divide 0 n).strip s t := by
  intro h
  obtain ⟨j, hj⟩ := Iterates.exists_of_bigStep h
  clear h
  induction hj with
  | @exit s hb =>
    have ht : (BExp.le (.const 0) (.var 0)).eval s = true :=
      BExp.eval_le_eq_true.mpr (Nat.zero_le _)
    rw [hb] at ht
    contradiction
  | step _ _ _ ih => exact ih

example (n : Nat) : ¬ ∃ t, (initial n 9, t) ∈
    ((compile (divide 0 n).strip).denote interpret SumRelCat.symmetricTrace).rel := by
  rintro ⟨t, ht⟩
  exact zero_divisor_no_run n _ _ ((execution_iff _ _ _).mp ht)

example (n : Nat) : ¬ TValid (fun s => s = initial n 9) (divide 0 n).strip (answer 0 n) := by
  intro h
  obtain ⟨t, ht, _⟩ := h (s := initial n 9) rfl
  exact zero_divisor_no_run n _ _ ht

#print axioms compiled_tvalid_iff
#print axioms compiled_while_iff_lfp
#print axioms annotated_total
end Cslib.IMP.DiagramTotalTests
