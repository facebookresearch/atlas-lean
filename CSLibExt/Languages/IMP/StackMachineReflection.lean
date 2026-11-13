/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.StackMachine
public import CSLibExt.Languages.IMP.Hoare
public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Termination reflection and reachable progress for the IMP compiler

Every reachable configuration of the actual compiled program either is a halted
source execution with the original stack, or is strictly before the halt address
and has a machine successor. Halting reflects a source big-step execution, with
the same final state and stack. Infinite execution and costs are not asserted.

For embedded code, reflection requires that step sources stay in the segment.
Unrestricted surrounding code can leave and reenter it. The private proof therefore
extracts a source execution *and a residual run*, or proves that the current
configuration has a successor before the segment end. Known expression runs are
reused, not reproved; deterministic prefix cancellation supplies the decreasing
measure for loops. The original reflection theorem is a corollary of this one
command induction.
-/

@[expose] public section

namespace Cslib.IMP.StackMachine

open Relation

/-- A machine step whose source program counter is in the half-open segment `[lo, hi)`. -/
def SegStep (prog : List Instr) (lo hi : Nat) (x y : Config) : Prop :=
  Step prog x y ∧ lo ≤ x.1 ∧ x.1 < hi

/-- Forgetting the segment restriction gives an ordinary machine step. -/
theorem SegStep.step {prog : List Instr} {lo hi : Nat} {x y : Config}
    (h : SegStep prog lo hi x y) : Step prog x y := h.1

private theorem step_of_fetch_eq {p q : List Instr} {x y : Config}
    (heq : p[x.1]? = q[x.1]?) (h : Step p x y) : Step q x y := by
  cases h with
  | push hf => exact .push (heq.symm.trans hf)
  | load hf => exact .load (heq.symm.trans hf)
  | store hf => exact .store (heq.symm.trans hf)
  | add hf => exact .add (heq.symm.trans hf)
  | sub hf => exact .sub (heq.symm.trans hf)
  | mul hf => exact .mul (heq.symm.trans hf)
  | eqI hf => exact .eqI (heq.symm.trans hf)
  | leI hf => exact .leI (heq.symm.trans hf)
  | notI hf => exact .notI (heq.symm.trans hf)
  | andI hf => exact .andI (heq.symm.trans hf)
  | jump hf => exact .jump (heq.symm.trans hf)
  | jumpIfZeroZero hf => exact .jumpIfZeroZero (heq.symm.trans hf)
  | jumpIfZeroSucc hf => exact .jumpIfZeroSucc (heq.symm.trans hf)

private theorem step_pc_lt {p : List Instr} {x y : Config} (h : Step p x y) :
    x.1 < p.length := by
  by_contra hn
  exact no_step_of_length_le (Nat.le_of_not_gt hn) y h

private theorem step_append {p q : List Instr} {x y : Config}
    (h : Step p x y) : Step (p ++ q) x y :=
  step_of_fetch_eq (List.getElem?_append_left (step_pc_lt h)).symm h

-- Cancel a known prefix against the observed run. If the observed run ends
-- earlier, its endpoint has the next step of the known run, rather than being stuck.
private theorem cancel_or_step {p prog : List Instr} {r : Config → Config → Prop}
    (hsub : ∀ ⦃x y⦄, r x y → Step prog x y)
    (hlift : ∀ ⦃x y⦄, Step p x y → Step prog x y)
    {x y z : Config} {n : Nat} (hknown : Steps p x y) (h : RelatesInSteps r x z n) :
    (∃ k ≤ n, RelatesInSteps r y z k) ∨ ∃ w, Step p z w := by
  induction hknown using ReflTransGen.head_induction_on generalizing n with
  | refl => exact Or.inl ⟨n, le_rfl, h⟩
  | @head x u hs _ ih =>
      cases n with
      | zero =>
          have heq := h.zero
          subst x
          exact Or.inr ⟨u, hs⟩
      | succ n =>
          obtain ⟨v, hv, hrest⟩ := h.succ'
          have heq := Step.deterministic (hlift hs) (hsub hv)
          subst v
          rcases ih hrest with ⟨k, hk, hout⟩ | hstep
          · exact Or.inl ⟨k, by omega, hout⟩
          · exact Or.inr hstep

private theorem cancel_prefix_or_step {p after prog : List Instr}
    {r : Config → Config → Prop} (hsub : ∀ ⦃x y⦄, r x y → Step prog x y)
    (hprog : prog = p ++ after) {x y z : Config} {n : Nat}
    (hknown : Steps p x y) (h : RelatesInSteps r x z n) :
    (∃ k ≤ n, RelatesInSteps r y z k) ∨ (z.1 < p.length ∧ ∃ w, Step prog z w) := by
  rcases cancel_or_step hsub (fun _ _ hs => hprog.symm ▸ step_append hs) hknown h with
    hr | ⟨w, hw⟩
  · exact Or.inl hr
  · exact Or.inr ⟨step_pc_lt hw, w, hprog.symm ▸ step_append hw⟩

private theorem consume_step {prog : List Instr} {r : Config → Config → Prop}
    (hsub : ∀ ⦃x y⦄, r x y → Step prog x y) {x y z : Config} {n : Nat}
    (hs : Step prog x y) (hne : x ≠ z) (h : RelatesInSteps r x z n) :
    ∃ k < n, RelatesInSteps r y z k := by
  cases n with
  | zero => exact (hne h.zero).elim
  | succ n =>
      obtain ⟨v, hv, hrest⟩ := h.succ'
      have heq := Step.deterministic hs (hsub hv)
      subst v
      exact ⟨n, by omega, hrest⟩

-- One generic local fetch helper replaces the private constructor-specific
-- family in StackMachine.lean. It uses the public embedded-segment API.
private theorem fetch_after {before after : List Instr} {op : Instr} {pc : Nat}
    (hlen : before.length = pc) : (before ++ [op] ++ after)[pc]? = some op := by
  subst pc
  exact fetch_segment (before := before) (seg := [op]) (after := after) (i := 0)
    (Nat.zero_lt_succ 0)

private theorem run_cases (c : Cmd) {prog : List Instr}
    {r : Config → Config → Prop} (hsub : ∀ ⦃x y⦄, r x y → Step prog x y)
    {n pc : Nat} {before after : List Instr} {stack : List Nat} {s : State} {z : Config}
    (hlen : before.length = pc) (hprog : prog = before ++ compile c pc ++ after)
    (h : RelatesInSteps r (pc, stack, s) z n) :
    (∃ s' k, k ≤ n ∧ BigStep c s s' ∧
      RelatesInSteps r (pc + codeLength c, stack, s') z k) ∨
    (z.1 < pc + codeLength c ∧ ∃ w, Step prog z w) := by
  induction c generalizing n pc before after stack s with
  | skip => exact Or.inl ⟨s, n, le_rfl, .skip s, by simpa [codeLength] using h⟩
  | assign name value =>
      have hf : Steps (before ++ compile (.assign name value) pc)
          (pc, stack, s)
          (pc + codeLength (.assign name value), stack,
            Function.update s name (value.eval s)) := by
        simpa [hlen] using
          (compile_runs (BigStep.assign s name value) (before := before) (after := [])
            (stack := stack))
      rcases cancel_prefix_or_step hsub hprog hf h with ⟨k, hk, hr⟩ | ⟨hlt, hs⟩
      · exact Or.inl ⟨_, k, hk, .assign s name value, hr⟩
      · exact Or.inr ⟨by simpa [List.length_append, compile_length, hlen] using hlt, hs⟩
  | seq first second ihFirst ihSecond =>
      rcases ihFirst hlen
        (show prog = before ++ compile first pc ++
          (compile second (pc + codeLength first) ++ after) by
          simpa [compile, List.append_assoc] using hprog) h with
        ⟨mid, k, hk, hb, hr⟩ | ⟨hlt, hs⟩
      · rcases ihSecond (before := before ++ compile first pc) (after := after)
          (by simp [List.length_append, compile_length, hlen])
          (by simpa [compile, List.append_assoc] using hprog) hr with
          ⟨fin, j, hj, hb', hr'⟩ | ⟨hlt, hs⟩
        · exact Or.inl ⟨fin, j, by omega, .seq hb hb', by
            simpa [codeLength, Nat.add_assoc] using hr'⟩
        · exact Or.inr ⟨by simpa [codeLength, Nat.add_assoc] using hlt, hs⟩
      · exact Or.inr ⟨by simp only [codeLength]; omega, hs⟩
  | ite b t e ihT ihE =>
      let thenPC := pc + blen b + 1
      let elsePC := thenPC + codeLength t + 1
      let endPC := elsePC + codeLength e
      let preT := before ++ compileB b ++ [Instr.jumpIfZero elsePC]
      let preE := preT ++ compile t thenPC ++ [Instr.jump endPC]
      have hlenT : preT.length = thenPC := by
        simp [preT, thenPC, List.length_append, compileB_length, hlen, Nat.add_assoc]
      have hlenE : preE.length = elsePC := by
        simp [preE, elsePC, List.length_append, compile_length, hlenT, Nat.add_assoc]
      have hcode : prog = preE ++ compile e elsePC ++ after := by
        simpa [preE, preT, thenPC, elsePC, endPC, compile, List.append_assoc] using hprog
      have hguard : prog = (before ++ compileB b) ++
          ([Instr.jumpIfZero elsePC] ++ compile t thenPC ++ [Instr.jump endPC] ++
            compile e elsePC ++ after) := by
        simpa [preE, preT, List.append_assoc] using hcode
      have hf : Steps (before ++ compileB b) (pc, stack, s)
          (pc + blen b, cond (b.eval s) 1 0 :: stack, s) := by
        simpa [hlen] using
          (compileB_runs (b := b) (before := before) (after := []) (stack := stack) (s := s))
      rcases cancel_prefix_or_step hsub hguard hf h with ⟨k, hk, hr⟩ | ⟨hlt, hs⟩
      · have hfetch : prog[pc + blen b]? = some (.jumpIfZero elsePC) := by
          rw [hguard]
          simpa [List.append_assoc] using
            (fetch_after (before := before ++ compileB b)
              (after := compile t thenPC ++ [Instr.jump endPC] ++ compile e elsePC ++ after)
              (op := .jumpIfZero elsePC) (by simp [List.length_append, compileB_length, hlen]))
        have hs : Step prog (pc + blen b, cond (b.eval s) 1 0 :: stack, s)
            (cond (b.eval s) thenPC elsePC, stack, s) := by
          cases hb : b.eval s
          · simpa [hb] using (Step.jumpIfZeroZero (stack := stack) (s := s) hfetch)
          · simpa [hb, thenPC] using
              (Step.jumpIfZeroSucc (n := 0) (stack := stack) (s := s) hfetch)
        by_cases hstop : (pc + blen b, cond (b.eval s) 1 0 :: stack, s) = z
        · right
          rw [← hstop]
          exact ⟨by dsimp; simp only [codeLength]; omega, _, hs⟩
        obtain ⟨j, hj, hr'⟩ := consume_step hsub hs hstop hr
        cases hb : b.eval s with
        | false =>
            rw [hb] at hr'
            rcases ihE hlenE hcode hr' with ⟨fin, l, hl, hbig, hout⟩ | ⟨hlt, hs⟩
            · exact Or.inl ⟨fin, l, by omega, .iteFalse hb hbig, by
                simpa [elsePC, thenPC, codeLength, Nat.add_assoc] using hout⟩
            · exact Or.inr ⟨by
                simpa [elsePC, thenPC, codeLength, Nat.add_assoc] using hlt, hs⟩
        | true =>
            rw [hb] at hr'
            rcases ihT hlenT (after := [Instr.jump endPC] ++ compile e elsePC ++ after)
              (by simpa [preE, List.append_assoc] using hcode) hr' with
              ⟨fin, l, hl, hbig, hout⟩ | ⟨hlt, hs⟩
            · have hjump : Step prog (thenPC + codeLength t, stack, fin)
                  (endPC, stack, fin) := by
                apply Step.jump
                rw [hcode]
                simpa [preE, List.append_assoc] using
                  (fetch_after (before := preT ++ compile t thenPC)
                    (after := compile e elsePC ++ after) (op := .jump endPC)
                    (by simp [List.length_append, compile_length, hlenT]))
              by_cases hstop : (thenPC + codeLength t, stack, fin) = z
              · right
                rw [← hstop]
                exact ⟨by dsimp [thenPC]; simp only [codeLength]; omega, _, hjump⟩
              obtain ⟨m, hm, hfinal⟩ := consume_step hsub hjump hstop hout
              exact Or.inl ⟨fin, m, by omega, .iteTrue hb hbig, by
                simpa [endPC, elsePC, thenPC, codeLength, Nat.add_assoc] using hfinal⟩
            · right
              refine ⟨?_, hs⟩
              dsimp [thenPC] at hlt
              simp only [codeLength]
              omega
      · right
        refine ⟨?_, hs⟩
        simp only [List.length_append, compileB_length, hlen] at hlt
        simp only [codeLength]
        omega
  | «while» b body ihBody =>
      induction n using Nat.strong_induction_on generalizing pc before after stack s with
      | h n ihLoop =>
          let bodyPC := pc + blen b + 1
          let endPC := bodyPC + codeLength body + 1
          let preBody := before ++ compileB b ++ [Instr.jumpIfZero endPC]
          have hlenBody : preBody.length = bodyPC := by
            simp [preBody, bodyPC, List.length_append, compileB_length, hlen, Nat.add_assoc]
          have hcode : prog = preBody ++ compile body bodyPC ++ [Instr.jump pc] ++ after := by
            simpa [preBody, bodyPC, endPC, compile, List.append_assoc] using hprog
          have hguard : prog = (before ++ compileB b) ++
              ([Instr.jumpIfZero endPC] ++ compile body bodyPC ++ [Instr.jump pc] ++ after) := by
            simpa [preBody, List.append_assoc] using hcode
          have hf : Steps (before ++ compileB b) (pc, stack, s)
              (pc + blen b, cond (b.eval s) 1 0 :: stack, s) := by
            simpa [hlen] using
              (compileB_runs (b := b) (before := before) (after := []) (stack := stack) (s := s))
          rcases cancel_prefix_or_step hsub hguard hf h with ⟨k, hk, hr⟩ | ⟨hlt, hs⟩
          · have hfetch : prog[pc + blen b]? = some (.jumpIfZero endPC) := by
              rw [hguard]
              simpa [List.append_assoc] using
                (fetch_after (before := before ++ compileB b)
                  (after := compile body bodyPC ++ [Instr.jump pc] ++ after)
                  (op := .jumpIfZero endPC) (by simp [List.length_append, compileB_length, hlen]))
            have hs : Step prog (pc + blen b, cond (b.eval s) 1 0 :: stack, s)
                (cond (b.eval s) bodyPC endPC, stack, s) := by
              cases hb : b.eval s
              · simpa [hb] using (Step.jumpIfZeroZero (stack := stack) (s := s) hfetch)
              · simpa [hb, bodyPC] using
                  (Step.jumpIfZeroSucc (n := 0) (stack := stack) (s := s) hfetch)
            by_cases hstop : (pc + blen b, cond (b.eval s) 1 0 :: stack, s) = z
            · right
              rw [← hstop]
              exact ⟨by dsimp; simp only [codeLength]; omega, _, hs⟩
            obtain ⟨j, hj, hr'⟩ := consume_step hsub hs hstop hr
            cases hb : b.eval s with
            | false =>
                rw [hb] at hr'
                exact Or.inl ⟨s, j, by omega, .whileFalse hb, by
                  simpa [endPC, bodyPC, codeLength, Nat.add_assoc] using hr'⟩
            | true =>
                rw [hb] at hr'
                rcases ihBody hlenBody (after := [Instr.jump pc] ++ after)
                  (by simpa [List.append_assoc] using hcode) hr' with
                  ⟨mid, l, hl, hbig, hout⟩ | ⟨hlt, hs⟩
                · have hjump : Step prog (bodyPC + codeLength body, stack, mid)
                      (pc, stack, mid) := by
                    apply Step.jump
                    rw [hcode]
                    exact fetch_after (by simp [List.length_append, compile_length, hlenBody])
                  by_cases hstop : (bodyPC + codeLength body, stack, mid) = z
                  · right
                    rw [← hstop]
                    exact ⟨by dsimp [bodyPC]; simp only [codeLength]; omega, _, hjump⟩
                  obtain ⟨m, hm, hrest⟩ := consume_step hsub hjump hstop hout
                  rcases ihLoop m (by omega) hlen hprog hrest with
                    ⟨fin, q, hq, hloop, hfinal⟩ | hprogress
                  · exact Or.inl ⟨fin, q, by omega, .whileTrue hb hbig hloop, hfinal⟩
                  · exact Or.inr hprogress
                · right
                  refine ⟨?_, hs⟩
                  dsimp [bodyPC] at hlt
                  simp only [codeLength]
                  omega
          · right
            refine ⟨?_, hs⟩
            simp only [List.length_append, compileB_length, hlen] at hlt
            simp only [codeLength]
            omega

private theorem reflect_cont (c : Cmd) {prog : List Instr}
    {r : Config → Config → Prop} (hsub : ∀ ⦃x y⦄, r x y → Step prog x y)
    {n pc : Nat} {before after : List Instr} {stack : List Nat} {s : State} {z : Config}
    (hlen : before.length = pc) (hprog : prog = before ++ compile c pc ++ after)
    (h : RelatesInSteps r (pc, stack, s) z n) (hz : pc + codeLength c ≤ z.1) :
    ∃ s' k, k ≤ n ∧ BigStep c s s' ∧
      RelatesInSteps r (pc + codeLength c, stack, s') z k := by
  rcases run_cases c hsub hlen hprog h with hr | ⟨hlt, _⟩
  · exact hr
  · omega

/-- A segment-confined run reaching the end of compiled code reflects an IMP
execution and restores its input stack. The source-PC restriction prevents
surrounding code from leaving and reentering the segment. -/
theorem bigStep_of_segRun {c : Cmd} {before after : List Instr} {stack : List Nat}
    {s : State} {y : Config} {n : Nat}
    (h : RelatesInSteps
      (SegStep (before ++ compile c before.length ++ after) before.length
        (before.length + codeLength c)) (before.length, stack, s) y n)
    (hy : y.1 = before.length + codeLength c) :
    ∃ s', BigStep c s s' ∧ y = (before.length + codeLength c, stack, s') := by
  obtain ⟨s', k, _, hb, hr⟩ := reflect_cont c (fun _ _ hs => hs.1) rfl rfl h (by omega)
  refine ⟨s', hb, (reflTransGen_iff_eq ?_).mp hr.reflTransGen⟩
  intro z hz
  exact (Nat.lt_irrefl _ hz.2.2)

/-- Every halting compiled run has a source execution with exactly its final
state, and its final stack equals its initial stack. -/
theorem bigStep_of_compile_halts {c : Cmd} {s s' : State} {stk stk' : List Nat}
    (h : Steps (compile c 0) (0, stk, s) (codeLength c, stk', s')) :
    BigStep c s s' ∧ stk' = stk := by
  obtain ⟨n, hn⟩ := h.relatesInSteps
  obtain ⟨fin, k, _, hb, hr⟩ := reflect_cont c (fun _ _ hs => hs)
    (before := []) (after := []) rfl (by simp) hn (by simp)
  have heq := ((reflTransGen_iff_eq
    (no_step_of_length_le (by simp [compile_length]))).mp hr.reflTransGen).symm
  have hstack : stk = stk' := congrArg (fun x : Config => x.2.1) heq
  have hstate : fin = s' := congrArg (fun x : Config => x.2.2) heq
  exact ⟨hstate ▸ hb, hstack.symm⟩

/-- Exact state-and-stack characterization of halting compiled executions. -/
theorem compile_run_iff {c : Cmd} {s s' : State} {stk stk' : List Nat} :
    Steps (compile c 0) (0, stk, s) (codeLength c, stk', s') ↔
      BigStep c s s' ∧ stk' = stk := by
  constructor
  · exact bigStep_of_compile_halts
  · rintro ⟨hb, heq⟩
    subst stk'
    simpa using (compile_runs hb (before := []) (after := []) (stack := stk))

/-- Forward correctness and termination reflection for the conventional empty stack. -/
theorem compile_correct_iff {c : Cmd} {s s' : State} :
    Steps (compile c 0) (0, [], s) (codeLength c, [], s') ↔ BigStep c s s' := by
  simp [compile_run_iff]

/-- Compiled code reaches its halt address exactly when the source terminates.
This is not a claim of progress or of existence of an infinite execution. -/
theorem compile_halts_iff {c : Cmd} {s : State} {stk : List Nat} :
    (∃ stk' s', Steps (compile c 0) (0, stk, s) (codeLength c, stk', s')) ↔
      ∃ s', BigStep c s s' := by
  simp only [compile_run_iff]
  constructor
  · rintro ⟨_, s', hb, _⟩
    exact ⟨s', hb⟩
  · rintro ⟨s', hb⟩
    exact ⟨stk, s', hb, rfl⟩

/-- Partial correctness transfers in both directions between IMP and its compiler.
The machine postcondition covers every halting run, including arbitrary final stacks. -/
theorem valid_iff_compiled {P Q : Assertion} {c : Cmd} :
    Valid P c Q ↔ ∀ s s' stk', P s →
      Steps (compile c 0) (0, [], s) (codeLength c, stk', s') → Q s' := by
  constructor
  · intro hv s s' stk' hp hr
    exact hv hp (bigStep_of_compile_halts hr).1
  · intro hv s s' hp hb
    exact hv s s' [] hp (compile_correct hb)

/-- A reachable compiled configuration is either the halted result of a source
execution with the original stack, or strictly before the halt address with a successor. -/
theorem compile_reachable_cases {c : Cmd} {s : State} {stk : List Nat} {z : Config}
    (h : Steps (compile c 0) (0, stk, s) z) :
    (∃ s', BigStep c s s' ∧ z = (codeLength c, stk, s')) ∨
      (z.1 < codeLength c ∧ ∃ w, Step (compile c 0) z w) := by
  obtain ⟨n, hn⟩ := h.relatesInSteps
  rcases run_cases c (fun _ _ hs => hs) (before := []) (after := [])
    rfl (by simp) hn with ⟨fin, k, _, hb, hr⟩ | ⟨hlt, hs⟩
  · left
    refine ⟨fin, hb, ?_⟩
    have heq := (reflTransGen_iff_eq
      (no_step_of_length_le (by simp [compile_length]))).mp hr.reflTransGen
    simpa using heq
  · exact Or.inr ⟨by simpa using hlt, hs⟩

/-- Reachable compiled code is at the halt address or can take an actual machine step. -/
theorem compile_progress {c : Cmd} {s : State} {stk : List Nat} {z : Config}
    (h : Steps (compile c 0) (0, stk, s) z) :
    z.1 = codeLength c ∨ ∃ w, Step (compile c 0) z w := by
  rcases compile_reachable_cases h with ⟨s', _, rfl⟩ | ⟨_, hs⟩
  · exact Or.inl rfl
  · exact Or.inr hs

/-- A normal reachable configuration is exactly a halted source execution,
including equality of the final state and restoration of the original stack. -/
theorem compile_reachable_normal {c : Cmd} {s : State} {stk : List Nat} {z : Config}
    (h : Steps (compile c 0) (0, stk, s) z) (hn : Relation.Normal (Step (compile c 0)) z) :
    ∃ s', BigStep c s s' ∧ z = (codeLength c, stk, s') := by
  rcases compile_reachable_cases h with hhalt | ⟨_, hs⟩
  · exact hhalt
  · exact (hn hs).elim

end Cslib.IMP.StackMachine
