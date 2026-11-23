/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps
public import MathlibExt.Computability.TuringMachine.Composition
public import MathlibExt.Computability.TuringMachine.Translation.TM2ToTM0
import Mathlib.Tactic.Ring

/-!
# The time overhead of emulating a multi-stack machine on a single tape

Mathlib emulates a multi-stack machine (`TM2`) on a single-tape machine with an internal store
(`TM1`, `Turing.TM2to1.tr`), and that on a plain single-tape machine (`TM0`, `Turing.TM1to0.tr`);
`MetaMathlibExt.TM2ToTM0.tr` is the composite. Mathlib proves that the emulations are correct
(`Turing.TM2to1.tr_respects`, `Turing.TM1to0.tr_respects`) without counting steps. This file
counts them: the emulation is at most quadratically slower, the overhead that Sipser's
Theorem 7.8 proves for his multi-tape simulation (Theorem 3.13): the bound `O(t (n + t))` is
quadratic in `t` when `t ≥ n`, Sipser's hypothesis `t(n) ≥ n`.

* **`TM2` to `TM1`.** The `TM1` emulator keeps the stacks side by side on its tape and rests at
  their common bottom. A `TM2` step runs one statement `M l`; each stack action in it walks right
  to the top of its stack, acts there and walks back, so it costs at most `2 (H + B) + 2`
  emulator steps when every stack has height at most `H` and every statement has size at most
  `B` (the size is `sizeOf`, which bounds the number of stack actions on any path through the
  statement, and so how far the heights grow during the step). With one more step to start the
  statement, a `TM2` step costs at most `1 + B (2 (H + B) + 2)` emulator steps.
* **`TM1` to `TM0`.** A `TM1` step runs a statement up to its `goto` or `halt`, and `TM1to0.tr`
  spends one `TM0` step on each `move` and `write` on the way and one on the `goto` or `halt`.
  The statements of the `TM2` emulator have at most two moves and writes on each path, so each
  of its steps is at most three `TM0` steps.
* **Runs.** Along a run of a bundled machine `tm : FinTM2` on an input `L`, the stacks after
  `i` steps have height at most `|L| + P i`, where `P = TM2Composition.pushBound tm` bounds the
  pushes of one step. Summing the costs of the first `t` steps gives the bound
  `C t (|L| + C t + 1)` with `C = emulationConstant tm`.

## Main results

- `Cslib.Turing.TM2Time.exists_relatesWithinSteps_tm1_of_step`: one `TM2` step costs at most
  `1 + B (2 (H + B) + 2)` steps of `TM2to1.tr`.
- `Cslib.Turing.TM2Time.relatesWithinSteps_tm0_of_relatesInSteps_tm1`: `m` steps of
  `TM2to1.tr` cost at most `3 m` steps of `MetaMathlibExt.TM2ToTM0.tr`.
- `Cslib.Turing.TM2Time.tm0_step_eq_none_of_step_eq_none`: the emulation halts where the
  multi-stack machine halts.
- `Cslib.Turing.TM2Time.emulationConstant`: the machine constant `C` of the bound.
- `Cslib.Turing.TM2Time.exists_tm0_run_of_tm2_run`: `t` steps of a bundled machine on the input
  `L` are emulated in at most `C t (|L| + C t + 1)` single-tape steps.
- `Cslib.Turing.TM2Time.exists_tm0_halt_of_tm2_halt`: a run that halts after `t` steps is
  emulated by a single-tape run that halts within the same bound.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Theorem 3.13 and its time analysis in Theorem 7.8.
-/

@[expose] public section

set_option autoImplicit false

open Relation Function
open _root_.Turing
open _root_.Turing.TM2to1

namespace Cslib.Turing.TM2Time

/-! ### Multi-stack steps on the `TM1` emulator -/

section TM2ToTM1

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*} (M : Λ → TM2.Stmt Γ Λ σ)

/-- **The emulator walks right to the top of a stack.** Let $M$ be a multi-stack machine, $k$ a
stack, $L$ tape contents whose $k$-th track lists a stack $S$ from bottom to top, and
$n \le |S|$. In the $\mathrm{TM1}$ emulator of $M$, the configuration in the state that walks to
stack $k$ (for a given stack action and continuation), with internal state $v$ and head at the
bottom marker of $L$, reaches in exactly $n$ steps the same configuration with the head moved
$n$ cells to the right. -/
theorem relatesInSteps_go {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : ℕ) (H : n ≤ S.length) :
    RelatesInSteps (fun a b ↦ b ∈ TM1.step (tr M) a)
      ⟨some (.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (.go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ n := by
  induction n with
  | zero => exact .refl _
  | succ n IH =>
    refine .tail _ _ _ _ (IH (le_of_lt H)) ?_
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd, Option.mem_def]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

/-- **The emulator walks back to the bottom.** Let $M$ be a multi-stack machine and $L$ tape
contents. For every $n$, in the $\mathrm{TM1}$ emulator of $M$, the configuration in the return
state (for a given continuation), with internal state $v$ and head $n$ cells to the right of the
bottom marker of $L$, reaches in exactly $n$ steps the same configuration with the head at the
bottom marker. -/
theorem relatesInSteps_ret {q : TM2.Stmt Γ Λ σ} {v : σ} {L : ListBlank (∀ k, Option (Γ k))}
    (n : ℕ) :
    RelatesInSteps (fun a b ↦ b ∈ TM1.step (tr M) a)
      ⟨some (.ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (.ret q), v, Tape.mk' ∅ (addBottom L)⟩ n := by
  induction n with
  | zero => exact .refl _
  | succ n IH =>
    refine .head _ _ _ _ ?_ IH
    simp only [Option.mem_def, TM1.step]
    rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
      addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', comp_apply, Tape.move_right_left]
    rfl

omit [DecidableEq K] in
/-- A stack action grows its stack by at most one symbol. -/
private theorem length_stWrite_le {k : K} (v : σ) (l : List (Γ k)) (s : StAct K Γ σ k) :
    (stWrite v l s).length ≤ l.length + 1 := by
  cases s <;> simp [stWrite]
  omega

omit [DecidableEq K] in
/-- A stack action is one node of the statement tree. -/
private theorem sizeOf_stRun {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    sizeOf q + 1 ≤ sizeOf (stRun s q) := by
  cases s <;> simp only [stRun, TM2.Stmt.push.sizeOf_spec, TM2.Stmt.peek.sizeOf_spec,
    TM2.Stmt.pop.sizeOf_spec] <;> omega

/-- The step bound of a statement is monotone in its size. -/
private theorem stepBound_mono {a b : ℕ} (H : ℕ) (h : a ≤ b) :
    a * (2 * (H + a) + 2) ≤ b * (2 * (H + b) + 2) :=
  Nat.mul_le_mul h (by omega)

/-- **Running one statement on the emulator.** Let $M$ be a multi-stack machine and $N$ a
statement over the same stack alphabets, labels and internal states, and write $|N|$ for the
structural size of $N$. Let $H \in \mathbb{N}$, let $v$ be an internal state, let $S$ be a
family of stacks $S_k$, each of height at most $H$, and let $L$ be tape contents whose $k$-th
track lists $S_k$ from bottom to top, for every $k$. Running the translation of $N$ in the
$\mathrm{TM1}$ emulator of $M$ from state $v$, with the head at the bottom marker of $L$, gives
a configuration that reaches, in some number $m \le |N| (2 (H + |N|) + 2)$ of emulator steps,
a configuration representing the result of running $N$ from state $v$ on the stacks $S$: it
has the corresponding label and the same internal state, and its head is at the bottom marker
of a tape whose $k$-th track lists the $k$-th resulting stack from bottom to top. -/
theorem exists_relatesInSteps_stepAux (N : TM2.Stmt Γ Λ σ) :
    ∀ (H : ℕ) (v : σ) (S : ∀ k, List (Γ k)) (L : ListBlank (∀ k, Option (Γ k))),
      (∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) →
      (∀ k, (S k).length ≤ H) →
      ∃ b m, TrCfg (TM2.stepAux N v S) b ∧
        RelatesInSteps (fun a b ↦ b ∈ TM1.step (tr M) a)
          (TM1.stepAux (trNormal N) v (Tape.mk' ∅ (addBottom L))) b m ∧
        m ≤ sizeOf N * (2 * (H + sizeOf N) + 2) := by
  induction N using stmtStRec with
  | run k s q IH =>
    intro H v S L hL hS
    rw [trNormal_run, step_run]
    obtain ⟨L', hL', hrun⟩ :=
      tr_respects_aux₂ (Λ := Λ) (q := TM1.Stmt.goto fun _ _ ↦ Λ'.ret q) hL s
    have hS' : ∀ k', (update S k (stWrite v (S k) s) k').length ≤ H + 1 := by
      intro k'
      rcases eq_or_ne k' k with rfl | hk
      · rw [update_self]
        exact (length_stWrite_le v _ s).trans (by have := hS k'; omega)
      · rw [update_of_ne hk]
        exact (hS k').trans (Nat.le_succ H)
    obtain ⟨b, m, hb, hr, hm⟩ := IH (H + 1) _ _ L' hL' hS'
    refine ⟨b, (S k).length + 1 + (update S k (stWrite v (S k) s) k).length + 1 + m, hb, ?_, ?_⟩
    · have hgo := relatesInSteps_go M s q v (hL k) _ le_rfl
      have hstep : (⟨some (.ret q), stVar v (S k) s, (Tape.move Dir.right)^[
          (update S k (stWrite v (S k) s) k).length] (Tape.mk' ∅ (addBottom L'))⟩ :
            TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) ∈
          TM1.step (tr M) ⟨some (.go k s q), v,
            (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ := by
        simp only [Option.mem_def, TM1.step]
        rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
          addBottom_nth_snd, stk_nth_val _ (hL k),
          List.getElem?_eq_none (le_of_eq List.length_reverse), Option.isNone, cond, hrun,
          TM1.stepAux]
      have hret := relatesInSteps_ret M (q := q) (v := stVar v (S k) s) (L := L')
        (update S k (stWrite v (S k) s) k).length
      have hlast : TM1.stepAux (trNormal q) (stVar v (S k) s) (Tape.mk' ∅ (addBottom L')) ∈
          TM1.step (tr M) ⟨some (.ret q), stVar v (S k) s, Tape.mk' ∅ (addBottom L')⟩ := by
        simp only [Option.mem_def, TM1.step]
        rw [Option.some_inj, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
        rfl
      exact (((hgo.tail _ _ _ _ hstep).trans hret).tail _ _ _ _ hlast).trans hr
    · have hsz := sizeOf_stRun s q
      have hk := hS k
      have hk' := hS' k
      have e : (sizeOf q + 1) * (2 * (H + (sizeOf q + 1)) + 2) =
          sizeOf q * (2 * (H + 1 + sizeOf q) + 2) + (2 * H + 2 * sizeOf q + 4) := by ring
      have := stepBound_mono H hsz
      omega
  | load a q IH =>
    intro H v S L hL hS
    obtain ⟨b, m, hb, hr, hm⟩ := IH H (a v) S L hL hS
    exact ⟨b, m, hb, hr, hm.trans (stepBound_mono H (by
      rw [TM2.Stmt.load.sizeOf_spec]; omega))⟩
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro H v S L hL hS
    have h₁ : sizeOf q₁ ≤ sizeOf (TM2.Stmt.branch p q₁ q₂) := by
      rw [TM2.Stmt.branch.sizeOf_spec]; omega
    have h₂ : sizeOf q₂ ≤ sizeOf (TM2.Stmt.branch p q₁ q₂) := by
      rw [TM2.Stmt.branch.sizeOf_spec]; omega
    cases hp : p v
    · obtain ⟨b, m, hb, hr, hm⟩ := IH₂ H v S L hL hS
      refine ⟨b, m, ?_, ?_, hm.trans (stepBound_mono H h₂)⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_false] using hb
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_false] using hr
    · obtain ⟨b, m, hb, hr, hm⟩ := IH₁ H v S L hL hS
      refine ⟨b, m, ?_, ?_, hm.trans (stepBound_mono H h₁)⟩
      · simpa only [TM2.stepAux, hp, Bool.cond_true] using hb
      · simpa only [trNormal, TM1.stepAux, hp, Bool.cond_true] using hr
  | goto l =>
    intro H v S L hL hS
    exact ⟨_, 0, ⟨_, hL⟩, .refl _, Nat.zero_le _⟩
  | halt =>
    intro H v S L hL hS
    exact ⟨_, 0, ⟨_, hL⟩, .refl _, Nat.zero_le _⟩

/-- **One multi-stack step costs at most $1 + B(2(H + B) + 2)$ emulator steps.** Let $M$ be a
multi-stack machine in which the statement of every label has size at most $B$, and consider its
emulation by a single-tape machine with an internal store that keeps the stacks side by side on
its tape. Let $c$ be a configuration of $M$ in which every stack has height at most $H$, and let
$c_1$ be a configuration of the emulator that represents $c$. If $M$ moves from $c$ to $c'$ in one
step, then there is a configuration $c_1'$ of the emulator that represents $c'$ and that the
emulator reaches from $c_1$ in at most $1 + B(2(H + B) + 2)$ steps.

The size of a statement is its structural size as a term. This is a counted form of the
correctness of the emulation. -/
theorem exists_relatesWithinSteps_tm1_of_step {B H : ℕ} (hB : ∀ l, sizeOf (M l) ≤ B)
    {c c' : TM2.Cfg Γ Λ σ} {c₁ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (hc : TrCfg c c₁)
    (hH : ∀ k, (c.stk k).length ≤ H) (h : TM2.step M c = some c') :
    ∃ c₁', TrCfg c' c₁' ∧
      RelatesWithinSteps (fun a b ↦ b ∈ TM1.step (tr M) a) c₁ c₁'
        (1 + B * (2 * (H + B) + 2)) := by
  obtain @⟨- | l, v, S, L, hL⟩ := hc
  · cases h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    obtain ⟨b, m, hb, hr, hm⟩ := exists_relatesInSteps_stepAux M (M l) H v S L hL hH
    exact ⟨b, hb, m + 1, by have := stepBound_mono H (hB l); omega, .head _ _ _ _ rfl hr⟩

/-- **The emulation halts where the multi-stack machine halts**: a halted configuration is
related only to configurations of the single-tape emulation that do not step. -/
theorem tm0_step_eq_none_of_step_eq_none [Inhabited Λ] [Inhabited σ] {c : TM2.Cfg Γ Λ σ}
    {c₁ : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} (hc : TrCfg c c₁) (h : TM2.step M c = none) :
    TM0.step (MetaMathlibExt.TM2ToTM0.tr M) (TM1to0.trCfg (tr M) c₁) = none := by
  obtain @⟨- | l, v, S, L, hL⟩ := hc
  · rfl
  · cases h

end TM2ToTM1

/-! ### `TM1` steps on `TM0` -/

section TM1ToTM0

variable {Γ Λ σ : Type*}

/-- The largest number of `move` and `write` nodes on a path through a `TM1` statement: the
`TM0` steps that `TM1to0.tr` spends on a run of the statement, besides the final `goto` or
`halt`. -/
private def moves : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => moves q + 1
  | .write _ q => moves q + 1
  | .load _ q => moves q
  | .branch _ q₁ q₂ => max (moves q₁) (moves q₂)
  | .goto _ => 0
  | .halt => 0

/-- Two configurations with the same successor reach the same configurations in a positive
number of steps. -/
private theorem relatesInSteps_of_step_eq {α : Type*} {f : α → Option α} {a a' b : α} {n : ℕ}
    (h : f a' = f a) (hr : RelatesInSteps (fun x y ↦ y ∈ f x) a b (n + 1)) :
    RelatesInSteps (fun x y ↦ y ∈ f x) a' b (n + 1) := by
  obtain ⟨t, ht, hr⟩ := hr.succ'
  exact .head _ _ _ _ (h ▸ ht) hr

variable [Inhabited Γ] [Inhabited Λ] [Inhabited σ] (M : Λ → TM1.Stmt Γ Λ σ)

/-- `TM1to0.tr` runs a statement in one `TM0` step per `move` and `write` on its path, plus one
for the final `goto` or `halt`: a counted form of `TM1to0.tr_respects`. -/
private theorem exists_relatesInSteps_trAux (q : TM1.Stmt Γ Λ σ) :
    ∀ (v : σ) (T : Tape Γ), ∃ n, n ≤ moves q ∧
      RelatesInSteps (fun a b ↦ b ∈ TM0.step (TM1to0.tr M) a) ⟨(some q, v), T⟩
        (TM1to0.trCfg M (TM1.stepAux q v T)) (n + 1) := by
  induction q with
  | move d q IH =>
    intro v T
    obtain ⟨n, hn, hr⟩ := IH v (T.move d)
    exact ⟨n + 1, by simp only [moves]; omega, .head _ _ _ _ rfl hr⟩
  | write a q IH =>
    intro v T
    obtain ⟨n, hn, hr⟩ := IH v (T.write (a T.1 v))
    exact ⟨n + 1, by simp only [moves]; omega, .head _ _ _ _ rfl hr⟩
  | load a q IH =>
    intro v T
    obtain ⟨n, hn, hr⟩ := IH (a T.1 v) T
    exact ⟨n, hn, relatesInSteps_of_step_eq (by rfl) hr⟩
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro v T
    cases hp : p T.1 v
    · obtain ⟨n, hn, hr⟩ := IH₂ v T
      refine ⟨n, by simp only [moves]; omega, ?_⟩
      rw [show TM1.stepAux (.branch p q₁ q₂) v T = TM1.stepAux q₂ v T by
        simp only [TM1.stepAux, hp, Bool.cond_false]]
      exact relatesInSteps_of_step_eq
        (by simp only [TM0.step, TM1to0.tr, TM1to0.trAux, hp]; rfl) hr
    · obtain ⟨n, hn, hr⟩ := IH₁ v T
      refine ⟨n, by simp only [moves]; omega, ?_⟩
      rw [show TM1.stepAux (.branch p q₁ q₂) v T = TM1.stepAux q₁ v T by
        simp only [TM1.stepAux, hp, Bool.cond_true]]
      exact relatesInSteps_of_step_eq
        (by simp only [TM0.step, TM1to0.tr, TM1to0.trAux, hp]; rfl) hr
  | goto l =>
    intro v T
    exact ⟨0, le_rfl,
      .single (congr_arg some (congr (congr_arg TM0.Cfg.mk rfl) (Tape.write_self T)))⟩
  | halt =>
    intro v T
    exact ⟨0, le_rfl,
      .single (congr_arg some (congr (congr_arg TM0.Cfg.mk rfl) (Tape.write_self T)))⟩

/-- `m` steps of a `TM1` machine whose statements have at most `B` moves and writes on each path
take at most `(B + 1) m` steps of `TM1to0.tr`. -/
private theorem relatesWithinSteps_trCfg {B : ℕ} (hM : ∀ l, moves (M l) ≤ B)
    {c c' : TM1.Cfg Γ Λ σ} {m : ℕ} (h : RelatesInSteps (fun a b ↦ b ∈ TM1.step M a) c c' m) :
    RelatesWithinSteps (fun a b ↦ b ∈ TM0.step (TM1to0.tr M) a) (TM1to0.trCfg M c)
      (TM1to0.trCfg M c') ((B + 1) * m) := by
  induction h with
  | refl => exact .refl _
  | tail t' t'' m _ hstep ih =>
    rw [Nat.mul_succ]
    refine ih.trans ?_
    obtain ⟨_ | l, v, T⟩ := t'
    · cases hstep
    · simp only [TM1.step, Option.mem_def, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨n, hn, hr⟩ := exists_relatesInSteps_trAux M (M l) v T
      exact ⟨n + 1, by have := hM l; omega, hr⟩

end TM1ToTM0

section Emulator

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*} (M : Λ → TM2.Stmt Γ Λ σ)

omit [DecidableEq K] in
/-- The translation of a multi-stack statement only moves to other labels: it never moves or
writes. -/
private theorem moves_trNormal (N : TM2.Stmt Γ Λ σ) :
    moves (trNormal N : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) = 0 := by
  induction N <;> simp_all [trNormal, moves]

/-- Every statement of the `TM1` emulator has at most two moves and writes on each path. -/
private theorem moves_tr (l : Λ' K Γ Λ σ) : moves (tr M l) ≤ 2 := by
  cases l with
  | normal l => simp [tr, moves_trNormal]
  | go k s q => cases s <;> simp [tr, trStAct, moves]
  | ret q => simp [tr, moves, moves_trNormal]

/-- **Each step of the $\mathrm{TM1}$ emulator is at most three single-tape steps.** Let $M$ be
a multi-stack machine with a default label and a default internal state. If the
$\mathrm{TM1}$ emulator of $M$ goes from $c$ to $c'$ in exactly $m$ steps, then the
single-tape emulation of $M$ goes from the single-tape form of $c$ to the single-tape form of
$c'$ in at most $3m$ steps. -/
theorem relatesWithinSteps_tm0_of_relatesInSteps_tm1 [Inhabited Λ] [Inhabited σ]
    {c c' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ} {m : ℕ}
    (h : RelatesInSteps (fun a b ↦ b ∈ TM1.step (tr M) a) c c' m) :
    RelatesWithinSteps (fun a b ↦ b ∈ TM0.step (MetaMathlibExt.TM2ToTM0.tr M) a)
      (TM1to0.trCfg (tr M) c) (TM1to0.trCfg (tr M) c') (3 * m) :=
  relatesWithinSteps_trCfg (tr M) (moves_tr M) h

end Emulator

/-! ### Runs of bundled machines -/

section Bundled

open scoped MetaMathlibExt.TM2ToTM0

attribute [local instance] FinTM2.ΛFin

/-- **Emulation constant.** For a bundled multi-stack machine $M$, the emulation constant is
$C = 3(2B + 1) + P$, where $B = \sum_l |M(l)|$ is the total structural size of the statements
$M(l)$ over all labels $l$ (so each statement has size at most $B$), and $P$ is the push bound
of $M$, the total number of push instructions in its statements, which bounds the number of
pushes in one step. -/
noncomputable def emulationConstant (tm : FinTM2) : ℕ :=
  3 * (2 * ∑ l, sizeOf (tm.m l) + 1) + MetaMathlibExt.TM2Composition.pushBound tm

/-- The arithmetic of one more step of the run. -/
private theorem bound_succ {X P B C t n k : ℕ} (hC : 3 * (2 * B + 1) + P ≤ C)
    (hn : n ≤ C * t * (X + C * t + 1)) (hk : k ≤ 3 * (1 + B * (2 * (X + P * t + B) + 2))) :
    n + k ≤ C * (t + 1) * (X + C * (t + 1) + 1) := by
  have h₁ : 3 * (1 + B * (2 * (X + P * t + B) + 2)) ≤
      3 * (2 * B + 1) * (X + P * t + B + 1) := by
    ring_nf; omega
  have h₂ : P * t ≤ C * t := Nat.mul_le_mul_right t (by omega)
  have h₃ : 3 * (2 * B + 1) * (X + P * t + B + 1) ≤ C * (X + C * (t + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by rw [Nat.mul_succ]; omega)
  have h₄ : C * t * (X + C * t + 1) ≤ C * t * (X + C * (t + 1) + 1) :=
    Nat.mul_le_mul_left _ (by rw [Nat.mul_succ]; omega)
  have e : C * (t + 1) * (X + C * (t + 1) + 1) =
      C * t * (X + C * (t + 1) + 1) + C * (X + C * (t + 1) + 1) := by ring
  omega

/-- **Quadratic overhead of the single-tape emulation.** Let $M$ be a bundled multi-stack
machine with emulation constant $C$, and $L$ an input for its input stack. If $M$, started on
$L$, reaches a configuration $c$ after $t$ steps, then the single-tape emulation of $M$,
started on the encoding of $L$, reaches in some number $n \le C t (|L| + C t + 1)$ of steps the
single-tape form of a configuration of the $\mathrm{TM1}$ emulator of $M$ that represents $c$:
it has the corresponding label and the same internal state, and its head is at the bottom
marker of a tape whose $k$-th track lists the $k$-th stack of $c$ from bottom to top. -/
theorem exists_tm0_run_of_tm2_run (tm : FinTM2) (L : List (tm.Γ tm.k₀)) {c : tm.Cfg} {t : ℕ}
    (h : (flip bind tm.step)^[t] (some (initList tm L)) = some c) :
    ∃ (c₁ : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ) (n : ℕ),
      TrCfg c c₁ ∧
      RelatesInSteps (fun a b ↦ b ∈ TM0.step (MetaMathlibExt.TM2ToTM0.tr tm.m) a)
        (TM0.init (trInit tm.k₀ L)) (TM1to0.trCfg (tr tm.m) c₁) n ∧
      n ≤ emulationConstant tm * t * (L.length + emulationConstant tm * t + 1) := by
  induction t generalizing c with
  | zero =>
    simp only [iterate_zero, id, Option.some.injEq] at h
    subst h
    refine ⟨TM1.init (trInit tm.k₀ L), 0, ?_, .refl _, by simp⟩
    rw [MetaMathlibExt.TM2ToTM0.initList_eq_init]
    exact trCfg_init tm.k₀ L
  | succ t IH =>
    rw [iterate_succ_apply'] at h
    obtain ⟨c', hc', hstep⟩ : ∃ c', (flip bind tm.step)^[t] (some (initList tm L)) = some c' ∧
        tm.step c' = some c := by
      cases e : (flip bind tm.step)^[t] (some (initList tm L)) with
      | none => rw [e] at h; cases h
      | some c' => rw [e] at h; exact ⟨c', rfl, h⟩
    obtain ⟨c₁, n, hc₁, hr, hn⟩ := IH hc'
    have hH : ∀ k, (c'.stk k).length ≤
        L.length + MetaMathlibExt.TM2Composition.pushBound tm * t := fun k ↦
      (MetaMathlibExt.TM2Composition.length_iter tm k t _ _ hc').trans
        (Nat.add_le_add_right (MetaMathlibExt.TM2Composition.initList_stk_length_le tm L k) _)
    obtain ⟨c₁', hc₁', m, hm, hr₁⟩ := exists_relatesWithinSteps_tm1_of_step tm.m
      (fun l ↦ Finset.single_le_sum (f := fun l ↦ sizeOf (tm.m l)) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ l)) hc₁ hH hstep
    obtain ⟨k, hk, hr₀⟩ := relatesWithinSteps_tm0_of_relatesInSteps_tm1 tm.m hr₁
    exact ⟨c₁', n + k, hc₁', hr.trans hr₀, bound_succ le_rfl hn (hk.trans (by omega))⟩

/-- **Single-tape emulation of halting multi-stack runs.** Let $M$ be a bundled multi-stack
machine with emulation constant $C$, and $L$ an input for its input stack. If $M$, started on
$L$, reaches after $t$ steps a configuration $c$ from which it does not step, then the
single-tape emulation of $M$, started on the encoding of $L$, reaches in some number
$n \le C t (|L| + C t + 1)$ of steps a configuration from which it does not step. That
configuration is the single-tape form of a configuration of the $\mathrm{TM1}$ emulator of $M$
that represents $c$: it has the corresponding label and the same internal state, and its head
is at the bottom marker of a tape whose $k$-th track lists the $k$-th stack of $c$ from bottom
to top. -/
theorem exists_tm0_halt_of_tm2_halt (tm : FinTM2) (L : List (tm.Γ tm.k₀)) {c : tm.Cfg} {t : ℕ}
    (h : (flip bind tm.step)^[t] (some (initList tm L)) = some c) (hc : tm.step c = none) :
    ∃ (c₁ : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ) (n : ℕ),
      TrCfg c c₁ ∧
      RelatesInSteps (fun a b ↦ b ∈ TM0.step (MetaMathlibExt.TM2ToTM0.tr tm.m) a)
        (TM0.init (trInit tm.k₀ L)) (TM1to0.trCfg (tr tm.m) c₁) n ∧
      TM0.step (MetaMathlibExt.TM2ToTM0.tr tm.m) (TM1to0.trCfg (tr tm.m) c₁) = none ∧
      n ≤ emulationConstant tm * t * (L.length + emulationConstant tm * t + 1) := by
  obtain ⟨c₁, n, hc₁, hr, hn⟩ := exists_tm0_run_of_tm2_run tm L h
  exact ⟨c₁, n, hc₁, hr, tm0_step_eq_none_of_step_eq_none tm.m hc₁ hc, hn⟩

end Bundled

end Cslib.Turing.TM2Time
