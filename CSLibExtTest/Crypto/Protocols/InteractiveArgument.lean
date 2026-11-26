/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Protocols.InteractiveArgument
import MathlibExt.Computability.TuringMachine.Program
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.NormNum

/-!
# A private-coin protocol for the last bit

The verifier sends the third of three independent bits. For the correct claim it checks
that the two messages are that challenge and its complement, in that order. For a wrong
claim it requires the last payload bit to equal *both* hidden bits. Conditional on the
challenge, the last payload bit is fixed, and just one of the four hidden pairs matches.
-/

namespace Cslib.Crypto.Interaction.Tests

open Turing MetaMathlibExt TM2Program BitstringEncoding Framework

-- Machine certificate for the finite-state scans used below: consume the entire input,
-- write one bit, reset control and halt. Input and output have separate stacks.
private abbrev Alph (α : Type) : Bool → Type
  | false => α
  | true => Bool

private def scanStacks {α : Type} (xs : List α) (ys : List Bool) : (k : Bool) → List (Alph α k)
  | false => xs
  | true => ys

private def scanCode {α Q : Type} (step : Q → α → Q) (finish : Q → Bool) (q : Q) :
    TM2.Stmt (Alph α) Q (Option α) :=
  .pop false (fun _ a => a) <| .branch Option.isSome
    (.goto fun a => a.elim q (step q))
    (.push true (fun _ => finish q) (.load (fun _ => none) .halt))

private theorem scanRun {α Q : Type} (step : Q → α → Q) (finish : Q → Bool)
    (q : Q) (xs : List α) (v : Option α) :
    Run (scanCode step finish) (xs.length + 1) ⟨some q, v, scanStacks xs []⟩
      ⟨none, none, scanStacks ([] : List α) [finish (xs.foldl step q)]⟩ := by
  induction xs generalizing q v with
  | nil =>
    apply Run.single
    apply congrArg (TM2.Cfg.mk none none)
    funext k
    cases k <;> rfl
  | cons a xs ih =>
    apply (ih (step q a) (some a)).head
    apply congrArg some
    apply congrArg (TM2.Cfg.mk (some (step q a)) (some a))
    funext k
    cases k <;> rfl

private noncomputable def scanMachine {α Q : Type} [Fintype α] [Fintype Q]
    (step : Q → α → Q) (start : Q) (finish : Q → Bool) :
    TM2ComputableInPolyTime id id (fun xs : List α => [finish (xs.foldl step start)]) where
  tm := { K := Bool, k₀ := false, k₁ := true, Γ := Alph α, Λ := Q,
          main := start, σ := Option α, initialState := none,
          Γk₀Fin := inferInstanceAs (Fintype α), m := scanCode step finish }
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun xs := by
    refine ⟨⟨xs.length + 1, ?_⟩, by simp⟩
    let tm : FinTM2 := { K := Bool, k₀ := false, k₁ := true, Γ := Alph α, Λ := Q,
                         main := start, σ := Option α, initialState := none,
                         Γk₀Fin := inferInstanceAs (Fintype α), m := scanCode step finish }
    let out := [finish (xs.foldl step start)]
    have h₀ : initList tm xs = ⟨some start, none, scanStacks xs []⟩ := by
      apply congrArg (TM2.Cfg.mk (some start) none)
      funext k
      cases k <;> rfl
    have h₁ : haltList tm out = ⟨none, none, scanStacks ([] : List α) out⟩ := by
      apply congrArg (TM2.Cfg.mk none none)
      funext k
      cases k <;> rfl
    change Run tm.m (xs.length + 1) (initList tm (xs.map id)) (haltList tm (out.map id))
    rw [List.map_id, List.map_id, h₀, h₁]
    exact scanRun step finish start xs none

private theorem bool_code (b : Bool) : bitEncode b = [b] := rfl

private noncomputable def scanBit {α Q : Type} [Fintype α] [Fintype Q]
    (step : Q → α → Q) (start : Q) (finish : Q → Bool) :
    TM2ComputableInPolyTime id bitEncode (fun xs : List α => finish (xs.foldl step start)) where
  toTM2ComputableAux := (scanMachine step start finish).toTM2ComputableAux
  time := (scanMachine step start finish).time
  outputsFun xs := (scanMachine step start finish).outputsFun xs

private structure Registers where
  actual : Bool := false
  claimed : Bool := false
  hidden₀ : Bool := false
  hidden₁ : Bool := false
  visible : Bool := false
  prev : Bool := false
  last : Bool := false
  deriving DecidableEq

private noncomputable instance : Fintype Registers := Fintype.ofInjective
  (fun s : Registers => ((s.actual, s.claimed), (s.hidden₀, s.hidden₁), (s.visible, s.prev), s.last))
  (by rintro ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h; simpa [and_assoc] using h)

private def readSymbol (s : Registers) : Symbol → Registers
  | .input b => {s with actual := b}
  | .claim b => {s with claimed := b}
  | .coin b => {s with hidden₀ := s.hidden₁, hidden₁ := s.visible, visible := b}
  | .payload b => {s with prev := s.last, last := b}
  | .stop => s

private def check (s : Registers) : Bool :=
  if s.actual == s.claimed then s.prev == s.visible && s.last == !s.visible
  else s.last == s.hidden₀ && s.last == s.hidden₁

private def scan := fun w : List Symbol => w.foldl readSymbol {}
private def lastBit := fun x : List Bool => x.foldl (fun _ b => b) false

private noncomputable def V : Verifier where
  verifierFirst := true
  messages := 2
  coins := 3
  width := 1
  send w := [(scan w).visible]
  accept w := check (scan w)
  sendTM := scanMachine readSymbol {} Registers.visible
  acceptTM := scanBit readSymbol {} check

private def honest : Strategy Bool where
  claim := lastBit
  reply w := [!(scan w).last]

private theorem readInput (x : List Bool) (s : Registers) :
    (x.map Symbol.input).foldl readSymbol s = {s with actual := x.foldl (fun _ b => b) s.actual} := by
  induction x generalizing s with
  | nil => rfl
  | cons a x ih => exact ih {s with actual := a}

private theorem view_start (x : List Bool) (y a b c : Bool) :
    scan (view x (bitEncode y) [a,b,c] []) =
      { actual := lastBit x, claimed := y, hidden₀ := a, hidden₁ := b, visible := c } := by
  simp [view, scan, List.foldl_append, readInput, bool_code, readSymbol, lastBit]

-- At a fixed challenge the reply has no hidden-bit parameter.
private def response (P : Strategy Bool) (x : List Bool) (c : Bool) : List Bool :=
  (P.reply (view x (bitEncode (P.claim x)) [] [[c]])).take 1

private theorem rounds (P : Strategy Bool) (x : List Bool) (a b c : Bool) :
    V.history P x [a,b,c] 2 = [[c], response P x c] := by
  simp [Verifier.history, V, view_start, response, List.take]

private def endBit (P : Strategy Bool) (x : List Bool) (c : Bool) : Bool :=
  (response P x c).foldl (fun _ b => b) c

private theorem readPayload (m : List Bool) (s : Registers) :
    let t := (m.map Symbol.payload).foldl readSymbol s
    t.actual = s.actual ∧ t.claimed = s.claimed ∧ t.hidden₀ = s.hidden₀ ∧
      t.hidden₁ = s.hidden₁ ∧ t.last = m.foldl (fun _ b => b) s.last := by
  induction m generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a m ih => exact ih {s with prev := s.last, last := a}

private theorem out_wrong (P : Strategy Bool) (x : List Bool) (hy : P.claim x ≠ lastBit x)
    (a b c : Bool) : V.out P x [a,b,c] = ((endBit P x c == a) && (endBit P x c == b)) := by
  have hm : V.messages.eval x.length = 2 := by simp [V]
  rw [Verifier.out, hm, rounds]
  let s : Registers :=
    { actual := lastBit x, claimed := P.claim x, hidden₀ := a, hidden₁ := b, visible := c, last := c }
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := readPayload (response P x c) s
  simp only [V, scan, view, bool_code, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil, readInput]
  change check (((response P x c).map Symbol.payload).foldl readSymbol s) = _
  simp [check, h₁, h₂, h₃, h₄, h₅, s, Ne.symm hy, endBit]

private theorem out_honest (x : List Bool) (a b c : Bool) : V.out honest x [a,b,c] = true := by
  have hm : V.messages.eval x.length = 2 := by simp [V]
  rw [Verifier.out, hm, rounds]
  simp [V, honest, check, scan, view, List.foldl_append, readInput, response, lastBit,
    bool_code, readSymbol, List.take]

private theorem count_hidden (g : Bool → Bool) :
    ((Finset.univ : Finset (Fin 3 → Bool)).filter fun r =>
      ((g (r 2) == r 0) && (g (r 2) == r 1)) = true).card = 2 := by
  have : g = fun b => cond b (g true) (g false) := by funext b; cases b <;> rfl
  conv_lhs => rw [this]
  cases g true <;> cases g false <;> decide

private theorem prob (P : Strategy Bool) (x : List Bool) : V.acceptance P x =
    ((Finset.univ.filter fun r : Fin 3 → Bool => V.out P x [r 0,r 1,r 2] = true).card : ℝ) / 8 := by
  rw [Verifier.acceptance, winProb_map_uniform]
  have hc : V.coins.eval x.length = 3 := by simp [V]
  rw [hc]
  simp [List.ofFn_succ]

private theorem proofSystem : IsSystem .statistical V honest lastBit 0 (1 / 4) := by
  refine ⟨by constructor <;> norm_num, by constructor <;> norm_num,
    ⟨(scanBit (fun _ b : Bool => b) false id).toTM2ComputableInTime.toTM2Computable⟩,
    ⟨(scanMachine readSymbol {} (fun s => !s.last)).toTM2ComputableInTime.toTM2Computable⟩,
    fun x => ⟨rfl, ?_⟩, fun P x hy => ?_⟩
  · rw [prob]
    norm_num [out_honest, Fintype.card_fun]
  · rw [prob]
    simp_rw [out_wrong P x hy]
    rw [count_hidden]
    norm_num

example : IsSystem .computational V honest lastBit 0 (1 / 4) := proofSystem.toArgument

-- Prover-first and zero-message boundary cases.
example (P : Strategy Bool) (x r : List Bool) :
    ({V with verifierFirst := false}).history P x r 1 =
      [(P.reply (view x (bitEncode (P.claim x)) [] [])).take 1] := by
  simp [Verifier.history, V]

example (P : Strategy Bool) (x r : List Bool) : V.history P x r 0 = [] := rfl

-- A finite exception tests the length threshold without a hardness assumption. For the
-- constant true function, accept either claim at the empty word but only true elsewhere.
private def exceptionStep (s : Bool) : Symbol → Bool
  | .input _ => false
  | .claim b => s || b
  | _ => s

private noncomputable def exceptionV : Verifier :=
  { V with
    messages := 0
    coins := 0
    accept := fun w => w.foldl exceptionStep true
    acceptTM := scanBit exceptionStep true id }

private def constantProver : Strategy Bool := { honest with claim := fun _ => true }

private theorem inputFlag (x : List Bool) (s : Bool) :
    (x.map Symbol.input).foldl exceptionStep s = (x.isEmpty && s) := by
  induction x generalizing s with
  | nil => rfl
  | cons a x ih => simpa [List.foldl_cons, exceptionStep] using ih false

private theorem exceptionProb (A : Strategy Bool) (x : List Bool) :
    exceptionV.acceptance A x = if x.isEmpty || A.claim x then 1 else 0 := by
  rw [Verifier.acceptance, winProb_map_uniform]
  have hz : exceptionV.coins.eval x.length = 0 := by simp [exceptionV]
  rw [hz]
  by_cases h : (x.isEmpty || A.claim x) = true <;>
    simp [exceptionV, Verifier.out, Verifier.history, view, bool_code, inputFlag, exceptionStep, h]

-- Threshold one works simultaneously for all inputs of positive length. Threshold zero
-- would incorrectly include the empty word, where even an efficient claim can be wrong.
example : IsSystem .computational exceptionV constantProver (fun _ => true) 0 0 ∧
    ¬ IsSystem .statistical exceptionV constantProver (fun _ => true) 0 0 := by
  constructor
  · refine ⟨by constructor <;> norm_num, by constructor <;> norm_num,
      ⟨(scanBit (fun _ b : Bool => b) true (fun _ => true)).toTM2ComputableInTime.toTM2Computable⟩,
      ⟨(scanMachine readSymbol {} (fun s => !s.last)).toTM2ComputableInTime.toTM2Computable⟩,
      fun x => ⟨rfl, ?_⟩, fun A _ _ => ⟨1, fun x hx hy => ?_⟩⟩
    · simp [exceptionProb, constantProver]
    · cases x with
      | nil => simp at hx
      | cons b xs => simp [exceptionProb, hy]
  · rintro ⟨_, _, _, _, _, hsound⟩
    have h := hsound honest [] (by decide)
    norm_num [exceptionProb] at h

-- The exception is visible even to the fixed efficient last-bit strategy above. Thus
-- restricting the all-input soundness test to efficient routines would still fail here.
example : ¬ (∀ A : Strategy Bool, Nonempty (TM2ComputableInPolyTime id bitEncode A.claim) →
    Nonempty (TM2ComputableInPolyTime id id A.reply) →
    ∀ x, A.claim x ≠ true → exceptionV.acceptance A x ≤ 0) := by
  intro allInputs
  have h := allInputs honest ⟨scanBit (fun _ b : Bool => b) false id⟩
    ⟨scanMachine readSymbol {} (fun s => !s.last)⟩ [] (by decide)
  norm_num [exceptionProb] at h

end Cslib.Crypto.Interaction.Tests
