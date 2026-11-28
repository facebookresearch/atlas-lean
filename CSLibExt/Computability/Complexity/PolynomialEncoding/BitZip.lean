/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Host
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine
import CSLibExt.Computability.Complexity.Karp.SubsetSumDigits
import CSLibExt.Computability.Complexity.BoolClosure

/-!
# Finite-state decisions on two input words

Scan two words in parallel, exposing an end marker for the shorter word.
This gives equality on raw words and binary comparison on actual input
representations, with one component-machine step per pair of positions.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.BitZip

open Turing Function MetaMathlibExt TM2Program ComplexityTheory

local notation "Bits" => List Bool

/-- Advance a finite control on two words. A missing bit is presented as `none`. -/
def fold {Q : Type} (step : Q → Option Bool → Option Bool → Q) (q : Q) :
    Bits → Bits → Q
  | [], [] => q
  | [], b :: ys => fold step (step q none (some b)) [] ys
  | a :: xs, [] => fold step (step q (some a) none) xs []
  | a :: xs, b :: ys => fold step (step q (some a) (some b)) xs ys

private abbrev Label (Q : Type) := Q ⊕ Bool
private abbrev Stmt (Q : Type) := TM2.Stmt (fun _ : Bool => Bool) (Label Q) Bool

private def right {Q : Type} (step : Q → Option Bool → Option Bool → Q)
    (finish : Q → Bool) (q : Q) (a : Option Bool) : Stmt Q :=
  .peek true (fun _ ob => ob.isSome) <| .branch id
    (.pop true (fun _ ob => ob.getD false) <| .branch id
      (.goto fun _ => .inl (step q a (some true))) (.goto fun _ => .inl (step q a (some false))))
    (.goto fun _ => if a.isSome then .inl (step q a none) else .inr (finish q))

private def prog {Q : Type} (step : Q → Option Bool → Option Bool → Q)
    (finish : Q → Bool) : Label Q → Stmt Q
  | .inr _ => .halt
  | .inl q => .peek false (fun _ oa => oa.isSome) <| .branch id
      (.pop false (fun _ oa => oa.getD false) <| .branch id
        (right step finish q (some true)) (right step finish q (some false)))
      (right step finish q none)

private def st (a b : Bits) : Bool → Bits
  | false => a
  | true => b

private theorem run {Q : Type} (step : Q → Option Bool → Option Bool → Q)
    (finish : Q → Bool) (q : Q) (x y : Bits) (v : Bool) :
    ∃ z, RunLe (prog step finish) (x.length + y.length + 1)
      ⟨some (.inl q), v, st x y⟩ ⟨some (.inr (finish (fold step q x y))), z, st [] []⟩ := by
  cases x with
  | nil =>
    cases y with
    | nil =>
      rw [fold]
      exact ⟨false, (Run.single (by rfl)).le le_rfl⟩
    | cons b ys =>
      obtain ⟨z, h⟩ := run step finish (step q none (some b)) [] ys b
      have h₁ : Run (prog step finish) 1 ⟨some (.inl q), v, st [] (b :: ys)⟩
          ⟨some (.inl (step q none (some b))), b, st [] ys⟩ := by
        apply Run.single
        cases b <;> simp [prog, right, TM2.stepAux, st, funext_iff]
      rw [fold]
      refine ⟨z, ((h₁.le (show 1 ≤ 1 by decide)).trans h).mono ?_⟩
      simp; omega
  | cons a xs =>
    cases y with
    | nil =>
      obtain ⟨z, h⟩ := run step finish (step q (some a) none) xs [] false
      have h₁ : Run (prog step finish) 1 ⟨some (.inl q), v, st (a :: xs) []⟩
          ⟨some (.inl (step q (some a) none)), false, st xs []⟩ := by
        apply Run.single
        cases a <;> simp [prog, right, TM2.stepAux, st, funext_iff]
      rw [fold]
      refine ⟨z, ((h₁.le (show 1 ≤ 1 by decide)).trans h).mono ?_⟩
      simp; omega
    | cons b ys =>
      obtain ⟨z, h⟩ := run step finish (step q (some a) (some b)) xs ys b
      have h₁ : Run (prog step finish) 1 ⟨some (.inl q), v, st (a :: xs) (b :: ys)⟩
          ⟨some (.inl (step q (some a) (some b))), b, st xs ys⟩ := by
        apply Run.single
        cases a <;> cases b <;> simp [prog, right, TM2.stepAux, st, funext_iff]
      rw [fold]
      refine ⟨z, ((h₁.le (show 1 ≤ 1 by decide)).trans h).mono ?_⟩
      simp; omega
termination_by x.length + y.length

/-- A finite-state two-word decision procedure runs in polynomial time on the
framed pair representation, including input conversion and workspace cleanup. -/
theorem polyFold {Q : Type} [Finite Q] (step : Q → Option Bool → Option Bool → Q)
    (finish : Q → Bool) (q : Q) :
    IsPolyTime (fun p : Bits × Bits => finish (fold step q p.1 p.2)) := by
  classical
  let _ := Fintype.ofFinite Q
  let c : Host.Comp := {
    K := Bool
    Γ := fun _ => Bool
    L := Label Q
    prog := prog step finish
    ks := [false, true]
    ks_nodup := by decide
    mem_ks := by decide }
  apply Host.isPolyTime_verifier (c := c) (cX := false) (cW := true) (gX := id) (gW := id)
    (start := .inl q) (yes := .inr true) (no := .inr false)
    (fun x y => finish (fold step q x y)) (Polynomial.X + 1) (by intro h; cases h)
    (by intro h; cases h) rfl rfl
  intro x y
  obtain ⟨z, h⟩ := run step finish q x y false
  have hs : update (update (fun _ : Bool => ([] : Bits)) false (x.map id)) true (y.map id) =
      st x y := by funext k; cases k <;> simp [st]
  rw [hs]
  generalize he : finish (fold step q x y) = b at h ⊢
  cases b <;> exact ⟨z, _, by simpa [c] using h⟩

private def eqStep (q : Bool) (x y : Option Bool) := q && x == y

private theorem fold_eq (q : Bool) (x y : Bits) : fold eqStep q x y = (q && x == y) := by
  match x, y with
  | [], [] => simp [fold]
  | [], b :: ys => simp [fold, eqStep, fold_eq false [] ys]
  | a :: xs, [] => simp [fold, eqStep, fold_eq false xs []]
  | a :: xs, b :: ys =>
    rw [fold]
    rw [fold_eq _ xs ys]
    cases q <;> cases a <;> cases b <;> simp [eqStep]
termination_by x.length + y.length

/-- Equality of two complete raw bitstrings. -/
theorem polyEq : IsPolyTime (fun p : Bits × Bits => p.1 == p.2) := by
  simpa only [fold_eq, id_eq, Bool.true_and] using polyFold eqStep id true

private def orderStep (tie : Bool) (a b : Option Bool) :=
  if a.getD false = b.getD false then tie else b.getD false

private def answer (tie : Bool) (m n : ℕ) := decide (m < n ∨ m = n ∧ tie)

private theorem answer_bit (tie a b : Bool) (m n : ℕ) :
    answer tie (a.toNat + 2 * m) (b.toNat + 2 * n) =
      answer (if a = b then tie else b) m n := by
  apply Bool.eq_iff_iff.mpr
  cases tie <;> cases a <;> cases b <;> simp [answer, Bool.toNat] <;> omega

private theorem fold_order (tie : Bool) (x y : Bits) : fold orderStep tie x y =
    answer tie (TM2Recursive.bitsVal x) (TM2Recursive.bitsVal y) := by
  match x, y with
  | [], [] => rw [fold]; cases tie <;> rfl
  | [], b :: ys =>
    rw [fold, fold_order _ [] ys]
    simpa [orderStep] using (answer_bit tie false b 0 (TM2Recursive.bitsVal ys)).symm
  | a :: xs, [] =>
    rw [fold, fold_order _ xs []]
    simpa [orderStep] using (answer_bit tie a false (TM2Recursive.bitsVal xs) 0).symm
  | a :: xs, b :: ys =>
    rw [fold, fold_order _ xs ys]
    simpa [orderStep] using
      (answer_bit tie a b (TM2Recursive.bitsVal xs) (TM2Recursive.bitsVal ys)).symm
termination_by x.length + y.length

/-- Compare binary integers represented by raw little-endian words. High
zero bits are allowed, and an empty word represents zero. -/
theorem polyBitsLE : IsPolyTime
    (fun p : Bits × Bits => decide (TM2Recursive.bitsVal p.1 ≤ TM2Recursive.bitsVal p.2)) := by
  have e (x y : Bits) : fold orderStep true x y =
      decide (TM2Recursive.bitsVal x ≤ TM2Recursive.bitsVal y) := by
    rw [fold_order]
    simp [answer, le_iff_lt_or_eq]
  simpa only [id_eq, e] using polyFold orderStep id true

/-- Compare arbitrary natural-number payloads as decoded by the repository's
total decoder, including the implicit high one on noncanonical inputs. -/
theorem polyDecodedLE : IsPolyTime
    (fun p : Bits × Bits =>
      decide (Computability.decodeNat p.1 ≤ Computability.decodeNat p.2)) := by
  let n := FramedCNF.NormalizeMachine.isPolyTime_normalizeNat
  have hn := (((n.map_fst.comp isPolyTime_swap).comp n.map_fst).comp
    isPolyTime_swap).comp polyBitsLE
  simpa only [Function.comp_def, Prod.swap, FramedCNF.normalizeNat_eq_encode_decode,
    TM2Recursive.bitsVal_encodeNat] using hn

end Cslib.Complexity.PolynomialEncoding.BitZip
