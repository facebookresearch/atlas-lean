/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Finite-state transductions of bitstrings

A scan with finite control and fixed output words has a polynomial-time
implementation on the canonical bitstring-encoded TM2 model.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.BitScan

open MetaMathlibExt ComplexityTheory TM2Program Turing Function

/-- Run a finite-state pass that emits a word at each transition and once at the end. -/
def scan {Q : Type} (step : Q → Bool → Q × List Bool) (finish : Q → List Bool)
    (q : Q) : List Bool → List Bool
  | [] => finish q
  | b :: x => (step q b).2 ++ scan step finish (step q b).1 x

/-- A finite-state scan stores output in reverse order and reverses it once at the end.
Each transition emits a bounded number of bits because the state and input alphabets are finite. -/
theorem polyScan {Q : Type} [Finite Q]
    (step : Q → Bool → Q × List Bool) (finish : Q → List Bool) (q₀ : Q) :
    IsPolyTime (scan step finish q₀) := by
  classical
  let := Fintype.ofFinite Q
  let prog : Q ⊕ Bool → TM2.Stmt (fun _ : Fin 3 => Bool) (Q ⊕ Bool) Bool
    | .inl q =>
      .peek 0 (fun _ o => o.isNone) <| .branch id
        (emit 1 (finish q) (.inr false))
        (.pop 0 (fun _ o => o.getD false) <| .branch id
          (emit 1 (step q true).2 (.inl (step q true).1))
          (emit 1 (step q false).2 (.inl (step q false).1)))
    | .inr false => moveB 1 2 some id (.inr false) (.inr true)
    | .inr true => .halt
  let comp : Host.Comp := {
    K := Fin 3, Γ := fun _ => Bool, L := Q ⊕ Bool, prog := prog,
    ks := [0, 1, 2], ks_nodup := by decide, mem_ks := by decide }
  let st (x r o : List Bool) : Fin 3 → List Bool := ![x, r, o]
  have up0 (x r o l : List Bool) : update (st x r o) 0 l = st l r o := by
    funext k
    fin_cases k <;> rfl
  have up1 (x r o l : List Bool) : update (st x r o) 1 l = st x l o := by
    funext k
    fin_cases k <;> rfl
  have hr (x : List Bool) (q : Q) (v : Bool) (r : List Bool) :
      Run prog (x.length + 1) ⟨some (.inl q), v, st x r []⟩
        ⟨some (.inr false), true, st [] ((scan step finish q x).reverse ++ r) []⟩ := by
    induction x generalizing q v r with
    | nil =>
      apply Run.single
      simp [prog, TM2.stepAux, emit, stepAux_pushList, scan, up1, st]
    | cons b x ih =>
      have h := ih (step q b).1 b ((step q b).2.reverse ++ r)
      simp only [scan, List.reverse_append, List.append_assoc]
      refine Run.head ?_ h
      cases b <;>
        simp [TM2.step, prog, TM2.stepAux, emit, stepAux_pushList, up0, up1, st]
  let B := Finset.univ.sup fun q : Q =>
    max (finish q).length (max (step q true).2.length (step q false).2.length)
  have bound (x : List Bool) (q : Q) : (scan step finish q x).length ≤ (x.length + 1) * B := by
    have h (q : Q) : max (finish q).length
        (max (step q true).2.length (step q false).2.length) ≤ B :=
      Finset.le_sup (f := fun q : Q =>
        max (finish q).length (max (step q true).2.length (step q false).2.length))
        (Finset.mem_univ q)
    induction x generalizing q with
    | nil => simpa [scan] using (le_max_left _ _).trans (h q)
    | cons b x ih =>
      have hb : (step q b).2.length ≤ B := by cases b <;> have := h q <;> omega
      have hi := ih (step q b).1
      simp only [scan, List.length_append, List.length_cons, Nat.succ_mul] at hi ⊢
      omega
  apply Host.isPolyTime_reduction (c := comp) (cX := 0) (cO := 2)
    (gX := id) (start := .inl q₀) (done := .inr true) (Equiv.refl Bool) _
    ((Polynomial.X + 1) * (Polynomial.C B + 1) + 1) rfl
  intro x
  let y := scan step finish q₀ x
  have h₁ := hr x q₀ false []
  simp only [List.append_nil] at h₁
  obtain ⟨v, S, h₂, _, ho, _⟩ := moveB_run (M := prog)
    (self := Sum.inr false) (next := .inr true) (a := (1 : Fin 3)) (b := 2)
    (d := some) (g := id) rfl (by decide) y.reverse y.reverse [] true
    (st [] y.reverse []) (by simp [st]) rfl rfl
  have hi : update (fun _ : Fin 3 => ([] : List Bool)) 0 x = st x [] [] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨v, S, ?_, ?_⟩
  · change RunLe prog _ ⟨_, _, update _ 0 (x.map id)⟩ _
    rw [List.map_id, hi]
    apply (h₁.trans h₂).le
    have := bound x q₀
    simp [y, Nat.mul_add] at *
    omega
  · simpa [y, st, comp] using ho

end Cslib.Complexity.PolynomialEncoding.BitScan
