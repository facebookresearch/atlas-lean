/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.MapFirst
import CSLibExt.Computability.Complexity.EncodingConverters

/-!
# Polynomially bounded iteration of bitstring algorithms

A step emits a tag bit followed by its result. A true tag feeds the result back
as the next input. A false tag returns it. The number of steps and the length
of each intermediate input are measured on the original input. Rewinding and
moving each intermediate word are included in the TM2 running time.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Iteration

open Turing Function MetaMathlibExt TM2Program TM2Composition ComplexityTheory

local notation "Bits" => List Bool

/-- A terminating sequence of calls to a bitstring step, with an upper bound on the
length of every argument passed to the step. -/
inductive Iterates (step : Bits → Bits) (bound : ℕ) : ℕ → Bits → Bits → Prop
  | halt {x y} : x.length ≤ bound → step x = false :: y → Iterates step bound 1 x y
  | next {i x y z} : x.length ≤ bound → step x = true :: y →
      Iterates step bound i y z → Iterates step bound (i + 1) x z

private abbrev side : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Unit
  initialState := ()
  m _ := .halt

variable {M : FinTM2}

private noncomputable abbrev st (S : ∀ k, List (M.Γ k)) (t : Bits) :=
  mkStk M side S (fun _ => []) t

private noncomputable abbrev drain (M : FinTM2) : CΛ M side := .inr (.inl false)
private noncomputable abbrev restore (M : FinTM2) : CΛ M side := .inr (.inl true)

variable (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

private noncomputable def program : CΛ M side → TM2.Stmt (CΓ M side) (CΛ M side) (Cσ M side)
  | .inl l => lift₁ M side (M.m l)
  | .inr (.inr (.inl none)) =>
    .pop (.inl M.k₁) (fun _ o => (M.initialState, (), o.map eo)) <|
      .branch (fun s => s.2.2.getD false)
        (.goto fun _ => drain M)
        (.load (fun _ => (M.initialState, (), none)) .halt)
  | .inr (.inl false) =>
    .pop (.inl M.k₁) (fun _ o => (M.initialState, (), o.map eo)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (tmp M side) (fun s => s.2.2.getD false) (.goto fun _ => drain M))
        (.goto fun _ => restore M)
  | .inr (.inl true) =>
    .pop (tmp M side) (fun _ o => (M.initialState, (), o)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inl M.k₀) (fun s => ei.symm (s.2.2.getD false)) (.goto fun _ => restore M))
        (.goto fun _ => .inl M.main)
  | .inr (.inr (.inl (some _))) => .halt
  | .inr (.inr (.inr _)) => .halt

private theorem run_step {s : ℕ} {c d : M.Cfg} (hr : Run M.m s c d) :
    Run (program ei eo) s (emb₁ (M₂ := side) c) (emb₁ (M₂ := side) d) := by
  apply iter_sim _ _ s _ _ hr
  rintro ⟨_ | l, v, S⟩ d hd
  · simp [TM2.step] at hd
  · simp only [TM2.step, Option.some.injEq] at hd
    subst d
    simp only [emb₁, lab₁, TM2.step, program]
    rw [stepAux_lift₁]
    rfl

-- A single active data stack inside the step machine.
private noncomputable abbrev one (k : M.K) (x : List (M.Γ k)) : ∀ k, List (M.Γ k) :=
  update (fun _ => []) k x

private theorem one_out (x : List (M.Γ M.k₁)) :
    one M.k₁ x = (haltList M x).stk := by
  funext k
  by_cases h : k = M.k₁
  · subst k
    simp [one, haltList]
  · simp [one, haltList, h]

private theorem drain_run (x t : Bits) (o : Option Bool) :
    Run (program ei eo) (x.length + 1)
      ⟨some (drain M), (M.initialState, (), o), st (one M.k₁ (x.map eo.symm)) t⟩
      ⟨some (restore M), (M.initialState, (), none), st (fun _ => []) (x.reverse ++ t)⟩ := by
  induction x generalizing t o with
  | nil =>
    apply Run.single
    simp [drain, restore, program, one, TM2.stepAux, st, mkStk, funext_iff]
  | cons b x ih =>
    have h := ih (b :: t) (some b)
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
    apply Run.head _ h
    simp [drain, program, TM2.step, TM2.stepAux, one, st, mkStk, funext_iff]

private theorem restore_run (x : Bits) (S : ∀ k, List (M.Γ k)) (o : Option Bool) :
    Run (program ei eo) (x.length + 1)
      ⟨some (restore M), (M.initialState, (), o), st S x⟩
      ⟨some (.inl M.main), (M.initialState, (), none),
        st (update S M.k₀ (x.reverse.map ei.symm ++ S M.k₀)) []⟩ := by
  induction x generalizing S o with
  | nil =>
    apply Run.single
    simp [restore, program, TM2.stepAux, st, mkStk, funext_iff]
  | cons b x ih =>
    have h := ih (update S M.k₀ (ei.symm b :: S M.k₀)) (some b)
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append, update_self, update_idem] at h ⊢
    apply Run.head _ h
    simp [restore, program, TM2.step, TM2.stepAux, st, mkStk, funext_iff]

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

private noncomputable abbrev machine : FinTM2 where
  K := CK M side
  k₀ := .inl M.k₀
  k₁ := .inl M.k₁
  Γ := CΓ M side
  Λ := CΛ M side
  main := .inl M.main
  σ := Cσ M side
  initialState := (M.initialState, (), none)
  Γk₀Fin := M.Γk₀Fin
  m := program ei eo

private theorem init_machine (x : List (M.Γ M.k₀)) :
    initList (machine ei eo) x = emb₁ (M₂ := side) (initList M x) :=
  initList_compTM (M₂ := side) eo x

private theorem halt_machine (x : List (M.Γ M.k₁)) :
    haltList (machine ei eo) x =
      ⟨none, (M.initialState, (), none), st (one M.k₁ x) []⟩ := by
  simp only [haltList, machine]
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = M.k₁
    · subst k
      simp [st, mkStk, one]
    · simp [st, mkStk, one, h]
  · simp [st, mkStk]
  · simp [st, mkStk]


private theorem dispatch (b : Bool) (x : Bits) :
    Run (program ei eo) 1 (emb₁ (M₂ := side) (haltList M ((b :: x).map eo.symm)))
      ⟨if b then some (drain M) else none, (M.initialState, (), if b then some true else none),
        st (one M.k₁ (x.map eo.symm)) []⟩ := by
  change Run _ 1 ⟨some (pop1 M side), (M.initialState, (), none),
      st (haltList M ((b :: x).map eo.symm)).stk []⟩ _
  rw [← one_out]
  cases b <;> apply Run.single <;>
    simp [program, drain, TM2.stepAux, st, mkStk, one, funext_iff]

private theorem finish {s : ℕ} {x y : Bits}
    (hr : Run M.m s (initList M (x.map ei.symm)) (haltList M ((false :: y).map eo.symm))) :
    Run (program ei eo) (s + 1)
      (initList (machine ei eo) (x.map ei.symm))
      (haltList (machine ei eo) (y.map eo.symm)) := by
  rw [init_machine, halt_machine]
  exact (run_step ei eo hr).trans (dispatch ei eo false y)

private theorem again {s : ℕ} {x y : Bits}
    (hr : Run M.m s (initList M (x.map ei.symm)) (haltList M ((true :: y).map eo.symm))) :
    Run (program ei eo) (s + 2 * y.length + 3)
      (initList (machine ei eo) (x.map ei.symm))
      (initList (machine ei eo) (y.map ei.symm)) := by
  have r₁ := (run_step ei eo hr).trans (dispatch ei eo true y)
  have r₂ := drain_run ei eo y [] (some true)
  have r₃ := restore_run ei eo y.reverse (fun _ => []) none
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil, update_nil_eq_initList]
    at r₂ r₃
  simp only [init_machine]
  exact ((r₁.trans r₂).trans r₃).of_eq (by omega)

private abbrev Raw (step : Bits → Bits) :=
  TM2ComputableInPolyTime (fun x : Bits => x) (fun x : Bits => x) step

private noncomputable def perCall {step : Bits → Bits} (h : Raw step) : Polynomial ℕ :=
  h.time + Polynomial.C 2 * midPoly h + Polynomial.C 3

private theorem iteration_run {step : Bits → Bits} (h : Raw step) {i bound : ℕ} {x z : Bits}
    (loop : Iterates step bound i x z) :
    RunLe (program h.inputAlphabet h.outputAlphabet) (i * (perCall h).eval bound)
      (initList (machine h.inputAlphabet h.outputAlphabet) (x.map h.inputAlphabet.symm))
      (haltList (machine h.inputAlphabet h.outputAlphabet) (z.map h.outputAlphabet.symm)) := by
  induction loop with
  | @halt x y hlen hstop =>
    obtain ⟨⟨s, hr⟩, ht⟩ := h.outputsFun x
    change Run h.tm.m s (initList h.tm _) (haltList h.tm ((step x).map h.outputAlphabet.symm)) at hr
    rw [hstop] at hr
    apply (finish h.inputAlphabet h.outputAlphabet hr).le
    have htime := (show s ≤ h.time.eval x.length from ht).trans (eval_mono h.time hlen)
    simp only [perCall, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, one_mul]
    omega
  | @next i x y z hlen hstep _ ih =>
    obtain ⟨⟨s, hr⟩, ht⟩ := h.outputsFun x
    change Run h.tm.m s (initList h.tm _) (haltList h.tm ((step x).map h.outputAlphabet.symm)) at hr
    rw [hstep] at hr
    have per : s + 2 * y.length + 3 ≤ (perCall h).eval bound := by
      have htime := (show s ≤ h.time.eval x.length from ht).trans (eval_mono h.time hlen)
      have hout := (Preimage.output_length_le h x).trans (eval_mono (midPoly h) hlen)
      change (step x).length ≤ _ at hout
      rw [hstep, List.length_cons] at hout
      simp only [perCall, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega
    exact (((again h.inputAlphabet h.outputAlphabet hr).le per).trans ih).mono
      (by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])

private noncomputable def computeFrom {α : Type} {step : Bits → Bits} (h : Raw step)
    (start f : α → Bits) (calls size : Polynomial ℕ)
    (runs : ∀ x, ∃ i ≤ calls.eval (start x).length,
      Iterates step (size.eval (start x).length) i (start x) (f x)) :
    TM2ComputableInPolyTime start (fun x : Bits => x) f where
  tm := machine h.inputAlphabet h.outputAlphabet
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := calls * (perCall h).comp size
  outputsFun x := by
    have cert := (Classical.choose_spec (runs x)).2
    have hrun := iteration_run h cert
    refine ⟨⟨Classical.choose hrun, (Classical.choose_spec hrun).2⟩, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_comp]
    exact (Classical.choose_spec hrun).1.trans
      (Nat.mul_le_mul_right _ (Classical.choose_spec (runs x)).1)

/-- A loop with a polynomial-time step, polynomially many calls, and polynomially
bounded intermediate input lengths computes its result in polynomial time. -/
theorem isPolyTime_of_iterates {step f : Bits → Bits} (hstep : IsPolyTime step)
    (calls size : Polynomial ℕ)
    (runs : ∀ x, ∃ i ≤ calls.eval x.length, Iterates step (size.eval x.length) i x (f x)) :
    IsPolyTime f := by
  obtain ⟨h⟩ := Preimage.raw_computable hstep
  obtain ⟨hin⟩ := tm2ComputableInPolyTime_comp DenseSAT.DecodeBits.computable
    (computeFrom h id f calls size runs)
  exact tm2ComputableInPolyTime_comp (f := f) (g := id) hin DenseSAT.EncodeBits.computable

/-- Run a loop from a polynomial-time initialization. The invariant and resource
bounds need only hold on reachable states, and are measured against the initial state. -/
theorem isPolyTime_of_iterates_from {α : Type} [BitstringEncoding α] {start f : α → Bits}
    {step : Bits → Bits} (hstart : IsPolyTime start) (hstep : IsPolyTime step)
    (calls size : Polynomial ℕ)
    (runs : ∀ x, ∃ i ≤ calls.eval (start x).length,
      Iterates step (size.eval (start x).length) i (start x) (f x)) :
    IsPolyTime f := by
  obtain ⟨h⟩ := Preimage.raw_computable hstep
  obtain ⟨hi⟩ := hstart
  obtain ⟨hs⟩ := tm2ComputableInPolyTime_comp (f := start) (g := id)
    hi DenseSAT.DecodeBits.computable
  let hs' : TM2ComputableInPolyTime BitstringEncoding.bitEncode start id :=
    { hs with outputsFun := hs.outputsFun }
  obtain ⟨hr⟩ := tm2ComputableInPolyTime_comp (f := id) (g := f) hs'
    (computeFrom h start f calls size runs)
  exact tm2ComputableInPolyTime_comp (f := f) (g := id) hr DenseSAT.EncodeBits.computable

end Cslib.Complexity.PolynomialEncoding.Iteration
