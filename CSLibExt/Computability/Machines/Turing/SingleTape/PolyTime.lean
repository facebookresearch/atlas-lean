/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.OfRecursive
public import CSLibExt.Computability.Machines.Turing.SingleTape.TM2Time
public import CSLibExt.Computability.Complexity.EncodingConverters
public import CSLibExt.Computability.Complexity.Host
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

/-!
# Polynomial time on CSLib's single-tape machines

The class `P` of this repository (`MetaMathlibExt.ComplexityTheory.P`) is defined with Mathlib's
multi-stack machines (`FinTM2`). This file shows that every problem in `P` is decided in
polynomial time by one of CSLib's single-tape machines (`Cslib.Complexity.SingleTapeP`): the
single-tape machine reads the input word bit by bit and halts on the one-cell tape holding the
answer bit, within a polynomial number of steps.

The single-tape decider is the one of `SingleTapeTM.OfTM2.deciderTM` (Mathlib's `TM2 → TM1 → TM0`
emulation run on a CSLib machine, behind an input adapter and an answer machine), and its running
time comes from the step-counted emulation `Cslib.Turing.TM2Time.exists_tm0_halt_of_tm2_halt`:
`t` multi-stack steps on an input of length `n` take at most `C t (n + C t + 1)` single-tape
steps. Before emulating, the multi-stack machine for the problem is

* preceded by a machine that reverses its raw input and drops the first bit
  (`Cslib.Turing.RevTail.computable`), because the emulation's start tape lays out the input stack
  bottom first, behind a flagged bottom cell, and by the converter from raw bits to the canonical
  encoding of a bit list (`DenseSAT.EncodeBits.computable`);
* restricted to finite stack alphabets, so that the single-tape machine's alphabet is finite: a
  run only ever holds input symbols and the finitely many values its statements push
  (`MetaMathlibExt.TM2Recursive.relevant`), and the restricted machine runs step for step like
  the original (private section "Finite stack alphabets").

## Main results

- `Cslib.Turing.RevTail.computable`: reversing a bit list and dropping its first bit is
  polynomial-time on raw bit lists.
- `Cslib.Turing.SingleTapeTM.OfTM2.deciderTM_outputsWithinTime`: a multi-stack machine that halts
  after `t` steps with a one-symbol answer gives a single-tape decider that halts within
  `C t (n + 1 + C t + 1) + 4` steps on an input of length `n`.
- `Cslib.Complexity.SingleTapeP`, `Cslib.Complexity.P_subset_singleTapeP`: every problem in `P` is
  decided in polynomial time by a single-tape machine.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013: the multi-stack
  analogue of Theorem 7.8 (the multitape-to-single-tape simulation of Theorem 3.13 is quadratic
  for `t(n) ≥ n`), and of the robustness of `P` across deterministic models (§7.2).
-/

@[expose] public section

set_option autoImplicit false

open Turing MetaMathlibExt MetaMathlibExt.TM2Program

namespace Cslib.Turing.RevTail

/-- Stacks of the reversal component: the input `X` and the output `O`. -/
inductive K | X | O
  deriving DecidableEq

/-- The two stacks. -/
instance K.instFintype : Fintype K := ⟨{.X, .O}, fun k ↦ by cases k <;> simp⟩

/-- Labels of the reversal component: move the input onto the output, drop one symbol, done. -/
inductive L | mv | drop | done
  deriving DecidableEq

/-- The three labels. -/
instance L.instFintype : Fintype L := ⟨{.mv, .drop, .done}, fun l ↦ by cases l <;> simp⟩

/-- Move the bits of `X` onto `O` (reversing them), pop `O` once, halt. -/
def prog : L → TM2.Stmt (fun _ : K ↦ Bool) L Bool
  | .mv => moveB .X .O some id .mv .drop
  | .drop => .pop .O (fun s _ ↦ s) (.goto fun _ ↦ .done)
  | .done => .halt

/-- The reversal component. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ ↦ Bool
  L := L
  prog := prog
  ks := [.X, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- The reversal component turns `x` into `x.reverse.tail` in `|x| + 2` steps. -/
theorem run (x : List Bool) : ∃ v S', RunLe comp.prog (x.length + 2)
    ⟨some L.mv, false, Function.update (fun _ ↦ []) K.X (x.map id)⟩ ⟨some L.done, v, S'⟩ ∧
      S' K.O = x.reverse.tail.map (Equiv.refl Bool).symm := by
  obtain ⟨v₁, S₁, r₁, h₁a, h₁b, -⟩ := moveB_run (M := comp.prog) (self := L.mv) (next := L.drop)
    (a := K.X) (b := K.O) (d := some) (g := id) rfl (by decide) x (x.map id) []
    false (Function.update (fun _ ↦ []) K.X (x.map id)) (by simp) (by simp [IsBitBlock])
    (by simp [EndsBitBlock])
  refine ⟨v₁, Function.update S₁ K.O (S₁ K.O).tail, ⟨x.length + 2, le_refl _, ?_⟩, ?_⟩
  · refine r₁.trans (Run.single ?_)
    simp only [comp, prog, TM2.stepAux]
  · simp [h₁b, List.tail_reverse]

/-- **Reversing and dropping the first bit is polynomial-time** on raw bit lists. -/
noncomputable def computable :
    TM2ComputableInPolyTime (fun l : List Bool ↦ l) (fun l : List Bool ↦ l)
      (fun x : List Bool ↦ x.reverse.tail) :=
  Cslib.Complexity.Host.reduction (c := comp) (cX := K.X) (cO := K.O) (gX := id)
    (start := L.mv) (done := L.done) (Equiv.refl Bool) _ (Polynomial.X + Polynomial.C 2) rfl
    fun x ↦ by simpa using run x

end Cslib.Turing.RevTail

namespace Cslib.Turing.SingleTapeTM.OfTM2

open Relation MetaMathlibExt.TM2Recursive Cslib.Turing.TM2Time
open scoped MetaMathlibExt.TM2ToTM0

section Timed

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)] (e : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool)

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- `answerTM` turns a one-cell tape into the answer bit of that cell in one step. -/
theorem answerTM_outputsWithinTime (x : NonBlank (TM2to1.Γ' tm.K tm.Γ)) :
    (answerTM tm e e₁).OutputsWithinTime [x] [inCell tm e (cellAnswer tm e₁ x)] 1 :=
  RelatesWithinSteps.single rfl

/-- **The decider within time.** If `tm` halts after `t` steps on the input stack
`w.reverse ++ [true]` with the single output symbol for the bit `b`, the decider outputs, on the
input word `w`, the input-bit cell for `b`, within `C t (|w| + 1 + C t + 1) + 4` steps, where
`C = emulationConstant tm`. -/
theorem deciderTM_outputsWithinTime {w : List Bool} (b : Bool) {t : ℕ}
    (h : (flip bind tm.step)^[t] (some (initList tm ((w.reverse ++ [true]).map e.symm))) =
      some (haltList tm [e₁.symm b])) :
    (deciderTM tm e e₁).OutputsWithinTime (w.map (inCell tm e)) [inCell tm e b]
      (emulationConstant tm * t * (w.length + 1 + emulationConstant tm * t + 1) + 4) := by
  obtain ⟨c₁, n, hTr, hr, hh, hn⟩ := exists_tm0_halt_of_tm2_halt tm _ h rfl
  generalize hcfg : haltList tm [e₁.symm b] = c at hTr
  obtain ⟨q, v, S⟩ := c
  cases hTr with
  | mk L' hL' =>
    have hS : ∀ k, (S k).length ≤ 1 := fun k ↦ by
      have hk := congrArg (fun c : tm.Cfg ↦ (c.stk k).length) hcfg
      by_cases hk₁ : k = tm.k₁
      · subst hk₁
        simp [haltList] at hk
        omega
      · simp [haltList, hk₁] at hk
        omega
    have ht := addBottom_eq_of_length_le_one tm hS hL'
    let cell : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
      ⟨(true, fun k ↦ (S k).head?), fun h ↦ Bool.noConfusion (congrArg Prod.fst h)⟩
    have hsim : (emuTM tm).OutputsWithinTime (botCell tm e :: w.map (inCell tm e)) [cell]
        (n + 1) := by
      refine outputsWithinTime_ofTM0 _ _ _ ?_ hh ?_
      · rw [map_val_botCell_cons]
        exact hr
      · change Tape.mk' ∅ (TM2to1.addBottom L') = _
        rw [ht]
        rfl
    have hans : cellAnswer tm e₁ cell = b := by
      have hk₁ : S tm.k₁ = [e₁.symm b] := by
        have := congrArg (fun c : tm.Cfg ↦ c.stk tm.k₁) hcfg
        simpa [haltList] using this.symm
      cases b <;> simp [cellAnswer, cell, hk₁]
    have hrun := ((consComputer_outputsWithinTime _ _).compComputer hsim).compComputer
      (answerTM_outputsWithinTime tm e e₁ cell)
    rw [hans] at hrun
    refine RelatesWithinSteps.mono ?_ hrun
    simp only [List.length_map, List.length_append, List.length_reverse,
      List.length_singleton] at hn
    omega

end Timed

end Cslib.Turing.SingleTapeTM.OfTM2

/-! ### Finite stack alphabets

A `FinTM2` only requires its input alphabet to be finite. A run, though, only ever holds input
symbols and the values pushed by the finitely many statements of the program
(`MetaMathlibExt.TM2Recursive.relevant`), so restricting every stack to those symbols (and the
whole output alphabet) loses nothing: the restricted machine runs step for step like the original
(`liftCfg` maps its configurations into the original's, injectively and commuting with `step`).
These declarations are private: they are an implementation step of `P_subset_singleTapeP`. -/

namespace Cslib.Turing.FinTM2Restrict

open _root_.Turing MetaMathlibExt.TM2Recursive

section Machine

variable (tm : FinTM2)

/-- The symbols stack `k` of the restricted machine can hold: the relevant symbols (pushed by
the program, or on the input stack), and every symbol of the output stack. -/
private def alphabet (k : tm.K) : Set (tm.Γ k) :=
  relevant tm k ∪ {_x | k = tm.k₁}

/-- Every input symbol is in the restricted input alphabet. -/
private theorem mem_alphabet_k₀ (x : tm.Γ tm.k₀) : x ∈ alphabet tm tm.k₀ :=
  Set.mem_union_left _ (Set.mem_union_right _ rfl)

/-- Every output symbol is in the restricted output alphabet. -/
private theorem mem_alphabet_k₁ (x : tm.Γ tm.k₁) : x ∈ alphabet tm tm.k₁ :=
  Set.mem_union_right _ rfl

/-- The restricted alphabet is finite when the output alphabet is. -/
private theorem alphabet_finite [Finite (tm.Γ tm.k₁)] (k : tm.K) : (alphabet tm k).Finite := by
  refine (relevant_finite tm k).union ?_
  by_cases h : k = tm.k₁
  · subst h
    exact Set.toFinite _
  · simp [h]

/-- A statement of `tm`, acting on the restricted stacks; it is defined for statements whose
pushed symbols lie in `alphabet`. -/
private def stmt : (q : TM2.Stmt tm.Γ tm.Λ tm.σ) → (∀ k, pushes tm k q ⊆ alphabet tm k) →
    TM2.Stmt (fun k ↦ alphabet tm k) tm.Λ tm.σ
  | .push k f q, h => .push k (fun v ↦ ⟨f v, h k (Set.mem_union_left _ (by simp))⟩)
      (stmt q fun k' ↦ Set.subset_union_right.trans (h k'))
  | .peek k f q, h => .peek k (fun v o ↦ f v (o.map Subtype.val)) (stmt q h)
  | .pop k f q, h => .pop k (fun v o ↦ f v (o.map Subtype.val)) (stmt q h)
  | .load a q, h => .load a (stmt q h)
  | .branch f q₁ q₂, h => .branch f (stmt q₁ fun k ↦ Set.subset_union_left.trans (h k))
      (stmt q₂ fun k ↦ Set.subset_union_right.trans (h k))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- Every symbol the program pushes onto stack `k` is in `alphabet tm k`. -/
private theorem pushes_subset_alphabet (l : tm.Λ) (k : tm.K) :
    pushes tm k (tm.m l) ⊆ alphabet tm k :=
  (Set.subset_iUnion (fun l ↦ pushes tm k (tm.m l)) l).trans
    (Set.subset_union_left.trans Set.subset_union_left)

/-- The machine `tm` with each stack `k` restricted to `alphabet tm k`: same stacks, labels,
states, main label and input/output stacks, and the program read through `stmt`. It is
reducible, so that `(restrict tm).K` and `(restrict tm).Γ k` unfold to `tm.K` and
`alphabet tm k` for simp and instance search. -/
private abbrev restrict : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ k := alphabet tm k
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := @Fintype.ofEquiv _ _ tm.Γk₀Fin (Equiv.subtypeUnivEquiv (mem_alphabet_k₀ tm)).symm
  m l := stmt tm (tm.m l) (pushes_subset_alphabet tm l)

/-- The restricted stack alphabets are finite when the output alphabet of `tm` is. -/
private instance finite_Γ [Finite (tm.Γ tm.k₁)] (k : (restrict tm).K) :
    Finite ((restrict tm).Γ k) :=
  (alphabet_finite tm k).to_subtype

/-- The input alphabet is unchanged. -/
private def inputEquiv : (restrict tm).Γ (restrict tm).k₀ ≃ tm.Γ tm.k₀ :=
  Equiv.subtypeUnivEquiv (mem_alphabet_k₀ tm)

/-- The output alphabet is unchanged. -/
private def outputEquiv : (restrict tm).Γ (restrict tm).k₁ ≃ tm.Γ tm.k₁ :=
  Equiv.subtypeUnivEquiv (mem_alphabet_k₁ tm)

/-! ### Configurations -/

/-- Restricted stacks, read as stacks of `tm`. -/
private def liftStk (S : ∀ k, List ((restrict tm).Γ k)) : ∀ k, List (tm.Γ k) :=
  fun k ↦ (S k).map Subtype.val

/-- A configuration of `restrict tm`, read as a configuration of `tm`. -/
private def liftCfg (c : (restrict tm).Cfg) : tm.Cfg :=
  TM2.Cfg.mk c.l c.var (liftStk tm c.stk)

/-- Distinct configurations of `restrict tm` are distinct configurations of `tm`. -/
private theorem liftCfg_injective : Function.Injective (liftCfg tm) := by
  rintro ⟨l, v, S⟩ ⟨l', v', S'⟩ h
  obtain ⟨rfl, rfl, h⟩ := TM2.Cfg.mk.inj h
  obtain rfl : S = S' :=
    funext fun k ↦ List.map_injective_iff.mpr Subtype.val_injective (congrFun h k)
  rfl

/-- Reading restricted stacks commutes with replacing one of them. -/
private theorem liftStk_update (S : ∀ k, List ((restrict tm).Γ k)) (k : tm.K)
    (l : List ((restrict tm).Γ k)) :
    liftStk tm (Function.update S k l) = Function.update (liftStk tm S) k (l.map Subtype.val) := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp [liftStk]
  · simp [liftStk, Function.update_of_ne h]

/-- Running a restricted statement is running the statement of `tm`. -/
private theorem liftCfg_stepAux (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : ∀ k, pushes tm k q ⊆ alphabet tm k)
    (v : tm.σ) (S : ∀ k, List ((restrict tm).Γ k)) :
    liftCfg tm (TM2.stepAux (stmt tm q hq) v S) = TM2.stepAux q v (liftStk tm S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [stmt, TM2.stepAux]
    rw [ih, liftStk_update]
    rfl
  | peek k f q ih =>
    have hk : (liftStk tm S k).head? = (S k).head?.map Subtype.val := List.head?_map
    simp only [stmt, TM2.stepAux, hk]
    exact ih _ _ _
  | pop k f q ih =>
    have hk : (liftStk tm S k).head? = (S k).head?.map Subtype.val := List.head?_map
    have ht : (liftStk tm S k).tail = (S k).tail.map Subtype.val := List.map_tail.symm
    simp only [stmt, TM2.stepAux, hk, ht]
    refine (ih hq _ _).trans ?_
    rw [liftStk_update]
  | load a q ih =>
    simp only [stmt, TM2.stepAux]
    exact ih _ _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f v
    · simp only [stmt, TM2.stepAux, hf, Bool.cond_false]
      exact ih₂ _ _ _
    · simp only [stmt, TM2.stepAux, hf, Bool.cond_true]
      exact ih₁ _ _ _
  | goto f => rfl
  | halt => rfl

/-- One step of `restrict tm` is one step of `tm`. -/
private theorem step_liftCfg (c : (restrict tm).Cfg) :
    tm.step (liftCfg tm c) = ((restrict tm).step c).map (liftCfg tm) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
    simp only [FinTM2.step, TM2.step]
    exact congrArg some (liftCfg_stepAux tm (tm.m l) (pushes_subset_alphabet tm l) v S).symm

/-- `n` steps of `restrict tm` are `n` steps of `tm`. -/
private theorem iterate_step_liftCfg (n : ℕ) (o : Option (restrict tm).Cfg) :
    (flip bind tm.step)^[n] (o.map (liftCfg tm)) =
      ((flip bind (restrict tm).step)^[n] o).map (liftCfg tm) := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    cases o with
    | none => rfl
    | some c => exact step_liftCfg tm c

/-- The initial configurations correspond. -/
private theorem liftCfg_initList (s : List ((restrict tm).Γ (restrict tm).k₀)) :
    liftCfg tm (initList (restrict tm) s) = initList tm (s.map Subtype.val) := by
  simp only [liftCfg, initList]
  congr
  funext k
  by_cases hk : k = tm.k₀
  · subst hk
    simp [liftStk]
  · simp [liftStk, hk]

/-- The halting configurations correspond. -/
private theorem liftCfg_haltList (s : List ((restrict tm).Γ (restrict tm).k₁)) :
    liftCfg tm (haltList (restrict tm) s) = haltList tm (s.map Subtype.val) := by
  simp only [liftCfg, haltList]
  congr
  funext k
  by_cases hk : k = tm.k₁
  · subst hk
    simp [liftStk]
  · simp [liftStk, hk]

/-- `restrict tm` outputs what `tm` outputs on the corresponding input, within the same number
of steps. (A `def`, because `TM2OutputsInTime` is data.) -/
private def outputsInTime {l : List ((restrict tm).Γ (restrict tm).k₀)}
    {l' : Option (List ((restrict tm).Γ (restrict tm).k₁))} {m : ℕ}
    (h : TM2OutputsInTime tm (l.map Subtype.val) (l'.map (List.map Subtype.val)) m) :
    TM2OutputsInTime (restrict tm) l l' m where
  steps := h.steps
  evals_in_steps := by
    have hrun := iterate_step_liftCfg tm h.steps (some (initList (restrict tm) l))
    rw [Option.map_some, liftCfg_initList, h.evals_in_steps] at hrun
    refine Option.map_injective (liftCfg_injective tm) (hrun.symm.trans ?_)
    cases l' with
    | none => rfl
    | some l' => exact congrArg some (liftCfg_haltList tm l').symm
  steps_le_m := h.steps_le_m

end Machine

/-! ### Polynomial time machines with finite alphabets -/

section PolyTime

variable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}

/-- A polynomial time machine for `f`, with its stacks restricted to `alphabet`: same time
polynomial, alphabets identified through `inputEquiv` and `outputEquiv`. -/
private def restrictPolyTime (T : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInPolyTime ea eb f where
  tm := restrict T.tm
  inputAlphabet := (inputEquiv T.tm).trans T.inputAlphabet
  outputAlphabet := (outputEquiv T.tm).trans T.outputAlphabet
  time := T.time
  outputsFun a := outputsInTime T.tm (by
    simp only [Option.map_some, List.map_map]
    exact T.outputsFun a)

/-- The machine of `restrictPolyTime T` is `restrict T.tm`. -/
@[simp]
private theorem restrictPolyTime_tm (T : TM2ComputableInPolyTime ea eb f) :
    (restrictPolyTime T).tm = restrict T.tm := rfl

/-- `restrictPolyTime T` has the time polynomial of `T`. -/
@[simp]
private theorem restrictPolyTime_time (T : TM2ComputableInPolyTime ea eb f) :
    (restrictPolyTime T).time = T.time := rfl

/-- **Finite alphabets without loss of generality.** A function computable in polynomial time
with a finite output alphabet `βΓ` is computable in polynomial time by a machine all of whose
stack alphabets are finite (the witness is `restrictPolyTime`, which keeps the time polynomial:
`restrictPolyTime_time`). The output
alphabet of any such machine is equivalent to `βΓ`, so finiteness of `βΓ` is necessary. -/
private theorem exists_finite_alphabets [Finite βΓ]
    (h : Nonempty (TM2ComputableInPolyTime ea eb f)) :
    ∃ T : TM2ComputableInPolyTime ea eb f, ∀ k, Finite (T.tm.Γ k) := by
  obtain ⟨T⟩ := h
  have : Finite (T.tm.Γ T.tm.k₁) := Finite.of_equiv _ T.outputAlphabet.symm
  exact ⟨restrictPolyTime T, finite_Γ T.tm⟩

end PolyTime

end Cslib.Turing.FinTM2Restrict

namespace Cslib.Complexity

open Relation MetaMathlibExt.ComplexityTheory Cslib.Turing Cslib.Turing.SingleTapeTM
  Cslib.Turing.SingleTapeTM.OfTM2 Cslib.Turing.TM2Time
open scoped Cslib.Turing.SingleTapeTM.OfTM2

attribute [local instance] FinTM2.kFin

/-- **Polynomial time on single-tape machines.** A decision problem `L` is in `SingleTapeP` when a
CSLib single-tape machine over a finite alphabet, reading the input word `w` through an injective
copy `ι` of the bits, halts on the one-cell tape `ι (L w)` within `p |w|` steps, for a polynomial
`p`. -/
def SingleTapeP : DecisionComplexityClass :=
  {L | ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ (tm : SingleTapeTM Symbol) (p : Polynomial ℕ),
      ∀ w : List Bool, tm.OutputsWithinTime (w.map ι) [ι (L w)] (p.eval w.length)}

/-- **Problems in `P` are decided in polynomial time by single-tape machines**: the multi-stack
machine of `P`, after the input reversal and restricted to finite alphabets, is emulated within
quadratic overhead. -/
theorem P_subset_singleTapeP : P ⊆ SingleTapeP := by
  intro L hL
  obtain ⟨T₀⟩ := hL
  obtain ⟨T, hfin⟩ := FinTM2Restrict.exists_finite_alphabets ⟨TM2Composition.compComputable
    (TM2Composition.compComputable RevTail.computable DenseSAT.EncodeBits.computable) T₀⟩
  have : ∀ k, Fintype (T.tm.Γ k) := fun k ↦ @Fintype.ofFinite _ (hfin k)
  let C := emulationConstant T.tm
  let q : Polynomial ℕ := T.time.comp (Polynomial.X + 1)
  refine ⟨_, inferInstance, inferInstance, inCell T.tm T.inputAlphabet,
    inCell_injective T.tm T.inputAlphabet, deciderTM T.tm T.inputAlphabet T.outputAlphabet,
    Polynomial.C C * q * (Polynomial.X + 1 + Polynomial.C C * q + 1) + 4, fun w ↦ ?_⟩
  obtain ⟨⟨t, ht⟩, htle⟩ := T.outputsFun (w.reverse ++ [true])
  have hx : (w.reverse ++ [true]).reverse.tail = w := by simp
  have h' : (flip bind T.tm.step)^[t]
      (some (initList T.tm ((w.reverse ++ [true]).map T.inputAlphabet.symm))) =
      some (haltList T.tm [T.outputAlphabet.symm (L w)]) := by
    refine ht.trans ?_
    simp only [Function.comp_apply, id, hx]
    rfl
  refine RelatesWithinSteps.mono ?_
    (deciderTM_outputsWithinTime T.tm T.inputAlphabet T.outputAlphabet (L w) h')
  have hq : q.eval w.length = T.time.eval (w.length + 1) := by simp [q]
  have ht' : t ≤ q.eval w.length := by
    rw [hq]
    simpa using htle
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  gcongr

end Cslib.Complexity
