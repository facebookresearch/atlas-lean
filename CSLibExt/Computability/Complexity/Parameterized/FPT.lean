/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Defs
public import MathlibExt.Computability.TuringMachine.Composition

/-!
# Reductions out of FPT

An FPT decider can reduce its input to either of two fixed target instances.
The postprocessing machine has both output strings in its finite program.
Choosing the empty circuit and the constant true circuit proves that FPT is
included in every level of the bounded-weft hierarchy, even at depth zero.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open ComplexityTheory BitstringEncoding TM2Program Turing

private def boolOutputMachine (out : Bool → List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop () (fun _ b => b.getD false) <|
    .branch id (pushList () (out true).reverse (.load (fun _ => false) .halt))
               (pushList () (out false).reverse (.load (fun _ => false) .halt))

private theorem boolOutputMachine_run (out : Bool → List Bool) (b : Bool) :
    Run (boolOutputMachine out).m 1 (initList (boolOutputMachine out) [b])
      (haltList (boolOutputMachine out) (out b)) := by
  let tm := boolOutputMachine out
  have hi : initList tm [b] = ⟨some (), false, fun _ => [b]⟩ := by congr 1
  have ho : haltList tm (out b) = ⟨none, false, fun _ => out b⟩ := by congr 1
  change Run tm.m 1 (initList tm [b]) (haltList tm (out b))
  rw [hi, ho]
  apply Run.single
  cases b <;>
    simp only [tm, boolOutputMachine, TM2.stepAux, List.head?_cons, Option.getD_some, id_eq,
      List.tail_cons, cond_eq_ite, Bool.false_eq_true, ↓reduceIte] <;>
    erw [stepAux_pushList, List.reverse_reverse] <;>
    apply congrArg (TM2.Cfg.mk none false) <;>
    funext k <;> cases k <;> exact List.append_nil _

/-- Any function on a single Boolean input is machine-computable in polynomial time:
the two encoded outputs are fixed words of a fixed finite machine. -/
theorem isPolyTime_of_bool {β : Type} [BitstringEncoding β] (f : Bool → β) :
    IsPolyTime f := by
  refine ⟨{ tm := boolOutputMachine (bitEncode ∘ f)
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := ?_ }⟩
  intro b
  refine ⟨⟨1, ?_⟩, by simp⟩
  let tm := boolOutputMachine (bitEncode ∘ f)
  change Run tm.m 1 (initList tm (List.map id [b]))
    (haltList tm (List.map id (bitEncode (f b))))
  erw [List.map_id, List.map_id]
  exact boolOutputMachine_run (bitEncode ∘ f) b

/-- Postcomposing an FPT-time function with a polynomial-time function preserves FPT time. -/
theorem FPTTime.comp_poly {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : List Bool × ℕ → α} {g : α → β} (hf : FPTTime f) (hg : IsPolyTime g) :
    FPTTime (g ∘ f) := by
  obtain ⟨pad, hpad, run, hrun, heq⟩ := hf
  exact ⟨pad, hpad, g ∘ run, hrun.comp hg, fun x k => congrArg g (heq x k)⟩

/-- An FPT problem reduces to any parameterized problem with one yes- and one no-instance.
The output parameter is bounded by the larger of their fixed parameters. -/
theorem FPT.reduces_of_nontrivial {P Q : ParamProblem} (hP : FPT P)
    (yes no : List Bool × ℕ) (hy : Q yes.1 yes.2) (hn : ¬Q no.1 no.2) :
    FPTReduces P Q := by
  obtain ⟨D, hD, hcorrect⟩ := hP
  let select (b : Bool) := if b then yes else no
  refine ⟨select ∘ D, hD.comp_poly (isPolyTime_of_bool select),
    fun _ => max yes.2 no.2, Computable.const _, ?_⟩
  intro x k
  rw [hcorrect]
  cases h : D (x, k) <;> simp [select, h, hy, hn]

/-- FPT lies in every weft level. At weight zero on zero variables, the constant-true
circuit supplies a yes-instance and the empty gate list supplies a no-instance. -/
theorem FPT.mem_wLevel {P : ParamProblem} (hP : FPT P) (t : ℕ) : P ∈ WLevel t := by
  let yes := bitEncode ((0, [(1, [1])]) : ℕ × List WCGate)
  let no := bitEncode ((0, []) : ℕ × List WCGate)
  refine ⟨0, hP.reduces_of_nontrivial (Q := WeightedCircuitSat t 0) (yes, 0) (no, 0) ?_ ?_⟩
  · simp only [yes, WeightedCircuitSat, bitDecode_bitEncode, decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, [], rfl, rfl, rfl⟩
    · intro j hj a ha hkind
      obtain rfl : j = 0 := by simpa using hj
      simp at hkind
    · simp [wcCircuitWefts, wcGateWeft, wcGatePreds]
    · simp [wcCircuitDepths, wcGateDepth]
  · simp [no, WeightedCircuitSat, wcCircuitEval, Cslib.Complexity.Classes.circuitEval]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
