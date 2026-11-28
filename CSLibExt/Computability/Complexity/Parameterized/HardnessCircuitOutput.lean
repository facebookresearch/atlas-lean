/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitCorrect
public import CSLibExt.Computability.Complexity.Parameterized.CircuitGuard

/-!
# A complete polynomial-time normalizer for weighted weft-one circuits

The output is a disjunction of signed CNFs. The normalizer enforces every raw
gate's topological, weft, and depth conditions and gives an unsatisfiable result
on invalid circuits. Weight is preserved by evaluating each formula on the
original set of selected variables.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.Comprehension BitScan

/-- Signed CNF alternatives computed for the final gate, including the validity guard. -/
def family (d n : ℕ) (C : List WCGate) : Family :=
  if NormalForm.validCircuit 1 d C then ((table n C (d+1)).getD (C.length - 1) falseNode).1 else []

/-- In the raw TM2 model the full validity check, all table rounds, reading the final gate,
and writing the signed family are polynomial time for each fixed depth. -/
theorem represented_family {α : Type} {repr : α → List Bool} {n : α → ℕ} {C : α → List WCGate}
    (hn : Represented repr (fun x => bitEncode (n x)))
    (hc : Represented repr (fun x => frames bitEncode (C x))) (d : ℕ) :
    Represented repr (fun x => familyWord (family d (n x) (C x))) := by
  have tail : Represented repr (fun x => frames bitEncode (C x).tail) := by
    apply (hc.after (polyField false true)).transport
    intro x
    cases C x with
    | nil => rfl
    | cons y ys => exact tl_pack (bitEncode y) (frames bitEncode ys)
  have idx : Represented repr (fun x => bitEncode ((C x).length - 1)) :=
    (tail.count.after isPolyTime_encodeLength).transport (by simp)
  have node := represented_getD nodeWord falseNode (represented_table hn hc (d+1)) idx
  have pos := (node.after (polyField true false)).transport (fun x => hd_pack _ _)
  have valid := NormalForm.represented_validCircuit_of_table hc 1 d
  apply (valid.cond pos (Represented.const repr (familyWord []))).transport
  intro x
  unfold family
  split <;> rfl

/-- The literal bounds hold on the machine's emitted literal lists, including duplicates. -/
theorem family_fits (d n : ℕ) (C : List WCGate) : Fits n (2^d) (family d n C) := by
  unfold family
  split
  · by_cases h : C = []
    · subst C
      simp [table, Fits, falseNode, constant]
    · have hi : C.length - 1 < (table n C (d+1)).length := by
        have := List.length_pos_iff.mpr h
        simp; omega
      rw [List.getD_eq_getElem _ _ hi]
      exact table_fits n d C _ (List.getElem_mem _) true
  · simp [Fits]

/-- The emitted family is satisfied by exactly the assignments accepted by the final gate
of an admissible circuit. Invalid circuits yield no satisfying assignment. -/
theorem family_satisfies (d : ℕ) (C : List WCGate) (a : List Bool) :
    NormalFormMachine.Satisfies (literalHolds a) (family d a.length C) ↔
      NormalForm.validCircuit 1 d C ∧ (wcCircuitEval C a).getLast? = some true := by
  by_cases hh : NormalForm.validCircuit 1 d C = true
  · simp only [family, hh, ite_true, true_and]
    obtain ⟨topo, weft, depth⟩ := (NormalForm.validCircuit_iff 1 d C).mp hh
    by_cases h : C = []
    · subst C
      simp [table, falseNode, constant, NormalFormMachine.Satisfies, NormalFormMachine.Models,
        wcCircuitEval, Cslib.Complexity.Classes.circuitEval]
    · have hi : C.length - 1 < C.length := by have := List.length_pos_iff.mpr h; omega
      have hd : C.length - 1 < (wcCircuitDepths C).length := by
        change C.length - 1 < (history wcGateDepth C).length
        simpa using hi
      have hw : C.length - 1 < (wcCircuitWefts C).length := by
        change C.length - 1 < (history wcGateWeft C).length
        simpa using hi
      have sound := gate_satisfies C a topo d (C.length - 1) hi
        (depth _ (by rw [List.getD_eq_getElem _ _ hd]; exact List.getElem_mem _))
        (weft _ (by rw [List.getD_eq_getElem _ _ hw]; exact List.getElem_mem _)) true
      apply sound.trans
      have hsz : (wcCircuitEval C a).length = C.length := by simp [eval_history]
      rw [List.getLast?_eq_getElem?, hsz, List.getD_eq_getElem?_getD]
      cases (wcCircuitEval C a)[C.length-1]? <;> simp
  · simp [family, hh, NormalFormMachine.Satisfies]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine
