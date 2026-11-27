/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Defs
import Mathlib.Data.List.GetD

/-!
# Changing the weft bound on encoded circuits

Increasing the weft bound can turn a no-instance into a yes-instance,
even at weight zero. A probe reading all gates shifts both bounds by one; a
separate gate relays the old output. This preserves the answer and the weight.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open MetaMathlibExt.BitstringEncoding

@[simp] theorem weightedCircuitSat_nil (t d k : ℕ) : WeightedCircuitSat t d [] k = false := by
  rfl

/-- Weighted satisfiability depends only on the decoded instance. -/
theorem weightedCircuitSat_congr_decode {x y : List Bool}
    (h : bitDecode (α := ℕ × List WCGate) x = bitDecode y) (t d k : ℕ) :
    WeightedCircuitSat t d x k = WeightedCircuitSat t d y k := by
  simp only [WeightedCircuitSat, h]

/-- References all old gates, including unreachable gates. The repeated zeroes
make the probe a large gate even on a one-gate circuit. -/
def probeRefs (n : ℕ) : List ℕ := List.range n ++ [0, 0, 0]

/-- Append a large probe and a unary OR relaying the previous output. The probe
contributes to the global weft and depth bounds without affecting that output. -/
def promoteWeftCircuit (C : List WCGate) : List WCGate :=
  if C = [] then [] else C ++ [(3, probeRefs C.length), (4, [C.length - 1])]

/-- Change the weft budget without testing it, by serializing the augmented circuit. -/
def promoteWeft (x : List Bool) : List Bool :=
  match bitDecode (α := ℕ × List WCGate) x with
  | none => []
  | some (n, C) => bitEncode (n, promoteWeftCircuit C)

private theorem trace_length {α β : Type} (step : List α → β → α) (xs : List β)
    (init : List α) :
    (xs.foldl (fun acc x => acc ++ [step acc x]) init).length = init.length + xs.length := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wefts_length (C : List WCGate) : (wcCircuitWefts C).length = C.length := by
  simpa [wcCircuitWefts] using trace_length wcGateWeft C []

private theorem depths_length (C : List WCGate) : (wcCircuitDepths C).length = C.length := by
  simpa [wcCircuitDepths] using trace_length wcGateDepth C []

private theorem eval_length (C : List WCGate) (a : List Bool) :
    (wcCircuitEval C a).length = C.length := by
  unfold wcCircuitEval Cslib.Complexity.Classes.circuitEval
  rw [trace_length]
  simp

private theorem wellFormed_probe {C : List WCGate} (hne : C ≠ []) :
    WCWellFormed (promoteWeftCircuit C) ↔ WCWellFormed C := by
  simp only [promoteWeftCircuit, hne, ite_false]
  have hn : 0 < C.length := List.length_pos_iff.mpr hne
  constructor
  · intro hf j hj
    have hj' : j < (C ++ [(3, probeRefs C.length), (4, [C.length - 1])]).length := by simp; omega
    simpa only [List.getElem_append_left hj] using hf j hj'
  · intro hf j hj
    by_cases hjc : j < C.length
    · simpa only [List.getElem_append_left hjc] using hf j hjc
    · have hj2 : j = C.length ∨ j = C.length + 1 := by
        simp at hj
        omega
      rcases hj2 with rfl | rfl
      · simp [probeRefs, List.getElem_append_right]
        grind
      · simp [List.getElem_append_right]

private def readMax (old : List ℕ) (idx : List ℕ) : ℕ :=
  idx.foldr (fun j acc => max (old.getD j 0) acc) 0

private theorem readMax_le_iff (old idx : List ℕ) (b : ℕ) :
    readMax old idx ≤ b ↔ ∀ j ∈ idx, old.getD j 0 ≤ b := by
  induction idx with
  | nil => simp [readMax]
  | cons i idx ih => simpa [readMax, max_le_iff] using
      and_congr_right (fun _ : old.getD i 0 ≤ b => ih)

private theorem readMax_probe_le (old : List ℕ) (b : ℕ) :
    readMax old (probeRefs old.length) ≤ b ↔ ∀ v ∈ old, v ≤ b := by
  rw [readMax_le_iff]
  constructor
  · intro h v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    simpa only [List.getD_eq_getElem old 0 hi] using h i (by simp [probeRefs, hi])
  · intro h i _
    by_cases hi : i < old.length
    · simpa only [List.getD_eq_getElem old 0 hi] using h old[i] (List.getElem_mem hi)
    · rw [List.getD_eq_default old 0 (Nat.le_of_not_gt hi)]
      exact Nat.zero_le _

private theorem bound_trace_probe (old : List ℕ) (hn : 0 < old.length) (b relayCost : ℕ)
    (hc : relayCost ≤ 1) :
    let p := 1 + readMax old (probeRefs old.length)
    let last := (old ++ [p]).getD (old.length - 1) 0
    (∀ v ∈ old ++ [p] ++ [last + relayCost], v ≤ b + 1) ↔ ∀ v ∈ old, v ≤ b := by
  dsimp only
  have hi : old.length - 1 < old.length := by omega
  rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  constructor
  · intro h
    have hh := h (1 + readMax old (probeRefs old.length)) (by simp)
    apply (readMax_probe_le old b).mp
    omega
  · intro h v hv
    have hp := (readMax_probe_le old b).mpr h
    have hl := h _ (List.getElem_mem hi)
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with (hmem | rfl) | rfl
    · exact (h v hmem).trans (Nat.le_succ b)
    · omega
    · omega

private theorem wefts_probe {C : List WCGate} (hne : C ≠ []) (b : ℕ) :
    (∀ w ∈ wcCircuitWefts (promoteWeftCircuit C), w ≤ b + 1) ↔
      ∀ w ∈ wcCircuitWefts C, w ≤ b := by
  let old := wcCircuitWefts C
  have len : old.length = C.length := wefts_length C
  have hn : 0 < old.length := len ▸ List.length_pos_iff.mpr hne
  have big : 2 < (probeRefs C.length).length := by simp [probeRefs]
  simp only [promoteWeftCircuit, hne, ite_false]
  simp only [wcCircuitWefts, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (∀ w ∈ old ++ [wcGateWeft old (3, probeRefs C.length)] ++
    [wcGateWeft (old ++ [wcGateWeft old (3, probeRefs C.length)]) (4, [C.length - 1])],
    w ≤ b + 1) ↔ ∀ w ∈ old, w ≤ b
  have probe : wcGateWeft old (3, probeRefs C.length) = 1 + readMax old (probeRefs C.length) := by
    simp [wcGateWeft, wcGatePreds, readMax, big]
  rw [probe]
  simpa [wcGateWeft, wcGatePreds, len] using bound_trace_probe old hn b 0 (by decide)

private theorem depths_probe {C : List WCGate} (hne : C ≠ []) (b : ℕ) :
    (∀ w ∈ wcCircuitDepths (promoteWeftCircuit C), w ≤ b + 1) ↔
      ∀ w ∈ wcCircuitDepths C, w ≤ b := by
  let old := wcCircuitDepths C
  have len : old.length = C.length := depths_length C
  have hn : 0 < old.length := len ▸ List.length_pos_iff.mpr hne
  simp only [promoteWeftCircuit, hne, ite_false]
  simp only [wcCircuitDepths, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (∀ w ∈ old ++ [wcGateDepth old (3, probeRefs C.length)] ++
    [wcGateDepth (old ++ [wcGateDepth old (3, probeRefs C.length)]) (4, [C.length - 1])],
    w ≤ b + 1) ↔ ∀ w ∈ old, w ≤ b
  have probe : wcGateDepth old (3, probeRefs C.length) = 1 + readMax old (probeRefs C.length) :=
    Nat.add_comm _ _
  rw [probe]
  simpa [wcGateDepth, len] using bound_trace_probe old hn b 1 (by decide)

private theorem eval_probe {C : List WCGate} (hne : C ≠ []) (a : List Bool) :
    (wcCircuitEval (promoteWeftCircuit C) a).getLast? = (wcCircuitEval C a).getLast? := by
  let vs := wcCircuitEval C a
  have len : vs.length = C.length := eval_length C a
  have hn : 0 < C.length := List.length_pos_iff.mpr hne
  have hi : C.length - 1 < vs.length := by omega
  simp only [promoteWeftCircuit, hne, ite_false]
  simp only [wcCircuitEval, List.map_append, List.map_cons, List.map_nil,
    Cslib.Complexity.Classes.circuitEval, List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize hgate : Cslib.Complexity.Classes.acGateOfPair (n := a.length)
    (3, probeRefs C.length) = g
  let probeVal := Cslib.Complexity.Classes.gateValue vs
    (fun i : Fin a.length => a.getD i.val false) g
  change ((vs ++ [probeVal]) ++
    [((vs ++ [probeVal]).getD (C.length - 1) false || false)]).getLast? = vs.getLast?
  simp [List.getLast?_eq_getElem? (l := vs), len, List.getElem_append_left hi]

/-- The promoted bitstring at budgets `(t+1,d+1)` has exactly the same answer as
the source at `(t,d)`, at the very same weight. This includes empty and malformed inputs. -/
theorem weightedCircuitSat_promoteWeft (t d : ℕ) (x : List Bool) (k : ℕ) :
    WeightedCircuitSat (t+1) (d+1) (promoteWeft x) k = WeightedCircuitSat t d x k := by
  cases h : bitDecode (α := ℕ × List WCGate) x with
  | none =>
    rw [show promoteWeft x = [] by simp only [promoteWeft, h], weightedCircuitSat_nil]
    simp only [WeightedCircuitSat, h]
  | some p =>
    obtain ⟨n, C⟩ := p
    apply Bool.eq_iff_iff.mpr
    simp only [promoteWeft, h, WeightedCircuitSat, bitDecode_bitEncode, decide_eq_true_eq]
    by_cases hc : C = []
    · simp [hc, promoteWeftCircuit, wcCircuitEval, Cslib.Complexity.Classes.circuitEval]
    · simp_rw [wellFormed_probe hc, wefts_probe hc t, depths_probe hc d, eval_probe hc]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
