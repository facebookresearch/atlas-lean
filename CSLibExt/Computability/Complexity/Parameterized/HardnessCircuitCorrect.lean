/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitTrace
public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitBounds

/-!
# Correctness of the fixed-depth synchronous normalization machine

A table row is stable after its gate depth plus one rounds. Below a large gate
of a weft-one circuit each family is a singleton, including the negative
polarity. The normalizer can therefore pool the clauses of all children in one
traversal at large conjunctions.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine

open Cslib.Complexity.Classes
open NormalFormMachine (Satisfies Models combineFamilies binaryAnd binaryOr)

/-- The signed literal agrees with the bit of the input assignment. -/
def literalHolds (a : List Bool) (v : ℕ × Bool) : Prop := a.getD v.1 false = v.2

private def Record (a : List Bool) (w : ℕ) (b : Bool) (x : Node) : Prop :=
  ∀ p, (atPolarity p x ≠ []) ∧ (w = 0 → (atPolarity p x).length = 1) ∧
    (Satisfies (literalHolds a) (atPolarity p x) ↔ b = p)

private def readMax (values refs : List ℕ) :=
  refs.foldr (fun i z => max (values.getD i 0) z) 0

private theorem le_readMax (xs : List ℕ) {rs : List ℕ} {j : ℕ} (hj : j ∈ rs) :
    xs.getD j 0 ≤ readMax xs rs := by
  induction rs with
  | nil => simp at hj
  | cons r rs ih =>
    rcases List.mem_cons.mp hj with rfl | h
    · exact le_max_left ..
    · exact (ih h).trans (le_max_right ..)

private theorem combine_nonempty (andGate : Bool) (xs : List Family) (h : ∀ q ∈ xs, q ≠ []) :
    combineFamilies andGate xs ≠ [] := by
  match xs with
  | [] => cases andGate <;> simp [combineFamilies]
  | [a] => exact h a (by simp)
  | [a,b] =>
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (h a (by simp))
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (h b (by simp))
    cases andGate <;> apply List.ne_nil_of_mem <;>
      exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
  | a :: b :: c :: tail =>
    cases andGate with
    | false =>
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (h a (by simp))
      exact List.ne_nil_of_mem (a := p) (List.mem_flatten.mpr ⟨a, by simp, hp⟩)
    | true => simp [combineFamilies]

private theorem combine_single (andGate : Bool) (xs : List Family) (h : ∀ q ∈ xs, q.length = 1)
    (len : xs.length ≤ 2) : (combineFamilies andGate xs).length = 1 := by
  match xs with
  | [] => cases andGate <;> rfl
  | [a] => exact h a (by simp)
  | [a,b] =>
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (h a (by simp))
    obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp (h b (by simp))
    cases andGate <;> rfl
  | a :: b :: c :: tail => simp at len

private abbrev weight (ws rs : List ℕ) := (if 2 < rs.length then 1 else 0) + readMax ws rs

private theorem compound (a : List Bool) (ws rs : List ℕ) (vs : List Bool) (prev : List Node)
    (hr : ∀ j ∈ rs, Record a (ws.getD j 0) (vs.getD j false) (prev.getD j falseNode))
    (hw : weight ws rs ≤ 1) (conj pol : Bool) :
    let xs := rs.map fun i => atPolarity pol (prev.getD i falseNode)
    let out := combineFamilies conj xs
    out ≠ [] ∧ (weight ws rs = 0 → out.length = 1) ∧
      (Satisfies (literalHolds a) out ↔ if conj then ∀ i ∈ rs, vs.getD i false = pol
        else ∃ i ∈ rs, vs.getD i false = pol) := by
  let xs := rs.map fun i => atPolarity pol (prev.getD i falseNode)
  have hx : xs.length = rs.length := by simp [xs]
  have hpos : ∀ p ∈ xs, p ≠ [] := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact (hr j hj pol).1
  have hsingle (hm : readMax ws rs = 0) : ∀ q ∈ xs, q.length = 1 := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact (hr j hj pol).2.1 (Nat.eq_zero_of_le_zero ((le_readMax ws hj).trans hm.le))
  have hbig (h : 2 < xs.length) : ∀ q ∈ xs, q.length = 1 := by
    have hh : 2 < rs.length := hx ▸ h
    have wm : readMax ws rs = 0 := by simpa [weight, hh] using hw
    exact hsingle wm
  have hzero (h : weight ws rs = 0) : (combineFamilies conj xs).length = 1 := by
    have hm : readMax ws rs = 0 := by dsimp only [weight] at h; split at h <;> omega
    apply combine_single _ _ (hsingle hm)
    dsimp only [weight] at h
    split at h <;> omega
  refine ⟨combine_nonempty conj xs hpos, hzero, ?_⟩
  rw [NormalFormMachine.combine_satisfies _ _ _ hpos hbig]
  cases conj with
  | false =>
    constructor
    · rintro ⟨q, hq, h⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact ⟨i, hi, (hr i hi pol).2.2.mp h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨_, List.mem_map_of_mem hi, (hr i hi pol).2.2.mpr h⟩
  | true =>
    constructor
    · intro h i hi
      exact (hr i hi pol).2.2.mp (h _ (List.mem_map_of_mem hi))
    · intro h q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact (hr i hi pol).2.2.mpr (h i hi)

private theorem const_spec (a : List Bool) (b p : Bool) (w : ℕ) :
    constant b p ≠ [] ∧ (w = 0 → (constant b p).length = 1) ∧
      (Satisfies (literalHolds a) (constant b p) ↔ b = p) := by
  cases b <;> cases p <;> simp [constant, Satisfies, Models]

private theorem gate_record (a : List Bool) (ws : List ℕ) (vals : List Bool)
    (prev : List Node) (g : WCGate) (hw : wcGateWeft ws g ≤ 1)
    (hr : ∀ j ∈ g.2, (g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4) →
      Record a (ws.getD j 0) (vals.getD j false) (prev.getD j falseNode)) :
    Record a (wcGateWeft ws g)
      (gateValue vals (fun i : Fin a.length => a.getD i.val false) (acGateOfPair g))
      (gate a.length prev g true, gate a.length prev g false) := by
  obtain ⟨kind, rs⟩ := g
  intro p
  have gate_p : atPolarity p (gate a.length prev (kind, rs) true,
      gate a.length prev (kind, rs) false) = gate a.length prev (kind,rs) p := by cases p <;> rfl
  rw [gate_p]
  match kind, rs with
  | 0, [i] =>
    by_cases hi : i < a.length
    · simp [gate, hi, acGateOfPair, gateValue, literalHolds, Satisfies, Models]
    · simpa [gate, acGateOfPair, hi, gateValue, wcGateWeft, wcGatePreds] using
        const_spec a false p 0
  | 1, [i] =>
    simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds] using
      const_spec a (decide (i = 1)) p 0
  | 2, [i] =>
    have h := hr i (by simp) (by simp) (!p)
    cases p <;> simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds] using h
  | 3, rs =>
    have hc (c : Bool) := compound a ws rs vals prev (fun j h => hr j h (by simp))
      (by simpa [wcGateWeft, wcGatePreds, weight, readMax] using hw) c p
    cases p with
    | false => simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds, weight,
        readMax, List.all_eq_true] using hc false
    | true => simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds, weight,
        readMax, List.all_eq_true] using hc true
  | 4, rs =>
    have hc (c : Bool) := compound a ws rs vals prev (fun j h => hr j h (by simp))
      (by simpa [wcGateWeft, wcGatePreds, weight, readMax] using hw) c p
    cases p with
    | false => simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds, weight,
        readMax, List.any_eq_true] using hc true
    | true => simpa [gate, acGateOfPair, gateValue, wcGateWeft, wcGatePreds, weight,
        readMax, List.any_eq_true] using hc false
  | 0, [] | 0, x :: y :: tail | 1, [] | 1, x :: y :: tail | 2, [] | 2, x :: y :: tail
  | _+5, rs =>
    simpa [gate, acGateOfPair, gateValue] using const_spec a false p _

private theorem pred_bounds (ws ds : List ℕ) (g : WCGate) (j : ℕ) (hj : j ∈ g.2)
    (hk : g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4) :
    ws.getD j 0 ≤ wcGateWeft ws g ∧ ds.getD j 0 < wcGateDepth ds g := by
  obtain ⟨k, rs⟩ := g
  change j ∈ rs at hj
  change k = 2 ∨ k = 3 ∨ k = 4 at hk
  have w := le_readMax ws hj
  have d := le_readMax ds hj
  rcases hk with rfl | rfl | rfl <;>
    simp only [wcGateWeft, wcGatePreds, wcGateDepth] <;>
    unfold readMax at w d <;> omega

private theorem table_record (C : List WCGate) (a : List Bool) (hf : WCWellFormed C)
    (fuel i : ℕ) (hi : i < C.length) (hd : (wcCircuitDepths C).getD i 0 < fuel)
    (hw : (wcCircuitWefts C).getD i 0 ≤ 1) :
    Record a ((wcCircuitWefts C).getD i 0) ((wcCircuitEval C a).getD i false)
      ((table a.length C fuel).getD i falseNode) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    let pre := C.take i
    let g := C[i]
    have hW : (wcCircuitWefts C).getD i 0 = wcGateWeft (wcCircuitWefts pre) g :=
      getD_history_gate wcGateWeft C 0 i hi
    have hD : (wcCircuitDepths C).getD i 0 = wcGateDepth (wcCircuitDepths pre) g :=
      getD_history_gate wcGateDepth C 0 i hi
    have hV : (wcCircuitEval C a).getD i false =
        gateValue (wcCircuitEval pre a) (fun j : Fin a.length => a.getD j.val false)
          (acGateOfPair g) := by
      rw [eval_history C a, eval_history pre a]
      exact getD_history_gate _ _ _ _ hi
    have hargs (j : ℕ) (hj : j ∈ g.2) (hk : g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4) :
        Record a ((wcCircuitWefts pre).getD j 0) ((wcCircuitEval pre a).getD j false)
          ((table a.length C fuel).getD j falseNode) := by
      have hji : j < i := hf i hi j hj hk
      have hWj : (wcCircuitWefts pre).getD j 0 = (wcCircuitWefts C).getD j 0 :=
        getD_history_prefix wcGateWeft C 0 hi.le hji
      have hDj : (wcCircuitDepths pre).getD j 0 = (wcCircuitDepths C).getD j 0 :=
        getD_history_prefix wcGateDepth C 0 hi.le hji
      have hVj : (wcCircuitEval pre a).getD j false = (wcCircuitEval C a).getD j false := by
        rw [eval_history pre a, eval_history C a]
        exact getD_history_prefix _ _ _ hi.le hji
      obtain ⟨wj, dj⟩ := pred_bounds (wcCircuitWefts pre) (wcCircuitDepths pre) g j hj hk
      rw [hWj, hVj]
      exact ih j (by omega) (by omega) (by omega)
    have result := gate_record a (wcCircuitWefts pre) (wcCircuitEval pre a)
      (table a.length C fuel) g (hW ▸ hw) hargs
    intro p
    have choose : atPolarity p (gate a.length (table a.length C fuel) g true,
        gate a.length (table a.length C fuel) g false) =
          gate a.length (table a.length C fuel) g p := by
      cases p <;> rfl
    simpa only [table_getD _ _ _ _ hi, hV, hW, choose] using result p

/-- Each gate's computed formula has the semantic value of that gate when the depth permits
sufficiently many synchronous rounds. -/
theorem gate_satisfies (C : List WCGate) (a : List Bool) (hf : WCWellFormed C)
    (d i : ℕ) (hi : i < C.length) (hd : (wcCircuitDepths C).getD i 0 ≤ d)
    (hw : (wcCircuitWefts C).getD i 0 ≤ 1) (p : Bool) :
    Satisfies (literalHolds a) (atPolarity p ((table a.length C (d+1)).getD i falseNode)) ↔
      (wcCircuitEval C a).getD i false = p :=
  (table_record C a hf (d+1) i hi (by omega) hw p).2.2

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine
