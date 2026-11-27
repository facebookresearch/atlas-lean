/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Identity
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.FinRange

/-!
# Clique witnesses on a compact set of vertices

The input graph declares the number of vertices in binary. Constructing a gate for
each declared vertex can therefore require exponential space. It suffices to use the
in-range endpoints of written edges together with vertex zero when the graph is nonempty.
The extra vertex preserves singleton cliques, including in edgeless graphs.

The reduction expresses incompatibility of two choices by a binary AND, combines the
violations at a single OR gate, and negates its output. Only the OR can have large fan-in.

Source: Downey and Fellows, *Parameterized Complexity* (1999), weighted circuit
satisfiability and the W[1]-completeness of Clique.
-/
@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized
open Cslib.Complexity.Classes

namespace CliqueMembership

/-- The compact input-variable alphabet for the clique circuit. -/
def vertices (n : ℕ) (edges : List (ℕ × ℕ)) : List ℕ :=
  ((List.range (min 1 n)) ++
    ((edges.map Prod.fst ++ edges.map Prod.snd).filter (· < n))).dedup

theorem vertices_nodup (n : ℕ) (edges : List (ℕ × ℕ)) : (vertices n edges).Nodup :=
  List.nodup_dedup _

private theorem mem_vertices_iff {n v : ℕ} {edges : List (ℕ × ℕ)} :
    v ∈ vertices n edges ↔ v < n ∧
      (v = 0 ∨ (∃ w, (v, w) ∈ edges) ∨ ∃ w, (w, v) ∈ edges) := by
  simp only [vertices, List.mem_dedup, List.mem_append, List.mem_range, List.mem_filter,
    List.mem_map, decide_eq_true_eq]
  constructor
  · rintro (hz | ⟨hedge, hv⟩)
    · exact ⟨by omega, Or.inl (by omega)⟩
    · refine ⟨hv, Or.inr ?_⟩
      rcases hedge with ⟨⟨a, b⟩, hab, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩
      · exact Or.inl ⟨b, hab⟩
      · exact Or.inr ⟨a, hab⟩
  · rintro ⟨hv, rfl | ⟨w, hw⟩ | ⟨w, hw⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨Or.inl ⟨(v, w), hw, rfl⟩, hv⟩
    · exact Or.inr ⟨Or.inr ⟨(w, v), hw, rfl⟩, hv⟩

/-- Restricting clique witnesses to compact vertices preserves every weight, including zero and
one, even in the presence of repeated edges, loops and out-of-range endpoints. -/
theorem clique_iff_compact (n k : ℕ) (edges : List (ℕ × ℕ)) :
    (∃ s : List ℕ, s.Nodup ∧ s.length = k ∧ (∀ u ∈ s, u < n) ∧
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (u, v) ∈ edges ∨ (v, u) ∈ edges) ↔
    (∃ s : List ℕ, s.Nodup ∧ s.length = k ∧ (∀ u ∈ s, u ∈ vertices n edges) ∧
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (u, v) ∈ edges ∨ (v, u) ∈ edges) := by
  constructor
  · rintro ⟨s, hs, hk, hn, ha⟩
    cases s with
    | nil => exact ⟨[], hs, hk, by simp, ha⟩
    | cons x xs =>
      cases xs with
      | nil =>
        refine ⟨[0], by simp, hk, ?_, by simp⟩
        have hx := hn x (by simp)
        simpa using (mem_vertices_iff.mpr ⟨by omega, Or.inl rfl⟩ :
          0 ∈ vertices n edges)
      | cons y ys =>
        have hxy : x ≠ y := fun e => (List.nodup_cons.mp hs).1 (by simp [e])
        refine ⟨_, hs, hk, ?_, ha⟩
        intro u hu
        apply mem_vertices_iff.mpr
        refine ⟨hn u hu, Or.inr ?_⟩
        have hex : ∃ v ∈ x :: y :: ys, u ≠ v := by
          by_cases h : u = x
          · exact ⟨y, by simp, h ▸ hxy⟩
          · exact ⟨x, by simp, h⟩
        obtain ⟨v, hv, huv⟩ := hex
        exact (ha u hu v hv huv).elim (fun h => Or.inl ⟨v, h⟩) (fun h => Or.inr ⟨v, h⟩)
  · rintro ⟨s, hs, hk, hv, ha⟩
    exact ⟨s, hs, hk, fun u hu => (mem_vertices_iff.mp (hv u hu)).1, ha⟩

/-- References to a contiguous layer of earlier gates. -/
def outputs (offset length : ℕ) : List ℕ :=
  (List.range length).map (offset + ·)

/-- The circuit for an antimonotone 2-CNF. A pair is a forbidden simultaneous choice.
Its output is true exactly when none of the listed pairs is chosen. -/
def exclusionCircuit (m : ℕ) (pairs : List (ℕ × ℕ)) : List WCGate :=
  (List.range m).map (fun i => (0, [i])) ++
  pairs.map (fun ij => (3, [ij.1, ij.2])) ++
  [(4, outputs m pairs.length), (2, [m + pairs.length])]

/-- A layer that only reads a fixed earlier prefix appends its gate values in order. -/
private theorem foldLayer {α β γ : Type} (value : List β → γ → β) (gate : α → γ)
    (result : α → β) (base built : List β) (xs : List α)
    (h : ∀ x ∈ xs, ∀ extra, value (base ++ extra) (gate x) = result x) :
    ((xs.map gate).foldl (fun acc g => acc ++ [value acc g]) (base ++ built)) =
      base ++ built ++ xs.map result := by
  induction xs generalizing built with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, h x List.mem_cons_self built]
    rw [List.append_assoc base built [result x], ih (built ++ [result x])
      (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

private theorem getD_prefix {α : Type} (a b : List α) (i : ℕ) (d : α)
    (hi : i < a.length) : (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_offset {α : Type} (a b : List α) (i : ℕ) (d : α) :
    (a ++ b).getD (a.length + i) d = b.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

private theorem map_range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

private def runGate (a vs : List Bool) (g : WCGate) : Bool :=
  gateValue vs (fun i : Fin a.length => a.getD i.val false) (acGateOfPair g)

/-- The two listed inputs are both selected. -/
def clashes (a : List Bool) (p : ℕ × ℕ) : Bool :=
  a.getD p.1 false && a.getD p.2 false

/-- Evaluation of the exclusion circuit, for every input assignment and even an empty set
of constraints. -/
theorem exclusionCircuit_eval (a : List Bool) (pairs : List (ℕ × ℕ))
    (h : ∀ p ∈ pairs, p.1 < a.length ∧ p.2 < a.length) :
    (wcCircuitEval (exclusionCircuit a.length pairs) a).getLast? =
      some (!(pairs.any (clashes a))) := by
  let input : ℕ → WCGate := fun i => (0, [i])
  let pairGate : ℕ × ℕ → WCGate := fun p => (3, [p.1, p.2])
  let step := fun (acc : List Bool) (g : WCGate) => acc ++ [runGate a acc g]
  have hin : ((List.range a.length).map input).foldl step [] = a := by
    have hh := foldLayer (runGate a) input (fun i => a.getD i false) [] [] (List.range a.length)
      (fun i hi extra => by
        have hi' := List.mem_range.mp hi
        simp [input, runGate, acGateOfPair, gateValue, hi'])
    rw [map_range_getD] at hh
    simpa [step] using hh
  have hpair : (pairs.map pairGate).foldl step a = a ++ pairs.map (clashes a) := by
    have hh := foldLayer (runGate a) pairGate (clashes a) a [] pairs
      (fun p hp extra => by
        simp [pairGate, runGate, acGateOfPair, gateValue, clashes,
          List.getElem?_append_left (h p hp).1, List.getElem?_append_left (h p hp).2])
    simpa [step] using hh
  let v := pairs.map (clashes a)
  have hor : runGate a (a ++ v) (4, outputs a.length pairs.length) = pairs.any (clashes a) := by
    simp only [runGate, acGateOfPair, gateValue, outputs, List.any_map, Function.comp_def,
      getD_offset]
    change ((List.range pairs.length).any (fun i => v.getD i false)) = _
    have hv : v.length = pairs.length := by simp [v]
    rw [← hv]
    calc
      _ = ((List.range v.length).map (fun i => v.getD i false)).any id := by
        rw [List.any_map]; rfl
      _ = _ := by rw [map_range_getD]; simp [v]
  have heval : wcCircuitEval (exclusionCircuit a.length pairs) a =
      (exclusionCircuit a.length pairs).foldl step [] := by
    simp [wcCircuitEval, circuitEval, List.foldl_map, step, runGate]
  rw [heval]
  change ((((List.range a.length).map input ++ pairs.map pairGate) ++
    [(4, outputs a.length pairs.length), (2, [a.length + pairs.length])]).foldl step
      []).getLast? = _
  simp only [List.foldl_append, hin, hpair, List.foldl_cons, List.foldl_nil]
  have hl : (a ++ v).length = a.length + pairs.length := by simp [v]
  change ((a ++ v ++ [runGate a (a ++ v) (4, outputs a.length pairs.length)]) ++
    [runGate a (a ++ v ++ [runGate a (a ++ v) (4, outputs a.length pairs.length)])
      (2, [a.length + pairs.length])]).getLast? = _
  rw [hor]
  simp [runGate, acGateOfPair, gateValue, ← hl]

private theorem wellFormed_append {xs ys : List WCGate} (hx : WCWellFormed xs)
    (hy : ∀ g ∈ ys, ∀ a ∈ g.2, g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4 → a < xs.length) :
    WCWellFormed (xs ++ ys) := by
  intro j hj
  by_cases hjx : j < xs.length
  · rw [List.getElem_append_left hjx]
    exact hx j hjx
  · rw [List.getElem_append_right (Nat.le_of_not_gt hjx)]
    intro a ha ht
    exact (hy _ (List.getElem_mem ..) a ha ht).trans_le (by omega)

theorem exclusionCircuit_wellFormed (m : ℕ) (pairs : List (ℕ × ℕ))
    (h : ∀ p ∈ pairs, p.1 < m ∧ p.2 < m) :
    WCWellFormed (exclusionCircuit m pairs) := by
  let ins : List WCGate := (List.range m).map fun i => (0, [i])
  let conjs : List WCGate := pairs.map fun p => (3, [p.1, p.2])
  let o : WCGate := (4, outputs m pairs.length)
  have hin : WCWellFormed ins := by
    intro j hj a ha ht
    simp [ins] at ht
  have hm : ins.length = m := by simp [ins]
  have hp : (ins ++ conjs).length = m + pairs.length := by simp [hm, conjs]
  have hc : WCWellFormed (ins ++ conjs) := by
    refine wellFormed_append hin ?_
    intro g hg a ha _
    obtain ⟨p, hmem, rfl⟩ := List.mem_map.mp hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    exact hm ▸ (ha.elim (fun e => e ▸ (h p hmem).1) (fun e => e ▸ (h p hmem).2))
  have ho : WCWellFormed ((ins ++ conjs) ++ [o]) := by
    refine wellFormed_append hc ?_
    intro g hg a ha _
    obtain rfl := List.mem_singleton.mp hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [hp]
    exact Nat.add_lt_add_left (List.mem_range.mp hi) _
  change WCWellFormed ((ins ++ conjs) ++ ([o] ++ [(2, [m + pairs.length])]))
  rw [← List.append_assoc]
  refine wellFormed_append ho ?_
  intro g hg a ha _
  obtain rfl := List.mem_singleton.mp hg
  obtain rfl := List.mem_singleton.mp ha
  simp [hm, conjs]

private theorem snoc_bound (xs : List ℕ) (z total : ℕ) (hx : ∀ x ∈ xs, x ≤ total)
    (hz : z ≤ total) : ∀ v ∈ xs ++ [z], v ≤ total := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact hx v h
  · simpa only [List.mem_singleton.mp h] using hz

private theorem fold_max_bound (values : List ℕ) (c : ℕ) (hc : ∀ x ∈ values, x ≤ c)
    (refs : List ℕ) : refs.foldr (fun i acc => max (values.getD i 0) acc) 0 ≤ c := by
  induction refs with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldr_cons, max_le_iff]
    refine ⟨?_, ih⟩
    by_cases hi : i < values.length
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
        hc values[i] (List.getElem_mem ..)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : values.length ≤ i)]

private theorem boundsForLayers (measure : List ℕ → WCGate → ℕ) (m : ℕ)
    (pairs : List (ℕ × ℕ)) (value : ℕ)
    (inputBound : ∀ i ws, measure ws (0, [i]) = 0)
    (pairBound : ∀ p ∈ pairs, ∀ extra, measure (List.replicate m 0 ++ extra)
        (3, [p.1, p.2]) = value) :
    (((List.range m).map fun i => (0, [i])) ++ pairs.map fun p : ℕ × ℕ => (3, [p.1, p.2])).foldl
        (fun acc g => acc ++ [measure acc g]) [] =
      List.replicate m 0 ++ List.replicate pairs.length value := by
  have hi := foldLayer measure (fun i => (0, [i])) (fun _ => 0)
    [] [] (List.range m) (fun i _ _ => inputBound i _)
  simp only [List.nil_append, List.map_const', List.length_range] at hi
  have hp := foldLayer measure (fun p : ℕ × ℕ => (3, [p.1, p.2])) (fun _ => value)
    (List.replicate m 0) [] pairs pairBound
  simp only [List.append_nil, List.map_const'] at hp
  simpa only [List.foldl_append, hi] using hp

private theorem read_zero (m i : ℕ) (h : i < m) (extra : List ℕ) :
    (List.replicate m 0 ++ extra).getD i 0 = 0 := by
  rw [getD_prefix _ _ _ _ (by simpa), List.getD_replicate _ h]

theorem exclusionCircuit_weft (m : ℕ) (pairs : List (ℕ × ℕ))
    (h : ∀ p ∈ pairs, p.1 < m ∧ p.2 < m) :
    ∀ w ∈ wcCircuitWefts (exclusionCircuit m pairs), w ≤ 1 := by
  have hl := boundsForLayers wcGateWeft m pairs 0 (by simp [wcGateWeft, wcGatePreds])
    (fun p hp extra => by
      simp only [wcGateWeft, wcGatePreds, List.length_cons, List.length_nil,
        List.foldr_cons, List.foldr_nil, read_zero _ _ (h p hp).1, read_zero _ _ (h p hp).2]
      decide)
  let ws := List.replicate m 0 ++ List.replicate pairs.length 0
  let o : WCGate := (4, outputs m pairs.length)
  have hz : ∀ v ∈ ws, v ≤ 0 := by simp [ws]
  have ho : wcGateWeft ws o ≤ 1 := by
    have hm := fold_max_bound ws 0 hz (outputs m pairs.length)
    simp only [o, wcGateWeft, wcGatePreds]
    split <;> omega
  have hn : wcGateWeft (ws ++ [wcGateWeft ws o]) (2,[m + pairs.length]) ≤ 1 := by
    have hm := fold_max_bound (ws ++ [wcGateWeft ws o]) 1
      (snoc_bound _ _ _ (fun x hx => (hz x hx).trans (by decide)) ho)
      [m + pairs.length]
    simpa [wcGateWeft, wcGatePreds] using hm
  unfold wcCircuitWefts exclusionCircuit
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [List.foldl_append] at hl
  rw [hl]
  change ∀ w ∈ (ws ++ [wcGateWeft ws o]) ++
    [wcGateWeft (ws ++ [wcGateWeft ws o]) (2, [m + pairs.length])], w ≤ 1
  simp only [List.mem_append, List.mem_singleton]
  grind

theorem exclusionCircuit_depth (m : ℕ) (pairs : List (ℕ × ℕ))
    (h : ∀ p ∈ pairs, p.1 < m ∧ p.2 < m) :
    ∀ d ∈ wcCircuitDepths (exclusionCircuit m pairs), d ≤ 3 := by
  have hl := boundsForLayers wcGateDepth m pairs 1 (by simp [wcGateDepth])
    (fun p hp extra => by
      simp only [wcGateDepth, List.foldr_cons, List.foldr_nil,
        read_zero _ _ (h p hp).1, read_zero _ _ (h p hp).2]
      decide)
  let ds := List.replicate m 0 ++ List.replicate pairs.length 1
  let o : WCGate := (4, outputs m pairs.length)
  have hz : ∀ v ∈ ds, v ≤ 1 := by simp [ds]; grind
  have ho : wcGateDepth ds o ≤ 2 := by
    have hm := fold_max_bound ds 1 hz (outputs m pairs.length)
    simpa only [wcGateDepth, o, Nat.succ_le_succ_iff] using hm
  have hn : wcGateDepth (ds ++ [wcGateDepth ds o]) (2,[m + pairs.length]) ≤ 3 := by
    have hm := fold_max_bound (ds ++ [wcGateDepth ds o]) 2
      (snoc_bound _ _ _ (fun x hx => (hz x hx).trans (by decide)) ho)
      [m + pairs.length]
    simpa only [wcGateDepth, Nat.succ_le_succ_iff] using hm
  unfold wcCircuitDepths exclusionCircuit
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [List.foldl_append] at hl
  rw [hl]
  change ∀ d ∈ (ds ++ [wcGateDepth ds o]) ++
    [wcGateDepth (ds ++ [wcGateDepth ds o]) (2,[m + pairs.length])], d ≤ 3
  simp only [List.mem_append, List.mem_singleton]
  grind

/-- Pairs of distinct input positions whose original vertices have no connecting edge. -/
def forbiddenPairs (vs : List ℕ) (edges : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((List.range vs.length).product (List.range vs.length)).filter fun (i, j) =>
    decide (i ≠ j ∧ (vs.getD i 0, vs.getD j 0) ∉ edges ∧ (vs.getD j 0, vs.getD i 0) ∉ edges)

private theorem mem_forbiddenPairs (vs : List ℕ) (edges : List (ℕ × ℕ)) (i j : ℕ) :
    (i, j) ∈ forbiddenPairs vs edges ↔ (i < vs.length ∧ j < vs.length) ∧ i ≠ j ∧
      (vs.getD i 0, vs.getD j 0) ∉ edges ∧ (vs.getD j 0, vs.getD i 0) ∉ edges := by
  simp [forbiddenPairs]

private theorem read (a : List ℕ) (i : Fin a.length) : a.getD i.val 0 = a.get i :=
  List.getD_eq_getElem a _ i.isLt

private theorem noViolation_iff (vs : List ℕ) (edges : List (ℕ × ℕ)) (a : List Bool) :
    (forbiddenPairs vs edges).any (clashes a) = false ↔
    ∀ (i j : Fin vs.length), i ≠ j → a.getD i.val false → a.getD j.val false →
      (vs.get i, vs.get j) ∈ edges ∨ (vs.get j, vs.get i) ∈ edges := by
  rw [List.any_eq_false]
  constructor
  · intro h i j hij hi hj
    by_contra! none
    have hmem := (mem_forbiddenPairs vs edges i j).mpr
      ⟨⟨i.isLt, j.isLt⟩, fun e => hij (Fin.ext e), by simpa only [read] using none⟩
    exact h _ hmem (Bool.and_eq_true_iff.mpr ⟨hi, hj⟩)
  · rintro h ⟨i, j⟩ hmem hboth
    obtain ⟨⟨hi, hj⟩, hij, h₁, h₂⟩ := (mem_forbiddenPairs ..).mp hmem
    obtain ⟨hi', hj'⟩ := Bool.and_eq_true_iff.mp hboth
    have hex := h ⟨i, hi⟩ ⟨j, hj⟩ (fun e => hij (congrArg Fin.val e)) hi' hj'
    rw [← read, ← read] at hex
    exact hex.elim h₁ h₂

private theorem compact_iff_assignment (vs : List ℕ) (edges : List (ℕ × ℕ)) (k : ℕ)
    (hd : vs.Nodup) :
    (∃ s : List ℕ, s.Nodup ∧ s.length = k ∧ (∀ u ∈ s, u ∈ vs) ∧
      ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (u, v) ∈ edges ∨ (v, u) ∈ edges) ↔
    ∃ a : List Bool, a.length = vs.length ∧ (a.filter id).length = k ∧
      (forbiddenPairs vs edges).any (clashes a) = false := by
  constructor
  · rintro ⟨s, hs, hk, hv, hedges⟩
    let pred := fun x : ℕ => decide (x ∈ s)
    have hp : (vs.filter pred).Perm s := by
      apply (List.perm_ext_iff_of_nodup (hd.filter _) hs).mpr
      intro x
      simp [pred, and_iff_right_of_imp (hv x)]
    refine ⟨vs.map pred, by simp, ?_, (noViolation_iff ..).mpr ?_⟩
    · simpa [List.filter_map] using hp.length_eq.trans hk
    · intro i j hij hi hj
      have mem (b : Fin vs.length) (hb : (vs.map pred).getD b.val false = true) :
          vs.get b ∈ s := by
        rw [List.getD_eq_getElem _ _ (by simp)] at hb
        simpa [pred] using hb
      exact hedges _ (mem i hi) _ (mem j hj) (fun h => hij (hd.get_inj_iff.mp h))
  · rintro ⟨a, ha, hw, hOK⟩
    let idx := (List.finRange vs.length).filter fun i => a.getD i.val false
    let s := idx.map vs.get
    have hnodup : idx.Nodup := (List.nodup_finRange _).filter _
    have hlen : idx.length = (a.filter id).length := by
      let readBit := fun i : Fin vs.length => a.getD i.val false
      have hv : (List.finRange vs.length).map readBit = a := by
        apply List.ext_getElem (by simp [ha])
        intro i hi hi'
        simp [readBit, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi']
      rw [← hv, List.filter_map, List.length_map]
      rfl
    refine ⟨s, hnodup.map (fun _ _ h => hd.get_inj_iff.mp h),
      by simpa [s] using hlen.trans hw, ?_, ?_⟩
    · rintro _ hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact vs.get_mem i
    · rintro _ hu _ hv hne
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact (noViolation_iff ..).mp hOK i j (fun h => hne (congrArg vs.get h))
        (List.mem_filter.mp hi).2 (List.mem_filter.mp hj).2

/-- Total map on encoded inputs. Decode failures are sent to an empty circuit (no output);
the weight parameter is carried through unchanged. -/
def reduce (x : List Bool) : List Bool :=
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | none => MetaMathlibExt.BitstringEncoding.bitEncode ((0, []) : ℕ × List WCGate)
  | some (n, edges) =>
    let vs := vertices n edges
    MetaMathlibExt.BitstringEncoding.bitEncode
      (vs.length, exclusionCircuit vs.length (forbiddenPairs vs edges))

/-- The explicit compact construction preserves acceptance for all bitstrings.
The target has weft at most one, depth at most three, and the original weight. -/
theorem reduce_correct (x : List Bool) (k : ℕ) :
    CliqueParam x k ↔ WeightedCircuitSat 1 3 (reduce x) k := by
  classical
  unfold CliqueParam reduce WeightedCircuitSat
  cases hd : MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | none => simp [MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode, wcCircuitEval, circuitEval]
  | some data =>
    obtain ⟨n, edges⟩ := data
    simp only [MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode, decide_eq_true_eq]
    let vs := vertices n edges
    let ps := forbiddenPairs vs edges
    have hb : ∀ p ∈ ps, p.1 < vs.length ∧ p.2 < vs.length := by
      rintro ⟨i, j⟩ h
      exact ((mem_forbiddenPairs ..).mp h).1
    have hev (a : List Bool) (ha : a.length = vs.length) :
        (wcCircuitEval (exclusionCircuit vs.length ps) a).getLast? =
        some (!ps.any (clashes a)) := by
      simpa only [ha] using exclusionCircuit_eval a ps (ha ▸ hb)
    rw [clique_iff_compact, compact_iff_assignment _ _ _ (vertices_nodup ..)]
    constructor
    · rintro ⟨a, ha, hw, hok⟩
      refine ⟨exclusionCircuit_wellFormed _ _ hb, exclusionCircuit_weft _ _ hb,
        exclusionCircuit_depth _ _ hb, a, ha, hw, ?_⟩
      rw [hev a ha, show ps.any (clashes a) = false from hok]
      rfl
    · rintro ⟨_, _, _, a, ha, hw, hout⟩
      refine ⟨a, ha, hw,?_⟩
      rw [hev a ha] at hout
      simpa using hout

/-- A polynomial-time machine for the encoded transformation completes the membership
direction, preserving the original weight and using the fixed circuit depth three. -/
theorem clique_mem_wLevel_of_isPolyTime (hr : ComplexityTheory.IsPolyTime reduce) :
    CliqueParam ∈ WLevel 1 :=
  ⟨3, (FPTReduces.refl CliqueParam).postcomp_instance hr reduce_correct⟩

end CliqueMembership
end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
