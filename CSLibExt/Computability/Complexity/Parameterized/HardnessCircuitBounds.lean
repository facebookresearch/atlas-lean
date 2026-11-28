/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitMachine

/-!
# Clause width and literal range in the serialized normalizer

These bounds apply to the actual lists of clauses and literals produced before
any duplicates are removed. They do not require the input circuit to be valid.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine

open NormalFormMachine (combineFamilies binaryAnd binaryOr distribute)

/-- Every clause is short and mentions only declared variables. -/
def Fits (n w : ℕ) (a : Family) : Prop :=
  ∀ p ∈ a, ∀ c ∈ p, c.length ≤ w ∧ ∀ l ∈ c, l.1 < n

private theorem fits_mono {n u v : ℕ} {a : Family} (h : Fits n u a) (huv : u ≤ v) :
    Fits n v a := fun p hp c hc => ⟨((h p hp c hc).1).trans huv, (h p hp c hc).2⟩

private theorem fits_constant (n w : ℕ) (b p : Bool) : Fits n w (constant b p) := by
  unfold constant
  split <;> simp [Fits]

private theorem fits_combine {n w} (b : Bool) (xs : List Family) (h : ∀ p ∈ xs, Fits n w p) :
    Fits n (w+w) (combineFamilies b xs) := by
  match xs with
  | [] => cases b <;> simp [Fits, combineFamilies]
  | [a] => exact fits_mono (h a (by simp)) (by omega)
  | [a,b'] =>
    intro p hp c hc
    cases b with
    | false =>
      obtain ⟨q, hq, hrest⟩ := List.mem_flatMap.mp hp
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrest
      obtain ⟨u, hu, hrest⟩ := List.mem_flatMap.mp hc
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hrest
      have hq' := h a (by simp) q hq u hu
      have hr' := h b' (by simp) r hr v hv
      exact ⟨by simpa using Nat.add_le_add hq'.1 hr'.1, fun l hl =>
        (List.mem_append.mp hl).elim (hq'.2 l) (hr'.2 l)⟩
    | true =>
      obtain ⟨q, hq, hrest⟩ := List.mem_flatMap.mp hp
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrest
      rcases List.mem_append.mp hc with hc | hc
      · exact fits_mono (h a (by simp)) (by omega) q hq c hc
      · exact fits_mono (h b' (by simp)) (by omega) r hr c hc
  | a :: z :: v :: tail =>
    let xs := a :: z :: v :: tail
    intro p hp c hc
    cases b with
    | false =>
      obtain ⟨u, hu, hp⟩ := List.mem_flatten.mp hp
      exact fits_mono (h _ hu) (by omega) p hp c hc
    | true =>
      obtain rfl : p = (xs.map (·.headD [])).flatten := List.mem_singleton.mp hp
      obtain ⟨q, hq, hc⟩ := List.mem_flatten.mp hc
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      cases u with
      | nil => simp at hc
      | cons p ps => exact fits_mono (h _ hu) (by omega) p (by simp) c hc

private theorem fits_gate {n w : ℕ} (prev : List Node)
    (h : ∀ x ∈ prev, ∀ p, Fits n w (atPolarity p x)) (g : WCGate) (p : Bool) :
    Fits n (max 1 (w+w)) (gate n prev g p) := by
  have read (i : ℕ) (p : Bool) : Fits n w (atPolarity p (prev.getD i falseNode)) := by
    by_cases hi : i < prev.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem _) p
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
      cases p with
      | false => exact fits_constant n w false false
      | true => exact fits_constant n w false true
  have hc (b : Bool) : Fits n (max 1 (w+w))
      (combineFamilies b (g.2.map fun j => atPolarity p (prev.getD j falseNode))) := by
    apply fits_mono (fits_combine _ _ ?_) (le_max_right _ _)
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact read j p
  simp only [gate]
  split_ifs with _ _ _ _ hi _ _
  all_goals first | exact hc _ | exact fits_constant _ _ _ _ |
    exact fits_mono (read _ _) ((by omega : w ≤ w+w).trans (le_max_right _ _)) |
    simp_all [Fits]

/-- After `d+1` synchronous rounds every formula has width at most `2^d`, even counting repeated
literals. All variables of the intermediate and output families belong to the input domain. -/
theorem table_fits (n d : ℕ) (C : List WCGate) (v : Node) (hv : v ∈ table n C (d + 1))
    (p : Bool) : Fits n (2^d) (atPolarity p v) := by
  induction d generalizing v p with
  | zero =>
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
    cases p <;> exact fits_gate (w := 0) [] (by simp) g _
  | succ d ih =>
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hv
    have arith : max 1 (2^d + 2^d) ≤ 2^(d+1) := by
      rw [pow_succ, Nat.mul_two]
      have : 0 < 2^d := by positivity
      omega
    cases p <;> exact fits_mono (fits_gate _ ih g _) arith

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine
