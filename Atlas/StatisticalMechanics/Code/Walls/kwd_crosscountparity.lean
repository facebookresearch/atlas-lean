/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanEnclosure

open Finset Set SimpleGraph
open StatMech.Lattice

namespace StatMech.Walls










def kwd_crossCount {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y : V} (w : G.Walk x y) : ℕ :=
  w.edges.countP B

@[simp] theorem kwd_crossCount_nil {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    (x : V) :
    kwd_crossCount B (SimpleGraph.Walk.nil : G.Walk x x) = 0 := by
  simp [kwd_crossCount]



theorem kwd_crossCount_cons {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {a b c : V} (hab : G.Adj a b) (p : G.Walk b c) :
    kwd_crossCount B (SimpleGraph.Walk.cons hab p)
      = (if B s(a, b) then 1 else 0) + kwd_crossCount B p := by
  rw [kwd_crossCount, kwd_crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : B s(a, b)
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring


theorem kwd_crossCount_append {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    kwd_crossCount B (p.append q) = kwd_crossCount B p + kwd_crossCount B q := by
  rw [kwd_crossCount, kwd_crossCount, kwd_crossCount,
    SimpleGraph.Walk.edges_append, List.countP_append]


theorem kwd_crossCount_reverse {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y : V} (w : G.Walk x y) :
    kwd_crossCount B w.reverse = kwd_crossCount B w := by
  rw [kwd_crossCount, kwd_crossCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]





def kwd_sideBoundary {V : Type*} (S : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => S x != S y, by
    intro x y
    simp only
    cases S x <;> cases S y <;> rfl⟩

@[simp] theorem kwd_sideBoundary_mk {V : Type*} (S : V → Bool) (x y : V) :
    kwd_sideBoundary S s(x, y) = (S x != S y) := rfl












theorem kwd_crossCount_parity {V : Type*} {G : SimpleGraph V} (S : V → Bool)
    {x y : V} (w : G.Walk x y) :
    Even (kwd_crossCount (kwd_sideBoundary S) w) ↔ (S x = S y) := by
  induction w with
  | nil => simp [kwd_crossCount]
  | @cons a b c hab p ih =>
    rw [kwd_crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
    rw [kwd_crossCount] at ih
    by_cases hbd : kwd_sideBoundary S s(a, b) = true
    · rw [if_pos hbd, Nat.even_add_one, ih]
      rw [kwd_sideBoundary_mk] at hbd
      cases ha : S a <;> cases hb : S b <;> cases hc : S c <;> simp_all
    · rw [if_neg hbd, add_zero, ih]
      rw [kwd_sideBoundary_mk] at hbd
      cases ha : S a <;> cases hb : S b <;> cases hc : S c <;> simp_all



theorem kwd_crossCount_parity_eq_of_sameEndpoints {V : Type*} {G : SimpleGraph V}
    (S : V → Bool) {x y : V} (w₁ w₂ : G.Walk x y) :
    kwd_crossCount (kwd_sideBoundary S) w₁ % 2
      = kwd_crossCount (kwd_sideBoundary S) w₂ % 2 := by
  have h1 := kwd_crossCount_parity S w₁
  have h2 := kwd_crossCount_parity S w₂
  rw [Nat.even_iff] at h1 h2
  by_cases hP : S x = S y
  · rw [h1.mpr hP, h2.mpr hP]
  · have e1 : kwd_crossCount (kwd_sideBoundary S) w₁ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one _ with h | h
      · exact absurd (h1.mp h) hP
      · exact h
    have e2 : kwd_crossCount (kwd_sideBoundary S) w₂ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one _ with h | h
      · exact absurd (h2.mp h) hP
      · exact h
    rw [e1, e2]



theorem kwd_crossCount_even_of_closed {V : Type*} {G : SimpleGraph V} (S : V → Bool)
    {x : V} (w : G.Walk x x) :
    Even (kwd_crossCount (kwd_sideBoundary S) w) :=
  (kwd_crossCount_parity S w).mpr rfl






open Classical in



noncomputable def kwd_crossCountZ2 (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (bdEdge S e))

open Classical in


noncomputable def kwd_sideBool (S : Set (Site 2)) : Site 2 → Bool := fun v => decide (v ∈ S)

@[simp] theorem kwd_sideBool_eq_true (S : Set (Site 2)) (v : Site 2) :
    kwd_sideBool S v = true ↔ v ∈ S := by
  classical
  unfold kwd_sideBool; rw [decide_eq_true_iff]




theorem kwd_crossCountZ2_eq (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    kwd_crossCountZ2 S w
      = kwd_crossCount (kwd_sideBoundary (kwd_sideBool S)) w := by
  classical
  unfold kwd_crossCountZ2 kwd_crossCount
  apply List.countP_congr
  intro e _
  induction e using Sym2.ind with
  | _ a b =>
    rw [kwd_sideBoundary_mk, bdEdge_mk]
    unfold kwd_sideBool
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]






theorem kwd_crossCountZ2_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (kwd_crossCountZ2 S w) ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  rw [kwd_crossCountZ2_eq, kwd_crossCount_parity (kwd_sideBool S) w]
  rw [show (kwd_sideBool S x = kwd_sideBool S y) ↔ (x ∈ S ↔ y ∈ S) from ?_]
  unfold kwd_sideBool
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]






theorem kwd_crossCountZ2_even_of_closed (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) :
    Even (kwd_crossCountZ2 S w) :=
  (kwd_crossCountZ2_parity S w).mpr Iff.rfl






theorem kwd_crossCountZ2_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (kwd_crossCountZ2 S w) := by
  rw [kwd_crossCountZ2_parity]
  intro h
  exact hy (h.mp hx)

end StatMech.Walls
