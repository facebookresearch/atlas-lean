/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































































import Code.Percolation.Exploration
import Code.Percolation.TildePc

open MeasureTheory Function Set
open scoped NNReal ENNReal
open StatMech
open Finset

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}







def withinConnEvent (d : ℕ) (S : Set (Site d)) (o x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ (ho : o ∈ S) (hx : x ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨x, hx⟩}

@[simp]
theorem mem_withinConnEvent {S : Set (Site d)} {o x : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ withinConnEvent d S o x ↔
      ∃ (ho : o ∈ S) (hx : x ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨x, hx⟩ :=
  Iff.rfl




noncomputable def edgesWithinFinset (S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (S ×ˢ S).image (fun p => s(p.1, p.2))

theorem mem_edgesWithinFinset {S : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ edgesWithinFinset S ↔ ∃ x ∈ S, ∃ y ∈ S, e = s(x, y) := by
  simp only [edgesWithinFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩; exact ⟨x, hx, y, hy, he.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩






theorem withinConn_congr (S : Finset (Site d)) (o x : Site d)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (edgesWithinFinset S : Set (Sym2 (Site d))), ω e = ω' e) :
    ω ∈ withinConnEvent d (S : Set (Site d)) o x ↔
      ω' ∈ withinConnEvent d (S : Set (Site d)) o x := by
  have hcoord : ∀ a b : Site d, a ∈ (S : Set (Site d)) → b ∈ (S : Set (Site d)) →
      ω s(a, b) = ω' s(a, b) := by
    intro a b ha hb
    apply h
    rw [Finset.mem_coe, mem_edgesWithinFinset]
    exact ⟨a, by simpa using ha, b, by simpa using hb, rfl⟩
  have hG : openSubgraphInduce d ω (S : Set (Site d))
      = openSubgraphInduce d ω' (S : Set (Site d)) := by
    apply SimpleGraph.ext
    ext aa bb
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord aa bb aa.2 bb.2]
  unfold withinConnEvent ConnectedWithin
  simp only [Set.mem_setOf_eq, hG]






theorem withinConn_dependsOn (S : Finset (Site d)) (o x : Site d) :
    DependsOn ((withinConnEvent d (S : Set (Site d)) o x).indicator (fun _ => (1 : ℝ)))
      ((edgesWithinFinset S : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff := withinConn_congr S o x (fun e he => h e he)
  by_cases hω : ω ∈ withinConnEvent d (S : Set (Site d)) o x
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]






theorem withinConnEvent_eq (S : Finset (Site d)) (x : Site d)
    (h0 : origin d ∈ (S : Set (Site d))) (hx : x ∈ (S : Set (Site d))) :
    withinConnEvent d (S : Set (Site d)) (origin d) x
      = {ω | ConnectedWithin d ω (S : Set (Site d)) ⟨origin d, h0⟩ ⟨x, hx⟩} := by
  ext ω
  simp only [mem_withinConnEvent, Set.mem_setOf_eq]
  exact ⟨fun ⟨_, _, hconn⟩ => hconn, fun hconn => ⟨h0, hx, hconn⟩⟩





theorem connWithinProb_eq (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) (x : Site d)
    (h0 : origin d ∈ (S : Set (Site d))) (hx : x ∈ (S : Set (Site d))) :
    connWithinProb d p hp S x
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) x) := by
  have h0' : origin d ∈ S := by simpa using h0
  have hx' : x ∈ S := by simpa using hx
  unfold connWithinProb
  rw [dif_pos h0', dif_pos hx', withinConnEvent_eq S x h0 hx]




















theorem withinConn_indep (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) (o x : Site d)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (edgesWithinFinset S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) o x ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  indep_cylinder_inf p hp _ B (edgesWithinFinset S) U hdisj
    (withinConn_dependsOn S o x) hB




theorem boundaryEdges_fst_mem {S : Finset (Site d)} {e : Site d × Site d}
    (he : e ∈ boundaryEdges d S) : e.1 ∈ S := by
  unfold boundaryEdges at he
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨t, ⟨⟨ht1, _, _⟩, _⟩, het⟩ := he
  rw [← het]; exact ht1













theorem phi_reassembly (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (h0 : origin d ∈ S)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (edgesWithinFinset S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (p : ℝ) * ∑ e ∈ boundaryEdges d S,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ B)
      = phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
  have h0c : origin d ∈ (S : Set (Site d)) := by simpa using h0
  unfold phi
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxc : e.1 ∈ (S : Set (Site d)) := by simpa using boundaryEdges_fst_mem he
  rw [withinConn_indep p hp S (origin d) e.1 B U hdisj hB,
      connWithinProb_eq p hp S e.1 h0c hxc]












theorem phi_surface_summand (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (h0 : origin d ∈ S) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (edgesWithinFinset S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (1 / (1 - (p : ℝ))) * ∑ e ∈ boundaryEdges d S,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ B)
      = (1 / ((p : ℝ) * (1 - (p : ℝ))))
          * (phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B) := by
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have h1mp : (1 - (p : ℝ)) ≠ 0 := by linarith
  set A : ℝ := ∑ e ∈ boundaryEdges d S,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ B) with hA
  have hreassembly :
      (p : ℝ) * A = phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
    phi_reassembly p hp S h0 B U hdisj hB
  rw [← hreassembly]
  field_simp

end Percolation

end StatMech
