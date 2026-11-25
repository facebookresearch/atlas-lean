/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Defs
import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds

/-! # Marked-edge certificate for DENSEST k-SUBGRAPH -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal

open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open MetaMathlibExt BitstringEncoding
open Cslib.Complexity.PolynomialEncoding (decoded_middle_list_length_le)

/- A mask selects an order-preserving sublist of its input. -/
def markedEdges (es : List (ℕ × ℕ)) (w : List Bool) : List (ℕ × ℕ) :=
  ((es.zip w).filterMap fun (e, b) => if b then some e else none)

private theorem markedEdges_sublist (es : List (ℕ × ℕ)) (w : List Bool) :
    (markedEdges es w).Sublist es := by
  induction es generalizing w with
  | nil => simp [markedEdges]
  | cons e es ih =>
    cases w with
    | nil => simp [markedEdges]
    | cons b w =>
      cases b
      · simpa [markedEdges] using (ih w).cons e
      · simpa [markedEdges] using (ih w).cons_cons e

private theorem exists_marks {es fs : List (ℕ × ℕ)} (h : fs.Sublist es) :
    ∃ w : List Bool, w.length = es.length ∧ markedEdges es w = fs := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons e _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    exact ⟨false :: w, by simp [hw], hs⟩
  | cons_cons e _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    exact ⟨true :: w, by simp [hw], by simpa [markedEdges] using congrArg (e :: ·) hs⟩

/- The only vertices a selected edge sublist forces into the solution. -/
def endpoints (es : List (ℕ × ℕ)) : Finset ℕ :=
  (es.map Prod.fst).toFinset ∪ (es.map Prod.snd).toFinset

private theorem mem_endpoints {v : ℕ} {es : List (ℕ × ℕ)} :
    v ∈ endpoints es ↔ ∃ e ∈ es, e.1 = v ∨ e.2 = v := by
  simp only [endpoints, Finset.mem_union, List.mem_toFinset, List.mem_map]
  grind

private theorem endpoints_subset {es : List (ℕ × ℕ)} {S : Finset ℕ} :
    endpoints es ⊆ S ↔ ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S := by
  refine ⟨fun h e he => ⟨h (mem_endpoints.mpr ⟨e, he, Or.inl rfl⟩),
    h (mem_endpoints.mpr ⟨e, he, Or.inr rfl⟩)⟩, ?_⟩
  intro h v hv
  obtain ⟨e, he, rfl | rfl⟩ := mem_endpoints.mp hv
  · exact (h e he).1
  · exact (h e he).2

/- A well-formed instance only needs a certificate marking its explicitly listed edges. -/
theorem feasible_iff_marks {i : DensestKSubgraphInstance} (hi : WellFormed i) :
    DensestKSubgraphFeasible i ↔
      ∃ w : List Bool, w.length = i.2.1.length ∧ i.2.2.1 ≤ i.1 ∧
        i.2.2.2 ≤ (markedEdges i.2.1 w).length ∧
        (endpoints (markedEdges i.2.1 w)).card ≤ i.2.2.1 := by
  constructor
  · rintro ⟨S, hS, hcard, es, hsub, hm, hends⟩
    obtain ⟨w, hw, rfl⟩ := exists_marks hsub
    have hn : S.card ≤ i.1 := by
      simpa using Finset.card_le_card (s := S) (t := Finset.range i.1)
        (fun v hv => Finset.mem_range.mpr (hS v hv))
    exact ⟨w, hw, hcard ▸ hn, hm,
      hcard ▸ Finset.card_le_card (endpoints_subset.mpr hends)⟩
  · rintro ⟨w, _, hk, hm, hcard⟩
    let es := markedEdges i.2.1 w
    have hsub : es.Sublist i.2.1 := markedEdges_sublist _ _
    have hr : endpoints es ⊆ Finset.range i.1 := endpoints_subset.mpr (fun e he =>
      ⟨Finset.mem_range.mpr (hi.2 e (hsub.subset he)).1,
        Finset.mem_range.mpr (hi.2 e (hsub.subset he)).2.1⟩)
    obtain ⟨S, hends, hS, hSc⟩ :=
      Finset.exists_subsuperset_card_eq hr hcard (by simpa using hk)
    exact ⟨S, fun v hv => Finset.mem_range.mp (hS hv), hSc,
      es, hsub, hm, endpoints_subset.mp hends⟩

/- Boolean well-formedness check over the explicitly stored edges. -/
def wellFormedCheck (i : DensestKSubgraphInstance) : Bool :=
  i.2.1.all (fun (u, v) => u < i.1 && v < i.1 && u != v && !(i.2.1.contains (v, u))) &&
    decide i.2.1.Nodup

private theorem wellFormedCheck_iff (i : DensestKSubgraphInstance) :
    wellFormedCheck i = true ↔ WellFormed i := by
  simp [wellFormedCheck, WellFormed, List.all_eq_true, and_assoc, and_left_comm, and_comm]

/- The marked sublist verifier specification on the exact bitstring decoder. -/
def densestCheck (x w : List Bool) : Bool :=
  match bitDecode (α := DensestKSubgraphInstance) x with
  | none => false
  | some i =>
    let es := markedEdges i.2.1 w
    wellFormedCheck i && (w.length == i.2.1.length) && (i.2.2.1 ≤ i.1) &&
      (i.2.2.2 ≤ es.length) && ((endpoints es).card ≤ i.2.2.1)

/- The marked verifier is sound and complete with at most one witness bit per input bit. -/
theorem densestKSubgraphDec_iff_marks (x : List Bool) :
    densestKSubgraphDec x = true ↔
      ∃ w : List Bool, w.length ≤ x.length ∧ densestCheck x w = true := by
  cases hx : bitDecode (α := DensestKSubgraphInstance) x with
  | none => simp [densestKSubgraphDec, densestCheck, hx]
  | some i =>
    simp only [densestKSubgraphDec, densestCheck, hx, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq, wellFormedCheck_iff]
    constructor
    · rintro ⟨h, hf⟩
      obtain ⟨w, hw, hk, hm, hc⟩ := (feasible_iff_marks h).mp hf
      obtain ⟨n, es, k, m⟩ := i
      exact ⟨w, hw.trans_le (decoded_middle_list_length_le hx), ⟨⟨⟨⟨h, hw⟩, hk⟩, hm⟩, hc⟩⟩
    · rintro ⟨w, -, ⟨⟨⟨⟨h, hw⟩, hk⟩, hm⟩, hc⟩⟩
      exact ⟨h, (feasible_iff_marks h).mpr ⟨w, hw, hk, hm, hc⟩⟩

end Cslib.Complexity.DensestKSubgraph.Internal
