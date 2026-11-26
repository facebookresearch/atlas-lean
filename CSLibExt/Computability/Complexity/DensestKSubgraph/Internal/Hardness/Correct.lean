/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Certificate
public import CSLibExt.Computability.Complexity.Karp.CliqueVerify
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Nat.Choose.Basic

/-!
# Combinatorial correctness of the CLIQUE map

This module proves acceptance preservation only; `Reduction` proves polynomial-time computability.
-/

namespace Cslib.Complexity.DensestKSubgraph.Internal.CliqueCorrect

open MetaMathlibExt BitstringEncoding Cslib.Complexity.Karp
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph

/- Translate the true entries of the Karp adjacency bits to an oriented edge list. -/
@[expose] public def edgesOfBits (n : ℕ) (bits : List Bool) : List (ℕ × ℕ) :=
  markedEdges (pairs n) bits

private theorem edges_sublist (n : ℕ) (bits : List Bool) :
    (edgesOfBits n bits).Sublist (pairs n) := by
  unfold edgesOfBits
  generalize pairs n = es
  induction es generalizing bits with
  | nil => simp [markedEdges]
  | cons a l ih =>
    cases bits with
    | nil => simp [markedEdges]
    | cons b w =>
      cases b
      · simpa [markedEdges] using (ih w).cons a
      · simpa [markedEdges] using (ih w).cons_cons a

private theorem mem_edges {n u v : ℕ} {bits : List Bool}
    (hb : bits.length = (pairs n).length) (huv : u < v) (hv : v < n) :
    (u, v) ∈ edgesOfBits n bits ↔ adjBits n bits u v = true := by
  have hkeys : ((pairs n).zip bits).map Prod.fst = pairs n := List.map_fst_zip (by omega)
  have hi (b : Bool) (he : ((u, v), b) ∈ (pairs n).zip bits) :
      adjBits n bits u v = b := by
    rw [adjBits, min_eq_left huv.le, max_eq_right huv.le,
      KGVerify.lookup_of_mem (by rw [hkeys]; exact pairs_nodup n) he]
    rfl
  simp only [edgesOfBits, markedEdges, List.mem_filterMap]
  constructor
  · rintro ⟨⟨p, b⟩, he, hb'⟩
    cases b with
    | false => exact False.elim (by cases hb')
    | true =>
      obtain rfl : p = (u, v) := Option.some.inj hb'
      exact hi true he
  · intro h
    have hm : (u, v) ∈ ((pairs n).zip bits).map Prod.fst := by
      rw [hkeys]
      exact mem_pairs.mpr ⟨huv, hv⟩
    obtain ⟨⟨p, b⟩, he, rfl : p = (u, v)⟩ := List.mem_map.mp hm
    have hbt : b = true := (hi b he).symm.trans h
    subst b
    exact ⟨((u, v), true), he, rfl⟩

private theorem edge_increasing {n : ℕ} {bits : List Bool} {e : ℕ × ℕ}
    (he : e ∈ edgesOfBits n bits) : e.1 < e.2 ∧ e.2 < n := by
  have h : e ∈ pairs n := (edges_sublist n bits).subset he
  obtain ⟨u, v⟩ := e
  exact mem_pairs.mp h

private theorem wellFormed_edges (n k : ℕ) (bits : List Bool) :
    WellFormed (n, edgesOfBits n bits, k, k.choose 2) := by
  refine ⟨(pairs_nodup n).sublist (edges_sublist n bits), fun e he => ?_⟩
  have h := edge_increasing he
  exact ⟨h.1.trans h.2, h.2, h.1.ne, fun hr => h.1.not_gt (edge_increasing hr).1⟩

private def endsPair (e : ℕ × ℕ) : Finset ℕ := {e.1, e.2}

private theorem endsPair_inj {e f : ℕ × ℕ} (he : e.1 < e.2) (hf : f.1 < f.2)
    (h : endsPair e = endsPair f) : e = f := by
  have h₁ : e.1 = f.1 ∨ e.1 = f.2 := by
    have hm : e.1 ∈ endsPair e := by simp [endsPair]
    rw [h] at hm
    simpa [endsPair] using hm
  have h₂ : e.2 = f.1 ∨ e.2 = f.2 := by
    have hm : e.2 ∈ endsPair e := by simp [endsPair]
    rw [h] at hm
    simpa [endsPair] using hm
  apply Prod.ext <;> omega

private theorem endsPair_image_card {es : List (ℕ × ℕ)} (hn : es.Nodup)
    (hinc : ∀ e ∈ es, e.1 < e.2) : (es.toFinset.image endsPair).card = es.length := by
  rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hn]
  intro e he f hf h
  exact endsPair_inj (hinc e (List.mem_toFinset.mp he)) (hinc f (List.mem_toFinset.mp hf)) h

private theorem endsPair_image_subset {es : List (ℕ × ℕ)} {S : Finset ℕ}
    (hinc : ∀ e ∈ es, e.1 < e.2) (hS : ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S) :
    es.toFinset.image endsPair ⊆ S.powersetCard 2 := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  have h := hS e (List.mem_toFinset.mp he)
  have hne := (hinc e (List.mem_toFinset.mp he)).ne
  refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_eq_two.mpr ⟨_, _, hne, rfl⟩⟩
  simpa [endsPair, Finset.insert_subset_iff] using h

private theorem lt_pair_mem_of_cover {es : List (ℕ × ℕ)} {S : Finset ℕ}
    (hinc : ∀ e ∈ es, e.1 < e.2) (hS : S.powersetCard 2 ⊆ es.toFinset.image endsPair)
    {u v : ℕ} (hu : u ∈ S) (hv : v ∈ S) (h : u < v) : (u, v) ∈ es := by
  have hp : endsPair (u, v) ∈ S.powersetCard 2 := by
    refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_eq_two.mpr ⟨u, v, h.ne, rfl⟩⟩
    simp [endsPair, Finset.insert_subset_iff, hu, hv]
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (hS hp)
  have he' : e ∈ es := List.mem_toFinset.mp he
  rwa [endsPair_inj (hinc e he') h heq] at he'

private theorem exists_natClique_iff (n k : ℕ) (bits : List Bool) :
    (∃ s, (toGraph n bits).IsNClique k s) ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v < n) ∧ S.card = k ∧
        ∀ u ∈ S, ∀ v ∈ S, u < v → adjBits n bits u v = true := by
  classical
  let em : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.map em, ?_, by simpa using hs.card_eq, ?_⟩
    · intro v hv
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hv
      exact u.isLt
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      exact (hs.isClique ha hb (fun h => huv.ne (congrArg em h))).2
  · rintro ⟨S, hS, hc, h⟩
    let s := S.preimage (Fin.val : Fin n → ℕ) Fin.val_injective.injOn
    have hsS : (S : Set ℕ) ⊆ Set.range (Fin.val : Fin n → ℕ) :=
      fun v hv => ⟨⟨v, hS v hv⟩, rfl⟩
    refine ⟨s, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a.val ∈ S := Finset.mem_preimage.mp ha
      have hb' : b.val ∈ S := Finset.mem_preimage.mp hb
      refine ⟨hab, ?_⟩
      rcases lt_or_gt_of_ne (fun h' => hab (Fin.ext h')) with hl | hl
      · exact h _ ha' _ hb' hl
      · rw [adjBits_comm]
        exact h _ hb' _ ha' hl
    · simpa only [s, Finset.card_preimage, Finset.filter_true_of_mem (fun v hv => hsS hv)] using hc

/- At the clique threshold the graph converted from pair bits has a feasible solution exactly
when the graph has a clique of the requested size. -/
public theorem feasible_edges_iff {n k : ℕ} {bits : List Bool}
    (hb : bits.length = (pairs n).length) :
    DensestKSubgraphFeasible (n, edgesOfBits n bits, k, k.choose 2) ↔
      ∃ s, (toGraph n bits).IsNClique k s := by
  rw [exists_natClique_iff]
  constructor
  · rintro ⟨S, hSn, hSc, es, hsub, hm, hS⟩
    have hinc (e : ℕ × ℕ) (he : e ∈ es) := (edge_increasing (hsub.subset he)).1
    have hnd := (pairs_nodup n).sublist (hsub.trans (edges_sublist n bits))
    have hle := endsPair_image_subset hinc hS
    have hcard : (S.powersetCard 2).card ≤ (es.toFinset.image endsPair).card := by
      rwa [Finset.card_powersetCard, hSc, endsPair_image_card hnd hinc]
    have hcov := Finset.eq_of_subset_of_card_le hle hcard
    refine ⟨S, hSn, hSc, ?_⟩
    intro u hu v hv huv
    exact (mem_edges hb huv (hSn _ hv)).mp
      (hsub.subset (lt_pair_mem_of_cover hinc hcov.ge hu hv huv))
  · rintro ⟨S, hSn, hSc, hcl⟩
    let es := (edgesOfBits n bits).filter fun e => e.1 ∈ S && e.2 ∈ S
    have hsub : es.Sublist (edgesOfBits n bits) := List.filter_sublist
    have hinc (e : ℕ × ℕ) (he : e ∈ es) := (edge_increasing (hsub.subset he)).1
    have hnd := (pairs_nodup n).sublist (hsub.trans (edges_sublist n bits))
    suffices hcov : S.powersetCard 2 ⊆ es.toFinset.image endsPair by
      refine ⟨S, hSn, hSc, es, hsub, ?_, ?_⟩
      · simpa only [Finset.card_powersetCard, hSc, endsPair_image_card hnd hinc] using
          Finset.card_le_card hcov
      · intro e he
        simpa [es] using (List.mem_filter.mp he).2
    intro p hp
    obtain ⟨hps, hpc⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hpc
    have hu : u ∈ S := hps (by simp)
    have hv : v ∈ S := hps (by simp)
    have add (a b : ℕ) (ha : a ∈ S) (hb' : b ∈ S) (h : a < b) :
        endsPair (a, b) ∈ es.toFinset.image endsPair := by
      have hm := (mem_edges hb h (hSn _ hb')).mpr (hcl _ ha _ hb' h)
      exact Finset.mem_image.mpr ⟨(a, b), List.mem_toFinset.mpr (by simp [es, hm, ha, hb']), rfl⟩
    rcases lt_or_gt_of_ne huv with h | h
    · exact add u v hu hv h
    · simpa [endsPair, Finset.pair_comm] using add v u hv hu h

/- A malformed CLIQUE encoding maps to the empty bitstring. A valid encoding maps to the
canonical tuple of the vertex count, true edges, target size, and clique threshold. -/
@[expose] public def cliqueToDensest (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) =>
    if bits.length = (pairs n).length then bitEncode (n, edgesOfBits n bits, k, k.choose 2) else []
  | none => []

/- The map preserves acceptance, including incomplete or overlong adjacency data. -/
public theorem cliqueDec_eq_densestKSubgraphDec (x : List Bool) :
    cliqueDec x = densestKSubgraphDec (cliqueToDensest x) := by
  have hfalse : densestKSubgraphDec [] = false := rfl
  cases hx : decodeKG x with
  | none =>
    rw [cliqueToDensest, hx, hfalse]
    exact kgDec_of_decodeKG_eq_none hx
  | some v =>
    obtain ⟨k, n, bits⟩ := v
    rw [cliqueToDensest, hx]
    rw [decodeKG_eq_some_iff] at hx
    subst x
    apply Bool.eq_iff_iff.mpr
    change kgDec _ _ = true ↔ _
    rw [kgDec_encodeKG_eq_true]
    by_cases h : bits.length = (pairs n).length
    · simp only [h, true_and, ite_true, densestKSubgraphDec, bitDecode_bitEncode, decide_eq_true_eq]
      exact (feasible_edges_iff h).symm.trans (and_iff_right (wellFormed_edges n k bits)).symm
    · simp [h, hfalse]

end Cslib.Complexity.DensestKSubgraph.Internal.CliqueCorrect
