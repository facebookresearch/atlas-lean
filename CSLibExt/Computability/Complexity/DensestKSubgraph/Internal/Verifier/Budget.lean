/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Row

/-! # Dictionary and runtime bounds for the marked scan -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierBudget

open MetaMathlibExt BitstringEncoding VerifierSpec GraphKeys

/- Every visited key is charged to an explicitly encoded edge; every vertex is charged to one
of that edge's two endpoints. Neither the header values nor the endpoints are expanded to unary. -/
structure History (B : ℕ) (seen : Seen) (es : List (ℕ × ℕ)) : Prop where
  nodup : seen.edges.Nodup
  volume : seen.edges.length + es.length ≤ B
  selected : seen.selected ≤ seen.edges.length
  vertices : seen.vertices.length ≤ 2 * seen.edges.length
  edgeBits : ∀ e ∈ seen.edges, e.1.size ≤ B ∧ e.2.size ≤ B
  vertexBits : ∀ v ∈ seen.vertices, v.size ≤ B

/- The exact empty scan history satisfies the invariant. -/
theorem history_empty (B : ℕ) (es : List (ℕ × ℕ)) (h : es.length ≤ B) :
    History B ⟨[], [], 0⟩ es := by
  constructor <;> simp_all

private theorem insert_length (xs : List ℕ) (x : ℕ) :
    (insertKey xs x).length ≤ xs.length + 1 := by
  unfold insertKey
  split <;> simp

private theorem insert_bits {xs : List ℕ} {x B : ℕ} (h : ∀ v ∈ xs, v.size ≤ B)
    (hx : x.size ≤ B) : ∀ v ∈ insertKey xs x, v.size ≤ B := by
  unfold insertKey
  split
  · exact h
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h v hv
    · obtain rfl := List.mem_singleton.mp hv
      exact hx

private theorem key_bits {e : ℕ × ℕ} {B : ℕ} (h : e.1.size ≤ B ∧ e.2.size ≤ B) :
    (key e).1.size ≤ B ∧ (key e).2.size ≤ B := by
  rcases le_total e.1 e.2 with he | he
  · simpa only [key, min_eq_left he, max_eq_right he] using h
  · simpa only [key, min_eq_right he, max_eq_left he] using h.symm

/- A successful iteration preserves uniqueness and all physical size bounds. -/
theorem history_next {B : ℕ} {seen : Seen} {e : ℕ × ℕ} {es : List (ℕ × ℕ)}
    (h : History B seen (e :: es)) (he : e.1.size ≤ B ∧ e.2.size ≤ B)
    (hk : key e ∉ seen.edges) (b : Bool) : History B (advance seen e b) es := by
  constructor
  · refine List.nodup_append.mpr ⟨h.nodup, by simp, ?_⟩
    intro a ha c hc eq
    obtain rfl := List.mem_singleton.mp hc
    exact hk (eq ▸ ha)
  · have hv := h.volume
    simp only [advance, List.length_append, List.length_cons, List.length_nil] at hv ⊢
    omega
  · have hs := h.selected
    cases b <;> simp only [advance, Bool.toNat_true, Bool.toNat_false, List.length_append,
      List.length_singleton] <;> omega
  · have hv := h.vertices
    have h₁ := insert_length seen.vertices e.1
    have h₂ := insert_length (insertKey seen.vertices e.1) e.2
    cases b <;> simp only [advance, mark, Bool.false_eq_true, ↓reduceIte, List.length_append,
      List.length_singleton] <;> omega
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.edgeBits p hp
    · obtain rfl := List.mem_singleton.mp hp
      exact key_bits he
  · cases b
    · exact h.vertexBits
    · exact insert_bits (insert_bits h.vertexBits he.1) he.2

/- Terminal work uses only the three header bit lengths and the physical unary counts. -/
def finish (B : ℕ) : ℕ := 10000 * (B + 1)

/- The per-edge budget includes reading one mark and its two framed endpoints. -/
def row (B : ℕ) : ℕ := 1000 * (B + 1) ^ 2

/- The two bound comparisons, canonical key, and three lookups are paid by raw sizes. -/
theorem row_le {B n : ℕ} {seen : Seen} {e : ℕ × ℕ} {es : List (ℕ × ℕ)}
    (h : History B seen (e :: es)) (hn : n.size ≤ B) (he : e.1.size ≤ B ∧ e.2.size ≤ B) :
    (2 * (e.1.size + e.2.size) + 5) + VerifierRow.cost n e seen ≤ row B := by
  have hcount : seen.edges.length ≤ B := by have := h.volume; omega
  have hvs : seen.vertices.length ≤ 2 * B := by have := h.vertices; omega
  have hG : VerifierRow.tableLen (seen.edges.map bitEncode) ≤ B * (4 * B + 2) := by
    have ht := VerifierRow.tableLen_le (seen.edges.map bitEncode) (4 * B + 1) (by
      intro word hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      have hf := h.edgeBits p hp
      have hb := BinaryNatEncoding.bitEncode_pair_nat_length_le p
      omega)
    rw [List.length_map] at ht
    exact ht.trans (Nat.mul_le_mul_right _ hcount)
  have hV : VerifierRow.tableLen (seen.vertices.map bitEncode) ≤ 2 * B * (B + 1) := by
    have ht := VerifierRow.tableLen_le (seen.vertices.map bitEncode) B (by
      intro word hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      simpa only [BinaryNatEncoding.length_bitEncode] using h.vertexBits _ hu)
    rw [List.length_map] at ht
    exact ht.trans (Nat.mul_le_mul_right _ hvs)
  unfold VerifierRow.cost row
  have hab : e.1.size + e.2.size ≤ 2 * B := by omega
  have hpay : 2 * (e.1.size + e.2.size) + 5 +
        (8 * (VerifierRow.tableLen (seen.edges.map bitEncode) +
          2 * VerifierRow.tableLen (seen.vertices.map bitEncode)) +
          100 * (n.size + e.1.size + e.2.size + 1)) ≤
        (4 * B + 5) + (8 * (B * (4 * B + 2) + 2 * (2 * B * (B + 1))) + 100 * (3 * B + 1)) := by
    omega
  exact hpay.trans (by nlinarith [Nat.zero_le B])

/- Charge cursor termination and threshold testing to the raw-size invariant. -/
theorem finish_le {B n k m : ℕ} {seen : Seen} {es : List (ℕ × ℕ)}
    (h : History B seen es) (hn : n.size ≤ B) (hk : k.size ≤ B) (hm : m.size ≤ B) :
    1 + 1500 * (n.size + k.size + m.size + seen.selected + seen.vertices.length + 1) ≤
      finish B := by
  have hcount := h.volume
  have hsc := h.selected
  have hvc := h.vertices
  unfold finish
  omega

/- A cursor read on any malformed witness costs at most its phase budget. -/
theorem one_le (B : ℕ) : 1 ≤ finish B := by unfold finish; omega

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierBudget
