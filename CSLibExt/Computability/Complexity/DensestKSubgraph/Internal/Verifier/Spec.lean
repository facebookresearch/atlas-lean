/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.GraphKeys
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Decode
import CSLibExt.Computability.Complexity.FramedCNF.Normalize

/-! # Specification and bit-length invariant for the marked edge verifier -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierSpec

open MetaMathlibExt BitstringEncoding Computability
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open GraphKeys

/- The verifier's abstract edge dictionary, vertex dictionary and selected-edge count. -/
structure Seen where
  edges : List (ℕ × ℕ) := []
  vertices : List ℕ := []
  selected : ℕ := 0

/- Locally valid graph edge. Duplicates are checked separately. -/
def Valid (n : ℕ) (e : ℕ × ℕ) : Prop := e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2

instance (n : ℕ) (e : ℕ × ℕ) : Decidable (Valid n e) :=
  inferInstanceAs (Decidable (e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2))

/- Insert both endpoints if the edge was marked. -/
def mark (seen : Seen) (e : ℕ × ℕ) (b : Bool) : List ℕ :=
  if b then insertKey (insertKey seen.vertices e.1) e.2 else seen.vertices

/- Advance the abstract dictionaries and counters by one accepted edge. -/
def advance (seen : Seen) (e : ℕ × ℕ) (b : Bool) : Seen :=
  ⟨seen.edges ++ [key e], mark seen e b, seen.selected + b.toNat⟩

/- Insert the distinct endpoints of the rest of the marked list into a previous dictionary. -/
def collect (es : List (ℕ × ℕ)) (vertices : List ℕ) : List ℕ :=
  es.foldl (fun xs e => insertKey (insertKey xs e.1) e.2) vertices

/- Acceptance from a scan state, whose old edge keys are assumed to be distinct. -/
def Accept (n k m : ℕ) (seen : Seen) (es : List (ℕ × ℕ)) (w : List Bool) : Prop :=
  w.length = es.length ∧ (seen.edges ++ es.map key).Nodup ∧ (∀ e ∈ es, Valid n e) ∧
    k ≤ n ∧ m ≤ seen.selected + (markedEdges es w).length ∧
    (collect (markedEdges es w) seen.vertices).length ≤ k

/- Both streams must end together, after which three numeric comparisons suffice. -/
theorem accept_nil (n k m : ℕ) (seen : Seen) (w : List Bool) (hnd : seen.edges.Nodup) :
    Accept n k m seen [] w ↔ w = [] ∧ k ≤ n ∧ m ≤ seen.selected ∧ seen.vertices.length ≤ k := by
  simp [Accept, hnd, markedEdges, collect]

/- The verifier rejects a missing mark before reading an edge. -/
theorem reject_missing (n k m : ℕ) (seen : Seen) (e : ℕ × ℕ) (es : List (ℕ × ℕ)) :
    ¬ Accept n k m seen (e :: es) [] := by simp [Accept]

private theorem nodup_extend {α : Type} {xs ys : List α} {x : α} :
    (xs ++ x :: ys).Nodup ↔ x ∉ xs ∧ ((xs ++ [x]) ++ ys).Nodup := by
  rw [List.append_assoc, List.singleton_append]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  intro hx
  have hcross := (List.nodup_append.mp h).2.2
  exact hcross _ hx _ (by simp) rfl

/- The loop invariant splits into the immediate checks and the invariant after the step. -/
theorem accept_cons (n k m : ℕ) (seen : Seen) (e : ℕ × ℕ) (es : List (ℕ × ℕ))
    (b : Bool) (w : List Bool) :
    Accept n k m seen (e :: es) (b :: w) ↔
      Valid n e ∧ key e ∉ seen.edges ∧ Accept n k m (advance seen e b) es w := by
  unfold Accept
  rw [List.map_cons, nodup_extend]
  cases b <;>
    simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp,
      advance, mark, collect, markedEdges, List.zip_cons_cons, List.filterMap_cons,
      Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Bool.toNat_false, Bool.toNat_true, Nat.add_zero,
      List.foldl_cons, Nat.add_right_comm _ 1]
  all_goals tauto

/- Initial loop semantics coincide with the original executable marked specification. -/
theorem accept_initial_iff (n k m : ℕ) (es : List (ℕ × ℕ)) (w : List Bool) :
    Accept n k m ⟨[], [], 0⟩ es w ↔
      WellFormed (n, es, k, m) ∧ w.length = es.length ∧ k ≤ n ∧
        m ≤ (markedEdges es w).length ∧ (endpoints (markedEdges es w)).card ≤ k := by
  rw [wellFormed_iff_keys]
  have hv := vertexKeys_length (markedEdges es w)
  change (collect (markedEdges es w) []).length = _ at hv
  simp only [Accept, List.nil_append, Nat.zero_add, hv, Valid]
  tauto

/- All three header words and each physical endpoint fit in one bit-length bound. -/
def Fits (B : ℕ) (n k m : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  n.size ≤ B ∧ k.size ≤ B ∧ m.size ≤ B ∧ ∀ e ∈ es, e.1.size ≤ B ∧ e.2.size ≤ B

private theorem index_size {es : List (ℕ × ℕ)} {e : ℕ × ℕ} (h : e ∈ es) (side : Bool) :
    (if side then e.2 else e.1).size ≤
      (bitEncode (es.map (if side then Prod.snd else Prod.fst))).length := by
  induction es with
  | nil => simp at h
  | cons a es ih =>
    cases side <;> rcases List.mem_cons.mp h with h | h
    · subst e
      change a.1.size ≤ (delimit (bitEncode a.1) ++ bitEncode (es.map Prod.fst)).length
      simp only [List.length_append, length_delimit, BinaryNatEncoding.length_bitEncode]
      omega
    · change e.1.size ≤ (delimit (bitEncode a.1) ++ bitEncode (es.map Prod.fst)).length
      have hh := ih h
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      rw [List.length_append]
      omega
    · subst e
      change a.2.size ≤ (delimit (bitEncode a.2) ++ bitEncode (es.map Prod.snd)).length
      simp only [List.length_append, length_delimit, BinaryNatEncoding.length_bitEncode]
      omega
    · change e.2.size ≤ (delimit (bitEncode a.2) ++ bitEncode (es.map Prod.snd)).length
      have hh := ih h
      simp only [↓reduceIte] at hh
      rw [List.length_append]
      omega

/- Input decoding has a uniform bit bound, even for noncanonical Nat frames. -/
theorem decoded_fits {x : List Bool} {n k m : ℕ} {es : List (ℕ × ℕ)}
    (h : bitDecode x = some (n, es, k, m)) :
    Fits (2 * x.length + 1) n k m es ∧ es.length ≤ x.length := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have hn : decodeNat p = n := Option.some.inj hp
  have hpn := length_normalizeNat_le p
  rw [normalizeNat_eq_encode_decode, hn, BinaryNatEncoding.length_encodeNat] at hpn
  have hs := ListNatPairPair.output_length_le hr
  rw [BinaryNatEncoding.length_encodeNat, BinaryNatEncoding.length_encodeNat] at hs
  have hx' : x.length = 2 * p.length + 1 + r.length := by
    rw [hx, List.length_append, length_delimit]
  refine ⟨⟨by omega, by omega, by omega, ?_⟩, decoded_middle_list_length_le h⟩
  intro e he
  have h₁ := index_size he false
  have h₂ := index_size he true
  change e.1.size ≤ (bitEncode (es.map Prod.fst)).length at h₁
  change e.2.size ≤ (bitEncode (es.map Prod.snd)).length at h₂
  exact ⟨by omega, by omega⟩

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierSpec
