/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShellabilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.Shellability

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

private theorem accepts_encoding (d : ℕ) (i : ShellabilityInstance) :
    shellabilityDec d (bitEncode i) = true ↔ WellFormed d i ∧ ShellabilityFeasible d i := by
  simp [shellabilityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every dimension. -/
example (d : ℕ) : shellabilityDec d [true] = false := by
  have h : bitDecode (α := ShellabilityInstance) [true] = none := rfl
  simp [shellabilityDec, h]

/-- In dimension `1`, the path with edges `{0, 1}, {1, 2}` is shellable: the second edge meets
the first in the vertex `1`, a pure `0`-dimensional complex. -/
example : shellabilityDec 1 (bitEncode ([[0, 1], [1, 2]] : ShellabilityInstance)) = true := by
  refine (accepts_encoding _ _).2 ⟨⟨by simp, by decide⟩, [{0, 1}, {1, 2}], by decide, ?_, ?_, ?_⟩
  · unfold IsFacet complex; decide
  · unfold IsFacet complex; decide
  · unfold IsPureOfCard IsFacet topCard intersectionComplex; decide

/-- The facets of the complex of two disjoint edges are those two edges. -/
private theorem facet_disjoint (F : Finset ℕ) (hF : IsFacet (complex [[0, 1], [2, 3]]) F) :
    F = {0, 1} ∨ F = {2, 3} := by
  have key : ∀ F ∈ complex [[0, 1], [2, 3]], (∀ G ∈ complex [[0, 1], [2, 3]], F ⊆ G → G = F) →
      F = {0, 1} ∨ F = {2, 3} := by
    unfold complex; decide
  exact key F hF.1 hF.2

/-- In dimension `1`, two disjoint edges are not shellable: whichever edge comes second meets the
first only in the empty face, which is not pure `0`-dimensional. -/
example : shellabilityDec 1 (bitEncode ([[0, 1], [2, 3]] : ShellabilityInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, l, hnd, hfac, hall, hpure⟩ := (accepts_encoding _ _).1 h
  have h01 : ({0, 1} : Finset ℕ) ∈ l := hall _ (by unfold complex; decide)
    (by unfold IsFacet complex; decide)
  have h23 : ({2, 3} : Finset ℕ) ∈ l := hall _ (by unfold complex; decide)
    (by unfold IsFacet complex; decide)
  have hlen : 1 < l.length := by
    match l, h01, h23 with
    | [], h, _ => simp at h
    | [a], h, h' => simp at h h'; rw [← h] at h'; exact absurd h' (by decide)
    | _ :: _ :: _, _, _ => simp
  have hp := hpure ⟨1, hlen⟩ (by simp)
  have hne : l[0] ≠ l[1] := fun e => by
    have := (List.Nodup.getElem_inj_iff hnd).1 e
    omega
  rcases facet_disjoint _ (hfac _ (List.getElem_mem (by omega : 0 < l.length))) with h0 | h0 <;>
    rcases facet_disjoint _ (hfac _ (List.getElem_mem hlen)) with h1 | h1
  · exact hne (h0.trans h1.symm)
  · have hl : l.take 1 = [l[0]] := by
      match l, hlen with
      | _ :: _ :: _, _ => rfl
    simp only [Fin.getElem_fin, hl, h0, h1] at hp
    revert hp
    unfold IsPureOfCard IsFacet topCard intersectionComplex
    decide
  · have hl : l.take 1 = [l[0]] := by
      match l, hlen with
      | _ :: _ :: _, _ => rfl
    simp only [Fin.getElem_fin, hl, h0, h1] at hp
    revert hp
    unfold IsPureOfCard IsFacet topCard intersectionComplex
    decide
  · exact hne (h0.trans h1.symm)

/-- In dimension `0`, two isolated vertices are shellable: the second meets the first in the
empty face, which is pure of dimension `-1`. -/
example : shellabilityDec 0 (bitEncode ([[0], [1]] : ShellabilityInstance)) = true := by
  refine (accepts_encoding _ _).2 ⟨⟨by simp, by decide⟩, [{0}, {1}], by decide, ?_, ?_, ?_⟩
  · unfold IsFacet complex; decide
  · unfold IsFacet complex; decide
  · unfold IsPureOfCard IsFacet topCard intersectionComplex; decide

/-- The same two isolated vertices are malformed in dimension `1`, whose facets are edges. -/
example : shellabilityDec 1 (bitEncode ([[0], [1]] : ShellabilityInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _ _).1 h).1.2 [0] (by simp)).2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.Shellability
