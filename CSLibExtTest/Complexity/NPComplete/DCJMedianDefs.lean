/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DCJMedianDefs

namespace MetaMathlibExt.Complexity.NPComplete.DCJMedian

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : DCJMedianInstance) :
    dcjMedianDec (bitEncode i) = true ↔ WellFormed i ∧ DCJMedianFeasible i := by
  simp [dcjMedianDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : dcjMedianDec [true] = false := by
  have h : bitDecode (α := DCJMedianInstance) [true] = none := rfl
  simp [dcjMedianDec, h]

/-- One gene; two genomes join its extremities and the third leaves both as telomeres. -/
private abbrev oneGene (k : ℕ) : DCJMedianInstance := ([true], [(0, 1)], [(0, 1)], [], k)

private theorem isGenome_genome (k : ℕ) (adj : List (ℕ × ℕ)) (h : adj ⊆ [(0, 1)]) :
    IsGenome (genome (oneGene k) adj) := by
  intro v x y hx hy
  simp only [genome, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj] at hx hy
  have hx' := hx.2.imp (fun h' => h h') (fun h' => h h')
  have hy' := hy.2.imp (fun h' => h h') (fun h' => h h')
  have hv : (v : ℕ) < 2 := v.isLt
  have hxl : (x : ℕ) < 2 := x.isLt
  have hyl : (y : ℕ) < 2 := y.isLt
  simp only [List.mem_singleton, Prod.mk.injEq] at hx' hy'
  apply Fin.ext
  have := Fin.val_ne_of_ne hx.1; have := Fin.val_ne_of_ne hy.1
  omega

private theorem wellFormed_oneGene (k : ℕ) : WellFormed (oneGene k) :=
  ⟨by simp, ⟨by simp, by simp [numGenes], isGenome_genome k _ (by simp)⟩,
    ⟨by simp, by simp [numGenes], isGenome_genome k _ (by simp)⟩,
    ⟨by simp, by simp, isGenome_genome k _ (by simp)⟩⟩

/-- Joining the two telomeres of the third genome is one DCJ. -/
private theorem join_step (k : ℕ) :
    IsDCJ (genome (oneGene k) []) (genome (oneGene k) [(0, 1)]) := by
  refine Or.inr (Or.inl ⟨⟨0, Nat.zero_lt_two⟩, ⟨1, Nat.one_lt_two⟩, by simp [Fin.ext_iff],
    ?_, ?_, ?_⟩)
  · intro x h; simp [genome, Cslib.Complexity.Karp.edgeGraph] at h
  · intro x h; simp [genome, Cslib.Complexity.Karp.edgeGraph] at h
  · ext a b
    have ha : (a : ℕ) < 2 := a.isLt
    have hb : (b : ℕ) < 2 := b.isLt
    simp [genome, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.edge_adj, Fin.ext_iff]
    omega

/-- With budget one, the median joining the gene's extremities is at distance `0`, `0` and
`1` from the three genomes. -/
example : dcjMedianDec (bitEncode (oneGene 1)) = true :=
  (accepts_encoding _).2 ⟨wellFormed_oneGene 1, genome (oneGene 1) [(0, 1)],
    isGenome_genome 1 _ (by simp), 0, 0, 1, le_refl _,
    ⟨[_], le_refl _, rfl, rfl, List.isChain_singleton _⟩,
    ⟨[_], le_refl _, rfl, rfl, List.isChain_singleton _⟩,
    ⟨[_, _], le_refl _, rfl, rfl, List.isChain_pair.2 (join_step 1)⟩⟩

/-- Distance at most `0` forces the median to equal each input genome. -/
private theorem eq_of_within_zero {V : Type} {G H : SimpleGraph V} (h : DCJWithin G H 0) :
    G = H := by
  obtain ⟨l, hl, hh, ht, -⟩ := h
  match l, hl with
  | [x], _ => simp at hh ht; exact hh.symm.trans ht

/-- With budget zero, the median would have to equal the first and the third genome, which
differ on the adjacency of the gene's extremities. -/
example : dcjMedianDec (bitEncode (oneGene 0)) = false := by
  cases h : dcjMedianDec (bitEncode (oneGene 0)) with
  | false => rfl
  | true =>
    obtain ⟨-, M, -, k₁, k₂, k₃, hk, h₁, -, h₃⟩ := (accepts_encoding _).1 h
    obtain rfl : k₁ = 0 := by simp at hk; omega
    obtain rfl : k₃ = 0 := by simp at hk; omega
    have e := (eq_of_within_zero h₁).trans (eq_of_within_zero h₃).symm
    have := congrArg (fun G => SimpleGraph.Adj G ⟨0, by decide⟩ ⟨1, by decide⟩) e
    simp [genome, Cslib.Complexity.Karp.edgeGraph, Fin.ext_iff] at this

end MetaMathlibExt.Complexity.NPComplete.DCJMedian
