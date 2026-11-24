/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Ramsey/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The theorem statement restates the bound `R(5,5) ≥ 43` from the “Known values” table at
commit e2e19eef093a77882da57f348def029533ec2d5e for the repository's `SimpleGraph.graphRamsey`.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Clique
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# Exoo's lower bound for the Ramsey number `R(5, 5)`

We prove `forty_three_le_graphRamsey_five_five`: the classical Ramsey number `R(5, 5)` is at
least `43`. Exoo found the first graph on `42` vertices with no clique and no independent set of
size `5` in 1989. Such a graph shows that the Ramsey property fails on `42` vertices. The property
is monotone in the number of vertices, and some number of vertices has it (Ramsey's theorem), so
the least such number is at least `43`.

## The witness

We use the colouring of the edges of the complete graph on `42` vertices given in Supplementary
Table S15 of B. Molnár, M. Varga, Z. Toroczkai and M. Ercsey-Ravasz, *A high-performance analog
Max-SAT solver and its application to Ramsey numbers*, arXiv:1801.06620v2 (2018). Each row of its
adjacency matrix is written below as a binary literal with the same `42` digits, so the entry in
row `i` and column `j` is bit `41 - j` of the `i`-th literal. Our vertex `i` is the vertex `41 - i`
of the table: vertices `i` and `j` are adjacent when bit `j` of the literal in position `41 - i`
is set. This relabelling of the vertices does not change the graph up to isomorphism.

## The certificate check

`noCliqueCheck r k b c` is a Boolean test, by bitmask arithmetic, for the absence of `k` pairwise
adjacent vertices below `b` in the bitmask `c`, where a vertex `w < v` is adjacent to `v` when
bit `w` of `r v` is set. It branches on the largest vertex `v` of a putative clique and recurses
on the neighbours of `v` below `v`. `noCliqueCheck_sound` shows that a `true` answer excludes
such cliques. The kernel evaluates the test for the witness and for its complement
(`decide +kernel`; no `native_decide`).
-/

namespace MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

open _root_.SimpleGraph
open MathlibExt.Combinatorics.RamseyErdosLowerBound (exists_classicalRamsey classicalRamsey_mono)

/-- A Boolean test whose `true` answer certifies that no `k` vertices below `b` in the bitmask
`c` are pairwise adjacent, where `w < v` is adjacent to `v` when bit `w` of `r v` is set
(`noCliqueCheck_sound`). It branches on the largest vertex `v` of a clique: the other vertices
lie in `c`, below `v`, and among the neighbours of `v`. -/
private def noCliqueCheck (r : ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | 1, _, c => c == 0
  | k + 2, b, c => (List.range b).all fun v =>
      !c.testBit v || noCliqueCheck r (k + 1) v (c &&& r v &&& (2 ^ v - 1))

/-- Soundness of `noCliqueCheck`: if it answers `true`, then no set of `k` vertices below `b`
in the bitmask `c` is a clique for the rows `r`. -/
private theorem noCliqueCheck_sound (r : ℕ → ℕ) :
    ∀ (k b c : ℕ), noCliqueCheck r k b c = true → ∀ S : Finset ℕ, S.card = k →
      (∀ v ∈ S, v < b ∧ c.testBit v = true) →
      (∀ v ∈ S, ∀ w ∈ S, w < v → (r v).testBit w = true) → False
  | 0, _, _, h, _, _, _, _ => by simp [noCliqueCheck] at h
  | 1, _, c, h, S, hS, hmem, _ => by
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hS
    have hc : c = 0 := by simpa [noCliqueCheck] using h
    simpa [hc] using (hmem v (Finset.mem_singleton_self v)).2
  | k + 2, b, c, h, S, hS, hmem, hadj => by
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hvS : S.max' hne ∈ S := S.max'_mem hne
    obtain ⟨hvb, hcv⟩ := hmem _ hvS
    have hall := List.all_eq_true.1 h _ (List.mem_range.2 hvb)
    simp only [hcv, Bool.not_true, Bool.false_or] at hall
    refine noCliqueCheck_sound r (k + 1) _ _ hall (S.erase (S.max' hne)) ?_ ?_ ?_
    · rw [Finset.card_erase_of_mem hvS, hS]
      rfl
    · intro w hw
      obtain ⟨hwv, hwS⟩ := Finset.mem_erase.1 hw
      have hlt : w < S.max' hne := lt_of_le_of_ne (S.le_max' w hwS) hwv
      refine ⟨hlt, ?_⟩
      simp [Nat.testBit_and, (hmem w hwS).2, hadj _ hvS w hwS hlt, hlt]
    · intro v hv w hw hwv
      exact hadj v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw) hwv

/-- A graph on `Fin n` is `k`-clique-free when `noCliqueCheck` accepts rows `r` that contain
its edges (each edge `{i, j}` with `j < i` is bit `j` of `r i`). -/
private theorem cliqueFree_of_noCliqueCheck {n k : ℕ} {G : SimpleGraph (Fin n)} (r : ℕ → ℕ)
    (hG : ∀ i j : Fin n, (j : ℕ) < i → G.Adj i j → (r i).testBit j = true)
    (h : noCliqueCheck r k n (2 ^ n - 1) = true) : G.CliqueFree k := by
  intro s hs
  refine noCliqueCheck_sound r k n (2 ^ n - 1) h (s.map Fin.valEmbedding) ?_ ?_ ?_
  · rw [Finset.card_map, hs.card_eq]
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hv
    exact ⟨i.isLt, by simp [i.isLt]⟩
  · intro v hv w hw hwv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hw
    exact hG i j hwv (hs.isClique hi hj (fun hij => (lt_irrefl _ (hij ▸ hwv))))

/-- The rows of the adjacency matrix of Supplementary Table S15 of Molnár, Varga, Toroczkai and
Ercsey-Ravasz (arXiv:1801.06620v2), in order, each written as a binary literal with the digits of
the row: the entry in row `i` and column `j` is bit `41 - j` of the `i`-th literal. -/
private def tableRows : List ℕ := [
    0b001110000000111011011011101101110000000110,
    0b000111000000011101101111110110111000000011,
    0b100011100000001110110111011011011100000001,
    0b110001110000000111011011001101101110001000,
    0b111000111000000011101101100110110111000000,
    0b011100011100000001110110111111011011100000,
    0b001110001110000000111011011111101101110000,
    0b000111000111000000011101101100110110111000,
    0b000011100011100000001110110110011011011100,
    0b000001110001110000000111011011010101101110,
    0b000000111000111000000011101101101110110111,
    0b000000011100011100000001110110110011011011,
    0b100000001110001110000000111011011001101101,
    0b110000000111000111000000011101101101110110,
    0b111000000011100011100000001110110111111011,
    0b011100000001110001110000001111011011101101,
    0b101110000000111000111000000011101101100110,
    0b110111000000011100011100000001110110110011,
    0b011011100000001110001110000000111011011111,
    0b101101110000000111000111000000011101101111,
    0b110110111000000011100011100000001110110110,
    0b011011011100000001110001110000000111011011,
    0b111101101110000000111000111000000011101101,
    0b111110110111000000011100011100000001110110,
    0b110011011011100000001110001110000000111011,
    0b011001101101110000000111000111000000011101,
    0b101101110110111100000011100011100000001110,
    0b110111111011011100000001110001110000000111,
    0b011011101101101110000000111000111000000011,
    0b101101100110110111000000011100011100000001,
    0b110110110011011011100000001110001110000000,
    0b111011011101101101110000000111000111000000,
    0b011101101010110110111000000011100011100000,
    0b001110110110011011011100000001110001110000,
    0b000111011011001101101110000000111000111000,
    0b000011101101111110110111000000011100011100,
    0b000001110110111111011011100000001110001110,
    0b000000111011011001101101110000000111000111,
    0b000100011101101100110110111000000011100011,
    0b100000001110110110111011011100000001110001,
    0b110000000111011011111101101110000000111000,
    0b011000000011101101110110110111000000011100]

/-- The neighbourhood bitmask of vertex `i` of the witness: the row `41 - i` of the table. -/
private def witnessRow (i : ℕ) : ℕ := tableRows.getD (41 - i) 0

/-- The neighbourhood bitmask of vertex `i` in the complement of the witness, apart from the bit
of `i` itself, which the check never reads. -/
private def witnessComplRow (i : ℕ) : ℕ := (2 ^ 42 - 1) ^^^ witnessRow i

private theorem witnessRow_symm :
    ∀ i j : Fin 42, (witnessRow i).testBit j = (witnessRow j).testBit i := by
  decide +kernel

private theorem witnessRow_irrefl : ∀ i : Fin 42, (witnessRow i).testBit i = false := by
  decide +kernel

/-- The witness: a graph on `42` vertices in which vertices `i` and `j` are adjacent when bit `j`
of `witnessRow i` is set; it is the graph of Table S15 with vertex `i` relabelled `41 - i`. -/
private def witness : SimpleGraph (Fin 42) where
  Adj i j := (witnessRow i).testBit j = true
  symm := ⟨fun i j h => (witnessRow_symm i j).symm.trans h⟩
  loopless := ⟨fun i h => by simp [witnessRow_irrefl i] at h⟩

/-- The witness contains no `K_5`; the kernel runs the clique check. -/
private theorem witness_cliqueFree : witness.CliqueFree 5 :=
  cliqueFree_of_noCliqueCheck witnessRow (fun _ _ _ h => h) (by decide +kernel)

/-- The complement of the witness contains no `K_5`; the kernel runs the clique check. -/
private theorem witness_compl_cliqueFree : witnessᶜ.CliqueFree 5 :=
  cliqueFree_of_noCliqueCheck witnessComplRow (fun i j _ h => by
    rw [compl_adj] at h
    have hj : (witnessRow i).testBit j = false := by simpa [witness] using h.2
    rw [witnessComplRow, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hj]
    simp [j.isLt]) (by decide +kernel)

/-- **Exoo's lower bound for $R(5, 5)$.** The classical Ramsey number $R(5, 5)$ is at
least $43$.

Thus some simple graph on $42$ vertices contains no $K_5$ and no independent set of size $5$.

Source: G. Exoo, *A lower bound for R(5,5)*, J. Graph Theory 13 (1989),
97–98; Radziszowski, DS1; listed in SqueezeBench
`SqueezeBench/Problems/Ramsey/README.md`. -/
public theorem forty_three_le_graphRamsey_five_five : 43 ≤ graphRamsey 5 5 := by
  rw [graphRamsey_eq_sInf]
  refine le_csInf (exists_classicalRamsey 5 5) fun N hN => ?_
  by_contra hlt
  rcases classicalRamsey_mono (by omega : N ≤ 42) hN witness with h | h
  · exact (not_cliqueFree_iff_top_isContained 5).2 h witness_cliqueFree
  · exact (not_cliqueFree_iff_top_isContained 5).2 h witness_compl_cliqueFree

end MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
