/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Ramsey3/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: P. Manrique, H. Xia, S. Szeider.
The theorem statement restates the bound R(3,10) ≥ 40 in the “Known values” table at
commit e2e19eef093a77882da57f348def029533ec2d5e for the repository's graph Ramsey number.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Clique
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# Exoo's lower bound for the Ramsey number `R(3, 10)`

We prove `forty_le_graphRamsey_three_ten` using a graph on 39 vertices with no triangle
and no independent set of size 10. The witness was found by a local search seeded with
the circulant graph on 35 vertices with jumps 1, 7, 11 and 16. The kernel checks
both forbidden configurations using a recursive search over bitmasks of vertices.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

open _root_.SimpleGraph
open MathlibExt.Combinatorics.RamseyErdosLowerBound (classicalRamsey_mono exists_classicalRamsey)

/-- Check whether the vertices below `b` in the mask `c` contain no `k`-clique.
For `w < v`, bit `w` of `rows v` records the edge to `v`. -/
private def checkNoClique (rows : ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | 0, _, _ + 1 => true
  | b + 1, c, k + 1 =>
    if c == 0 then true else
      let rest := c &&& (2 ^ b - 1)
      (!c.testBit b || checkNoClique rows b (rest &&& rows b) k) &&
        checkNoClique rows b rest (k + 1)

private lemma checkNoClique_sound (rows : ℕ → ℕ) (b c k : ℕ)
    (h : checkNoClique rows b c k = true) (s : Finset ℕ) (hcard : s.card = k)
    (hmem : ∀ v ∈ s, v < b ∧ c.testBit v = true)
    (hadj : ∀ v ∈ s, ∀ w ∈ s, w < v → (rows v).testBit w = true) : False := by
  induction b generalizing c k s with
  | zero =>
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun v hv =>
      (Nat.not_lt_zero v) (hmem v hv).1
    simp [hs] at hcard
    simp [← hcard, checkNoClique] at h
  | succ b ih =>
    cases k with
    | zero => simp [checkNoClique] at h
    | succ k =>
      have hne : c ≠ 0 := by
        have hpos : 0 < s.card := hcard.symm ▸ Nat.succ_pos k
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        intro hc
        simpa [hc] using (hmem v hv).2
      simp only [checkNoClique, beq_iff_eq, hne, ite_false, Bool.and_eq_true] at h
      by_cases hb : b ∈ s
      · have hinclude := h.1
        simp only [(hmem b hb).2, Bool.not_true, Bool.false_or] at hinclude
        refine ih _ _ hinclude (s.erase b) ?_ ?_ ?_
        · rw [Finset.card_erase_of_mem hb, hcard, Nat.add_sub_cancel]
        · intro w hw
          obtain ⟨hwb, hws⟩ := Finset.mem_erase.mp hw
          have hlt : w < b := lt_of_le_of_ne (Nat.lt_succ_iff.mp (hmem w hws).1) hwb
          exact ⟨hlt, by simp [Nat.testBit_and, hlt, (hmem w hws).2, hadj b hb w hws hlt]⟩
        · intro v hv w hw hwv
          exact hadj v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw) hwv
      · refine ih _ _ h.2 s hcard ?_ hadj
        intro w hw
        have hlt : w < b := by
          have := (hmem w hw).1
          have hne : w ≠ b := fun he => hb (he ▸ hw)
          omega
        exact ⟨hlt, by simp [hlt, (hmem w hw).2]⟩

private lemma cliqueFree_of_checkNoClique {n k : ℕ} {G : SimpleGraph (Fin n)} (rows : ℕ → ℕ)
    (hrows : ∀ i j : Fin n, (j : ℕ) < i → G.Adj i j → (rows i).testBit j = true)
    (h : checkNoClique rows n (2 ^ n - 1) k = true) : G.CliqueFree k := by
  intro s hs
  refine checkNoClique_sound rows _ _ _ h (s.map Fin.valEmbedding) ?_ ?_ ?_
  · rw [Finset.card_map, hs.card_eq]
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨i.isLt, by simp [i.isLt]⟩
  · intro v hv w hw hwv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hw
    exact hrows i j hwv (hs.isClique hi hj (ne_of_gt hwv ∘ congrArg Fin.val))

/-- The witness's adjacency matrix. Row `i` has bit `j` set exactly when vertices
`i` and `j` are adjacent. -/
private def witnessRows : List ℕ := [
  0x0411090882, 0x1022121105, 0x084424220a, 0x2088484414, 0x4110908828,
  0x1221211050, 0x0c024a20a0, 0x4084844141, 0x0909088282, 0x4212110504,
  0x1424220a08, 0x0848441411, 0x2090882822, 0x1121105044, 0x0a4220a088,
  0x04a4414110, 0x2108828221, 0x4211050442, 0x14220a0884, 0x0044141149,
  0x2088282212, 0x4110504424, 0x1200a08848, 0x0c41411090, 0x2082822121,
  0x0105044242, 0x020a088484, 0x0414110908, 0x1028221211, 0x205004a422,
  0x40a0884804, 0x0941109088, 0x0282212110, 0x2504424220, 0x4208848441,
  0x3080804944, 0x4810442422, 0x4a21111008, 0x3440220290]

private def witnessRow (i : ℕ) : ℕ := witnessRows.getD i 0

/-- The complement's adjacency mask, with the diagonal bit unused by the clique check. -/
private def witnessComplRow (i : ℕ) : ℕ := (2 ^ 39 - 1) ^^^ witnessRow i

private theorem witnessRow_symm :
    ∀ i j : Fin 39, (witnessRow i).testBit j = (witnessRow j).testBit i := by
  decide +kernel

private theorem witnessRow_irrefl : ∀ i : Fin 39, (witnessRow i).testBit i = false := by
  decide +kernel

/-- A triangle-free graph on 39 vertices with no independent set of size 10. -/
private def witness : SimpleGraph (Fin 39) where
  Adj i j := (witnessRow i).testBit j = true
  symm := ⟨fun i j h => (witnessRow_symm i j).symm.trans h⟩
  loopless := ⟨fun i h => by simp [witnessRow_irrefl i] at h⟩

private lemma witness_cliqueFree : witness.CliqueFree 3 :=
  cliqueFree_of_checkNoClique witnessRow (fun _ _ _ h => h) (by decide +kernel)

private lemma witness_compl_cliqueFree : witnessᶜ.CliqueFree 10 :=
  cliqueFree_of_checkNoClique witnessComplRow (fun i j _ h => by
    rw [compl_adj] at h
    have hj : (witnessRow i).testBit j = false := by simpa [witness] using h.2
    rw [witnessComplRow, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hj]
    simp [j.isLt]) (by decide +kernel)

/-- **Exoo's lower bound for $R(3, 10)$.** The classical Ramsey number $R(3, 10)$ is at
least $40$.

Source: G. Exoo, *On two classical Ramsey numbers of the form R(3,n)*, SIAM
J. Discrete Math. 2 (1989), 488–490; Radziszowski, DS1; listed in
SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem forty_le_graphRamsey_three_ten : 40 ≤ graphRamsey 3 10 := by
  rw [graphRamsey_eq_sInf]
  refine le_csInf (exists_classicalRamsey 3 10) fun n hn => ?_
  by_contra! h
  rcases classicalRamsey_mono (by omega : n ≤ 39) hn witness with h₃ | h₁₀
  · exact h₃.not_cliqueFree witness_cliqueFree
  · exact h₁₀.not_cliqueFree witness_compl_cliqueFree

end MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
