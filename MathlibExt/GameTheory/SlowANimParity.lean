/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.GameTheory.SlowANim

/-!
# Parity in Slow A-Nim

When the allowed move sizes are one and an odd number, the P-positions are exactly
the positions with an even total number of tokens.
-/

namespace MetaMathlibExt

namespace slowANim_one_odd_isP_iff

private theorem even_sum_iff {n k : ℕ} (hk : Odd k) {p q : Fin n → ℕ}
    (hq : q ∈ slowANimMoves {1, k} p) : Even (∑ i, p i) ↔ ¬ Even (∑ i, q i) := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at hq
  obtain ⟨S, ⟨-, -, hcard, hpos⟩, rfl⟩ := hq
  have hsum : (∑ i, slowANimAfter p S i) + S.card = ∑ i, p i := by
    calc
      _ = ∑ i, (slowANimAfter p S i + if i ∈ S then 1 else 0) := by
        simp [Finset.sum_add_distrib, ← Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [slowANimAfter, hi, Nat.sub_add_cancel (hpos i hi)]
        · simp [slowANimAfter, hi]
  have hodd : Odd S.card := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
    rcases hcard with h | h
    · simp [h]
    · exact h ▸ hk
  rw [← hsum, Nat.even_add]
  simp [Nat.not_even_iff_odd.mpr hodd]

end slowANim_one_odd_isP_iff

set_option linter.unusedVariables false in
/-- **P-positions of Slow A-Nim with A = {1, k}, k odd.** Let $k$ be odd with $1 \le k \le n$
and let $A = \{1, k\}$. A position $p = (p_1, \dots, p_n)$ of Slow$A$-Nim on $n$ stacks is a
P-position if and only if its total number of tokens $p_1 + \dots + p_n$ is even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem slowANim_one_odd_isP_iff (n k : ℕ) (hA : ({1, k} : Finset ℕ) ⊆ Finset.Icc 1 n)
    (hk : Odd k) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, k}) p ↔ Even (∑ i, p i) := by
  let G := slowANimGame n {1, k}
  change SpragueGrundy.IsP G p ↔ _
  induction p using (SpragueGrundy.wfRel G).induction with
  | h p ih =>
    rw [SpragueGrundy.isP_iff]
    constructor
    · intro hp
      by_cases hex : ∃ i, 1 ≤ p i
      · obtain ⟨i, hi⟩ := hex
        let q := slowANimAfter p {i}
        have hq : q ∈ G.moves p := by
          change q ∈ slowANimMoves {1, k} p
          simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter]
          refine ⟨{i}, ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          simpa using hi
        exact (slowANim_one_odd_isP_iff.even_sum_iff hk hq).2
          (fun h => hp q hq ((ih q hq).2 h))
      · have hzero (i : Fin n) : p i = 0 := by
          have hi := not_exists.mp hex i
          omega
        simp [hzero]
    · intro hp q hq hPq
      exact (slowANim_one_odd_isP_iff.even_sum_iff hk hq).1 hp ((ih q hq).1 hPq)

end MetaMathlibExt
