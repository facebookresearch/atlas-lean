/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuples

/-! # Multiplicativity for graph coprimality indicators -/

namespace MetaMathlibExt

/-- **Multiplicativity of the coprimality indicator.** Let $G$ be a graph on the vertices
$0, \dots, k-1$ given by an arbitrary set $E$ of ordered pairs of vertices, with coprimality
indicator $\delta_G$. If $m, n \in \mathbb{N}^k$ satisfy
$\gcd(m_0 m_1 \cdots m_{k-1}, n_0 n_1 \cdots n_{k-1}) = 1$, then
$\delta_G(m_0 n_0, \dots, m_{k-1} n_{k-1}) = \delta_G(m)\, \delta_G(n)$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 4 (`jis-2024-24.8.5-lem-4`). -/
public theorem coprimalityIndicator_mul {k : ℕ} (E : Finset (Fin k × Fin k))
    (m n : Fin k → ℕ)
    (hmn : Nat.Coprime (∏ i, m i) (∏ i, n i)) :
    coprimalityIndicator E (fun i => m i * n i) =
      coprimalityIndicator E m * coprimalityIndicator E n := by
  -- Each coordinate divides its tuple's product, so the cross terms are coprime.
  have cross (i j : Fin k) : Nat.Coprime (m i) (n j) :=
    Nat.Coprime.of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
      (Finset.dvd_prod_of_mem n (Finset.mem_univ j)) hmn
  have edge (i j : Fin k) : Nat.Coprime (m i * n i) (m j * n j) ↔
      Nat.Coprime (m i) (m j) ∧ Nat.Coprime (n i) (n j) := by
    simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
    exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h =>
      ⟨⟨h.1, (cross j i).symm⟩, cross i j, h.2⟩⟩
  have all_edges : (∀ e ∈ E, Nat.Coprime (m e.1 * n e.1) (m e.2 * n e.2)) ↔
      (∀ e ∈ E, Nat.Coprime (m e.1) (m e.2)) ∧
        (∀ e ∈ E, Nat.Coprime (n e.1) (n e.2)) := by
    constructor
    · intro h
      exact ⟨fun e he => ((edge e.1 e.2).mp (h e he)).1,
        fun e he => ((edge e.1 e.2).mp (h e he)).2⟩
    · intro h e he
      exact (edge e.1 e.2).mpr ⟨h.1 e he, h.2 e he⟩
  unfold coprimalityIndicator
  by_cases hm : ∀ e ∈ E, Nat.Coprime (m e.1) (m e.2)
  · by_cases hn : ∀ e ∈ E, Nat.Coprime (n e.1) (n e.2)
    · simp only [ite_eq_left (all_edges.mpr ⟨hm, hn⟩), ite_eq_left hm, ite_eq_left hn, Nat.one_mul]
    · simp only [ite_eq_right (fun h => hn (all_edges.mp h).2), ite_eq_left hm, ite_eq_right hn,
        Nat.mul_zero]
  · simp only [ite_eq_right (fun h => hm (all_edges.mp h).1), ite_eq_right hm, Nat.zero_mul]

end MetaMathlibExt
