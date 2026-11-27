/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander
public import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
public import Mathlib.Combinatorics.SimpleGraph.Clique

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spectral expanders and the graph Laplacian

For a `d`-regular graph the Laplacian is `L = d I - A`, so a spectral expander with parameter `λ`
has Laplacian Rayleigh quotient at least `d (1 - λ)` on the vectors orthogonal to the constants.
This bridges spectral expansion to the Laplacian results of D. A. Spielman's *Spectral and
Algebraic Graph Theory* already in the library: with the easy direction of Cheeger's inequality
(`EndpointMapMultigraph.mul_card_mul_card_compl_le_of_forall`) it gives edge expansion, and the
same edge bound follows from the expander mixing lemma
(`mul_card_mul_card_compl_le_card_interedges`). The mixing lemma also bounds independent sets
(`one_add_mul_card_le_of_isIndepSet`).
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.SpectralExpander

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Laplacian Rayleigh quotient of a spectral expander.** If `G` is a `d`-regular spectral
expander with parameter `λ`, then `xᵀ L x ≥ d (1 - λ) xᵀ x` for every `x` orthogonal to the
constant vector, where `L = D - A` is Mathlib's Laplacian `SimpleGraph.lapMatrix`. Equivalently
the second-smallest Laplacian eigenvalue is at least `d (1 - λ)` (the eigenvalue form is not
formalized here). The proof: `xᵀ L x = d xᵀ x - xᵀ A x` and `xᵀ A x ≤ ‖x‖ ‖A x‖ ≤ d λ ‖x‖²`. -/
theorem mul_dotProduct_le_lapMatrix {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {lam : ℝ}
    (h : IsSpectralExpander G d lam) (x : V → ℝ) (hx : x ⬝ᵥ 1 = 0) :
    d * (1 - lam) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) := by
  obtain ⟨hreg, hlam, hb⟩ := h
  have hsum : ∑ i, x i = 0 := by rwa [dotProduct_one] at hx
  have hL : G.lapMatrix ℝ *ᵥ x = (d : ℝ) • x - G.adjMatrix ℝ *ᵥ x := by
    funext v
    simp [SimpleGraph.lapMatrix, sub_mulVec, SimpleGraph.degMatrix_mulVec_apply, hreg v]
  rw [hL, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hnn : 0 ≤ x ⬝ᵥ x := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hAA := hb x hsum
  have hcs : (x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) ^ 2 ≤
      (x ⬝ᵥ x) * ((G.adjMatrix ℝ *ᵥ x) ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) := by
    simpa [dotProduct, sq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (G.adjMatrix ℝ *ᵥ x)
  have hsq : (x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) ^ 2 ≤ ((d : ℝ) * lam * (x ⬝ᵥ x)) ^ 2 := by
    calc _ ≤ (x ⬝ᵥ x) * ((G.adjMatrix ℝ *ᵥ x) ⬝ᵥ (G.adjMatrix ℝ *ᵥ x)) := hcs
      _ ≤ (x ⬝ᵥ x) * (((d : ℝ) * lam) ^ 2 * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left hAA hnn
      _ = _ := by ring
  have habs := abs_le_of_sq_le_sq' hsq (by positivity)
  nlinarith [habs.2]

/-- **Spectral expanders have edge expansion, through Cheeger's inequality.** For a `d`-regular
spectral expander with parameter `λ` on `N` vertices and every vertex set `S`,
`d (1 - λ) |S| |V \ S| ≤ N · w(∂S)`, where `w(∂S)` is the cut weight of `S` in the multigraph of
darts of `G` with weights `1/2`, that is the number of edges of `G` leaving `S`. This applies
the easy direction of Cheeger's inequality (D. A. Spielman, *Spectral and Algebraic Graph
Theory*, draft of 2 April 2025, Theorem 20.1.1, as
`EndpointMapMultigraph.mul_card_mul_card_compl_le_of_forall`) with
`mul_dotProduct_le_lapMatrix`. -/
theorem mul_card_mul_card_compl_le_cut {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {lam : ℝ} (h : IsSpectralExpander G d lam) (S : Finset V) :
    d * (1 - lam) * S.card * (Finset.univ \ S).card ≤
      (Fintype.card V : ℝ) * ∑ _e ∈ EndpointMapMultigraph.cut (fun e : G.Dart => e.fst)
        (fun e => e.snd) S, (1 / 2 : ℝ) := by
  refine EndpointMapMultigraph.mul_card_mul_card_compl_le_of_forall _ _ (fun _ => (1 / 2 : ℝ))
    (fun x hx => ?_) S
  rw [EndpointMapMultigraph.laplacian_dart_eq_lapMatrix]
  exact mul_dotProduct_le_lapMatrix h x hx

/-- **Spectral expanders have edge expansion, from the mixing lemma.** For a `d`-regular spectral
expander with parameter `λ` on `N` vertices and every vertex set `S`, the number `e(S, V \ S)` of
edges leaving `S` satisfies `d (1 - λ) |S| |V \ S| ≤ N e(S, V \ S)`. This is the expander mixing
lemma with `T = V \ S` (S. Vadhan, *Pseudorandomness* (2012), remark after Lemma 4.15: Part 1 of
Theorem 4.14 follows by setting `T = Sᶜ`). -/
theorem mul_card_mul_card_compl_le_card_interedges {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} {lam : ℝ} (h : IsSpectralExpander G d lam) (S : Finset V) :
    d * (1 - lam) * S.card * (Finset.univ \ S).card ≤
      (Fintype.card V : ℝ) * (G.interedges S (Finset.univ \ S)).card := by
  obtain ⟨hreg, hlam, hb⟩ := h
  set T := Finset.univ \ S
  set N : ℝ := (Fintype.card V : ℝ) with hN
  by_cases hN0 : N = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (by rw [hN] at hN0; exact_mod_cast hN0)
    simp [Finset.eq_empty_of_isEmpty S]
  have hNpos : 0 < N := lt_of_le_of_ne (by positivity) (Ne.symm hN0)
  have hrow : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
    funext v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simpa using this
  have hm := abs_indicator_dotProduct_mulVec_sub_le (G.transpose_adjMatrix (α := ℝ))
    (by positivity : (0 : ℝ) ≤ d * lam) hrow hb S T
  rw [← card_interedges_eq_indicator_dotProduct] at hm
  have hT : (T.card : ℝ) = N - S.card := by
    have := Finset.card_sdiff_add_card_inter Finset.univ S
    rw [Finset.univ_inter, Finset.card_univ] at this
    simp only [T, hN]
    rw [← this]; push_cast; ring
  have hroot : √(S.card * (1 - S.card / N)) * √(T.card * (1 - T.card / N)) =
      S.card * T.card / N := by
    have hS1 : 0 ≤ (S.card : ℝ) * (1 - S.card / N) := by
      rw [show (S.card : ℝ) * (1 - S.card / N) = S.card * T.card / N by rw [hT]; field_simp]
      positivity
    rw [← Real.sqrt_mul hS1]
    have : (S.card : ℝ) * (1 - S.card / N) * (T.card * (1 - T.card / N)) =
        (S.card * T.card / N) ^ 2 := by
      rw [hT]; field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [mul_assoc (d * lam : ℝ), hroot] at hm
  have hlow := (abs_le.mp hm).1
  have key : (d : ℝ) * (1 - lam) * S.card * T.card / N ≤ (G.interedges S T).card := by
    have : (d : ℝ) * (1 - lam) * S.card * T.card / N =
        d * S.card * T.card / N - d * lam * (S.card * T.card / N) := by ring
    linarith
  rw [div_le_iff₀ hNpos] at key
  linarith

omit [DecidableEq V] in
/-- **Independent sets in spectral expanders are small.** If `G` is a `d`-regular graph, `d ≥ 1`,
on `N` vertices that is a spectral expander with parameter `λ`, then every independent set `S`
satisfies `(1 + λ) |S| ≤ λ N`, that is `|S| ≤ (λ / (1 + λ)) N`; so the independence number is at
most `(λ / (1 + λ)) N` (S. Vadhan, *Pseudorandomness* (2012), Problem 4.2 (1)). The proof applies
the expander mixing lemma with `T = S`: there are no edges inside `S`, so
`d |S|² / N ≤ d λ |S| (1 - |S| / N)`. -/
theorem one_add_mul_card_le_of_isIndepSet {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {lam : ℝ} (h : IsSpectralExpander G d lam) (hd : 0 < d) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    (1 + lam) * S.card ≤ lam * Fintype.card V := by
  classical
  obtain ⟨hreg, hlam, hb⟩ := h
  set N : ℝ := (Fintype.card V : ℝ) with hN
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · rw [hS0, Finset.card_empty, Nat.cast_zero, mul_zero]; positivity
  have hNpos : 0 < N := by
    simp only [hN]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨hSne.choose⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrow : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
    funext v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simpa using this
  have hm := abs_indicator_dotProduct_mulVec_sub_le (G.transpose_adjMatrix (α := ℝ))
    (by positivity : (0 : ℝ) ≤ d * lam) hrow hb S S
  rw [← card_interedges_eq_indicator_dotProduct] at hm
  have hempty : G.interedges S S = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ hab
    rw [SimpleGraph.mem_interedges_iff] at hab
    obtain ⟨ha, hb', hadj⟩ := hab
    exact hS ha hb' hadj.ne hadj
  have h1S : 0 ≤ (S.card : ℝ) * (1 - S.card / N) := by
    have : (S.card : ℝ) ≤ N := by
      simp only [hN]; exact_mod_cast Finset.card_le_univ S
    have : (S.card : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr this
    nlinarith
  rw [hempty, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg, mul_assoc (d * lam : ℝ),
    Real.mul_self_sqrt h1S] at hm
  rw [abs_of_nonneg (by positivity)] at hm
  -- `d |S|² / N ≤ d λ |S| (1 - |S| / N)`; divide by `d |S| / N`.
  have key : (S.card : ℝ) ≤ lam * (N - S.card) := by
    have e : (d : ℝ) * S.card * S.card / N = d * S.card / N * S.card := by ring
    have e2 : (d : ℝ) * lam * (S.card * (1 - S.card / N)) =
        d * S.card / N * (lam * (N - S.card)) := by
      field_simp
    rw [e, e2] at hm
    exact le_of_mul_le_mul_left hm (by positivity)
  linarith

end MathlibExt.Combinatorics.SpectralExpander
