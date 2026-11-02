/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The Kővári–Sós–Turán bound

This file proves the standard upper bound for the Zarankiewicz number by double-counting common
neighborhoods and applying the power-mean inequality.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset Fintype

private theorem kst_degree_sum {m n : ℕ} (G : SimpleGraph (Fin m ⊕ Fin n))
    [DecidableRel G.Adj] (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n)) :
    ∑ u : Fin m, G.degree (.inl u) = #G.edgeFinset := by
  let left : Finset (Fin m ⊕ Fin n) :=
    Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  let right : Finset (Fin m ⊕ Fin n) :=
    Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hK := SimpleGraph.IsBipartiteWith.completeBipartiteGraph (Fin m) (Fin n)
  have hB₀ : G.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) :=
    ⟨hK.disjoint, fun {_ _} hadj ↦ hK.mem_of_adj (hG hadj)⟩
  have hB : G.IsBipartiteWith (left : Set _) (right : Set _) := by
    simpa [left, right] using hB₀
  simpa [left] using SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hB

private theorem kst_card_right_neighbors {m n : ℕ} (G : SimpleGraph (Fin m ⊕ Fin n))
    [DecidableRel G.Adj] (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n)) (u : Fin m) :
    #{w : Fin n | G.Adj (.inl u) (.inr w)} = G.degree (.inl u) := by
  let emb : Fin n ↪ Fin m ⊕ Fin n := ⟨Sum.inr, Sum.inr_injective⟩
  let neighbors : Finset (Fin n) := {w | G.Adj (.inl u) (.inr w)}
  have hneighbors : G.neighborFinset (.inl u) = neighbors.map emb := by
    ext v
    cases v with
    | inl v =>
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, emb, neighbors]
        constructor
        · intro hadj
          simpa using hG hadj
        · rintro ⟨_, _, h⟩
          simp at h
    | inr w => simp [SimpleGraph.mem_neighborFinset, emb, neighbors]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors, Finset.card_map]

private theorem kst_common_left_neighbors_le {m n s t : ℕ}
    (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (hs : 1 ≤ s) (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G)
    (T : Finset (Fin n)) (hT : #T = t) :
    #{u : Fin m | ∀ w ∈ T, G.Adj (.inl u) (.inr w)} ≤ s - 1 := by
  let common : Finset (Fin m) := {u | ∀ w ∈ T, G.Adj (.inl u) (.inr w)}
  by_contra hle
  change ¬#common ≤ s - 1 at hle
  have hscommon : s ≤ #common := by omega
  obtain ⟨A, hA, hcardA⟩ := Finset.exists_subset_card_eq hscommon
  apply hfree
  rw [SimpleGraph.completeBipartiteGraph_isContained_iff]
  let inlEmb : Fin m ↪ Fin m ⊕ Fin n := ⟨Sum.inl, Sum.inl_injective⟩
  let inrEmb : Fin n ↪ Fin m ⊕ Fin n := ⟨Sum.inr, Sum.inr_injective⟩
  refine ⟨A.map inlEmb, T.map inrEmb, ?_, ?_, ?_⟩
  · simp [hcardA]
  · simp [hT]
  · intro x hx y hy
    change x ∈ A.map inlEmb at hx
    change y ∈ T.map inrEmb at hy
    simp only [Finset.mem_map] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    have hucommon := hA hu
    have hucommon' : ∀ w ∈ T, G.Adj (.inl u) (.inr w) := by
      simpa only [common, Finset.mem_filter, Finset.mem_univ, true_and] using hucommon
    exact hucommon' w hw

private theorem kst_sum_choose_degree_le {m n s t : ℕ}
    (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n)) (hs : 1 ≤ s)
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G) :
    ∑ u : Fin m, (G.degree (.inl u)).choose t ≤ (s - 1) * n.choose t := by
  let N (u : Fin m) : Finset (Fin n) := {w | G.Adj (.inl u) (.inr w)}
  let subsets : Finset (Finset (Fin n)) := Finset.univ.powersetCard t
  have hdegree (u : Fin m) : #(N u) = G.degree (.inl u) := by
    exact kst_card_right_neighbors G hG u
  calc
    ∑ u : Fin m, (G.degree (.inl u)).choose t =
        ∑ u : Fin m, #((N u).powersetCard t) := by
      simp only [Finset.card_powersetCard, hdegree]
    _ = ∑ u : Fin m, ∑ T ∈ subsets, if T ⊆ N u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_boole]
      congr 1
      ext T
      simp [subsets, and_comm]
    _ = ∑ T ∈ subsets, ∑ u : Fin m, if T ⊆ N u then 1 else 0 := Finset.sum_comm
    _ = ∑ T ∈ subsets, #{u : Fin m | ∀ w ∈ T, G.Adj (.inl u) (.inr w)} := by
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext u
      simp [N, Finset.subset_iff]
    _ ≤ ∑ _T ∈ subsets, (s - 1) := by
      apply Finset.sum_le_sum
      intro T hT
      apply kst_common_left_neighbors_le G hs hfree T
      simpa [subsets] using (Finset.mem_powersetCard.mp hT).2
    _ = (s - 1) * n.choose t := by
      simp [subsets, Finset.card_powersetCard, Nat.mul_comm]

private theorem kst_shift_pow_mul_choose_le {d n t : ℕ} (hdn : d ≤ n) :
    ((d + 1 - t : ℕ) : ℝ) ^ t * (n.choose t : ℝ) ≤
      ((n + 1 - t : ℕ) : ℝ) ^ t * (d.choose t : ℝ) := by
  by_cases htd : t ≤ d
  · have htn : t ≤ n := htd.trans hdn
    have hfactor (i : ℕ) (hi : i ∈ Finset.range t) :
        ((d + 1 - t : ℕ) : ℝ) * (n - i : ℕ) ≤
          ((n + 1 - t : ℕ) : ℝ) * (d - i : ℕ) := by
      have hit : i < t := Finset.mem_range.mp hi
      have hid : i ≤ d := hit.le.trans htd
      have hin : i ≤ n := hid.trans hdn
      rw [Nat.cast_sub (by omega : t ≤ d + 1), Nat.cast_sub (by omega : t ≤ n + 1),
        Nat.cast_sub hin, Nat.cast_sub hid]
      push_cast
      have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
      have hit' : (i : ℝ) + 1 ≤ t := by exact_mod_cast hit
      have hmul : 0 ≤ ((n : ℝ) - d) * ((t : ℝ) - 1 - i) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hprod :
        ∏ i ∈ Finset.range t, ((d + 1 - t : ℕ) : ℝ) * (n - i : ℕ) ≤
          ∏ i ∈ Finset.range t, ((n + 1 - t : ℕ) : ℝ) * (d - i : ℕ) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) hfactor
    have hnprod :
        ∏ i ∈ Finset.range t, ((n - i : ℕ) : ℝ) =
          (t.factorial : ℝ) * (n.choose t : ℝ) := by
      rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      rfl
    have hdprod :
        ∏ i ∈ Finset.range t, ((d - i : ℕ) : ℝ) =
          (t.factorial : ℝ) * (d.choose t : ℝ) := by
      rw [← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      rfl
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
    simp only [Finset.prod_const, Finset.card_range, hnprod, hdprod] at hprod
    have hfactorial : (0 : ℝ) < t.factorial := by positivity
    nlinarith
  · have : d + 1 - t = 0 := by omega
    have ht : 0 < t := by omega
    rw [this, Nat.cast_zero, zero_pow (Nat.ne_of_gt ht), zero_mul]
    positivity

private theorem kst_shifted_moment_le {m n s t : ℕ}
    (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (htn : t ≤ n) (hs : 1 ≤ s)
    (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n))
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G) :
    ∑ u : Fin m, ((G.degree (.inl u) + 1 - t : ℕ) : ℝ) ^ t ≤
      ((s - 1 : ℕ) : ℝ) * ((n + 1 - t : ℕ) : ℝ) ^ t := by
  let x (u : Fin m) : ℝ := ((G.degree (.inl u) + 1 - t : ℕ) : ℝ)
  let y : ℝ := ((n + 1 - t : ℕ) : ℝ)
  have hdegree (u : Fin m) : G.degree (.inl u) ≤ n := by
    rw [← kst_card_right_neighbors G hG u]
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun w : Fin n ↦ G.Adj (.inl u) (.inr w)) Finset.univ)
  have hterm (u : Fin m) :
      x u ^ t * (n.choose t : ℝ) ≤ y ^ t * (G.degree (.inl u)).choose t := by
    exact kst_shift_pow_mul_choose_le (hdegree u)
  have hterms :
      (∑ u : Fin m, x u ^ t) * (n.choose t : ℝ) ≤
        y ^ t * ∑ u : Fin m, ((G.degree (.inl u)).choose t : ℝ) := by
    calc
      (∑ u : Fin m, x u ^ t) * (n.choose t : ℝ) =
          ∑ u : Fin m, x u ^ t * (n.choose t : ℝ) := by rw [Finset.sum_mul]
      _ ≤ ∑ u : Fin m, y ^ t * (G.degree (.inl u)).choose t := by
        exact Finset.sum_le_sum fun u _ ↦ hterm u
      _ = y ^ t * ∑ u : Fin m, ((G.degree (.inl u)).choose t : ℝ) := by
        rw [Finset.mul_sum]
  have hcount := kst_sum_choose_degree_le G hG hs hfree
  have hcount' :
      (∑ u : Fin m, ((G.degree (.inl u)).choose t : ℝ)) ≤
        ((s - 1 : ℕ) : ℝ) * (n.choose t : ℝ) := by
    exact_mod_cast hcount
  have hcombined := hterms.trans (mul_le_mul_of_nonneg_left hcount' (by positivity : 0 ≤ y ^ t))
  have hchoose : (0 : ℝ) < n.choose t := by exact_mod_cast Nat.choose_pos htn
  dsimp only [x, y] at hcombined ⊢
  nlinarith

private theorem kst_excess_pow_le {m n s t : ℕ}
    (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (ht : 0 < t) (htn : t ≤ n) (hs : 1 ≤ s)
    (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n))
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G)
    (hedge : ((t : ℝ) - 1) * m < (#G.edgeFinset : ℝ)) :
    ((#G.edgeFinset : ℝ) - ((t : ℝ) - 1) * m) ^ t ≤
      ((s : ℝ) - 1) * ((n : ℝ) - t + 1) ^ t * (m : ℝ) ^ (t - 1) := by
  let x (u : Fin m) : ℝ := ((G.degree (.inl u) + 1 - t : ℕ) : ℝ)
  let shiftSum : ℕ := ∑ u : Fin m, (G.degree (.inl u) + 1 - t)
  have hpoint (u : Fin m) :
      G.degree (.inl u) ≤ G.degree (.inl u) + 1 - t + (t - 1) := by omega
  have hsumNat :
      #G.edgeFinset ≤ shiftSum + (t - 1) * m := by
    calc
      #G.edgeFinset = ∑ u : Fin m, G.degree (.inl u) := (kst_degree_sum G hG).symm
      _ ≤ ∑ u : Fin m, ((G.degree (.inl u) + 1 - t) + (t - 1)) := by
        exact Finset.sum_le_sum (s := Finset.univ) fun u _ ↦ hpoint u
      _ = shiftSum + (t - 1) * m := by
        rw [Finset.sum_add_distrib]
        simp [shiftSum, Nat.mul_comm]
  have hxsum : (shiftSum : ℝ) = ∑ u : Fin m, x u := by
    simp [shiftSum, x]
  have hsumReal :
      (#G.edgeFinset : ℝ) ≤ (∑ u : Fin m, x u) + ((t - 1 : ℕ) : ℝ) * m := by
    rw [← hxsum]
    exact_mod_cast hsumNat
  have ht1 : 1 ≤ t := ht
  rw [Nat.cast_sub ht1] at hsumReal
  push_cast at hsumReal
  have hqsum :
      (#G.edgeFinset : ℝ) - ((t : ℝ) - 1) * m ≤ ∑ u : Fin m, x u := by
    linarith
  have hqnonneg : 0 ≤ (#G.edgeFinset : ℝ) - ((t : ℝ) - 1) * m := by linarith
  have hmean := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset (Fin m))) (f := x) (fun _ _ ↦ by positivity) (t - 1)
  have htadd : t - 1 + 1 = t := Nat.sub_add_cancel ht1
  simp only [htadd, Finset.card_univ, Fintype.card_fin] at hmean
  have hmoment := kst_shifted_moment_le G htn hs hG hfree
  have hmoment' :
      ∑ u : Fin m, x u ^ t ≤ ((s : ℝ) - 1) * ((n : ℝ) - t + 1) ^ t := by
    have hsCast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs]
      norm_num
    have hnCast : ((n + 1 - t : ℕ) : ℝ) = (n : ℝ) - t + 1 := by
      rw [Nat.cast_sub (by omega : t ≤ n + 1)]
      push_cast
      ring
    simpa only [x, hsCast, hnCast] using hmoment
  have hmean' := hmean.trans
    (mul_le_mul_of_nonneg_left hmoment' (by positivity : 0 ≤ (m : ℝ) ^ (t - 1)))
  exact (pow_le_pow_left₀ hqnonneg hqsum t).trans <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmean'

private theorem kst_root_bound {a b c q : ℝ} {t : ℕ}
    (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hq : 0 ≤ q)
    (h : q ^ t ≤ a * b ^ t * c ^ (t - 1)) :
    q ≤ Real.rpow a (1 / (t : ℝ)) * b * Real.rpow c (1 - 1 / (t : ℝ)) := by
  have htne : t ≠ 0 := Nat.ne_of_gt ht
  have ht1 : 1 ≤ t := ht
  have htCast : (t : ℝ) ≠ 0 := by positivity
  have hExp : ((t - 1 : ℕ) : ℝ) * (t : ℝ)⁻¹ = 1 - 1 / (t : ℝ) := by
    rw [Nat.cast_sub ht1]
    push_cast
    field_simp
  calc
    q = Real.rpow (q ^ t) ((t : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast hq htne).symm
    _ ≤ Real.rpow (a * b ^ t * c ^ (t - 1)) ((t : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = Real.rpow a ((t : ℝ)⁻¹) * b * Real.rpow c (1 - 1 / (t : ℝ)) := by
      change (a * b ^ t * c ^ (t - 1)) ^ ((t : ℝ)⁻¹) =
        a ^ ((t : ℝ)⁻¹) * b * c ^ (1 - 1 / (t : ℝ))
      rw [Real.mul_rpow (x := a * b ^ t) (y := c ^ (t - 1))
          (z := (t : ℝ)⁻¹)
          (mul_nonneg ha (by positivity)) (by positivity),
        Real.mul_rpow (x := a) (y := b ^ t) (z := (t : ℝ)⁻¹) ha (by positivity),
        Real.pow_rpow_inv_natCast hb htne,
        ← Real.rpow_natCast_mul hc.le, hExp]
    _ = Real.rpow a (1 / (t : ℝ)) * b * Real.rpow c (1 - 1 / (t : ℝ)) := by
      rw [one_div]

private theorem kst_fixed_graph_bound {m n s t : ℕ}
    (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (ht : 0 < t) (hs : 1 ≤ s) (htn : t ≤ n)
    (hG : G ≤ completeBipartiteGraph (Fin m) (Fin n))
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G) :
    (#G.edgeFinset : ℝ) ≤
      Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - (t : ℝ) + 1) *
        Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) + ((t : ℝ) - 1) * (m : ℝ) := by
  have hsReal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htnReal : (t : ℝ) ≤ n := by exact_mod_cast htn
  have ha : 0 ≤ (s : ℝ) - 1 := by linarith
  have hb : 0 ≤ (n : ℝ) - t + 1 := by linarith
  have hfirst :
      0 ≤ Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - t + 1) *
        Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ha _) hb)
      (Real.rpow_nonneg (by positivity) _)
  by_cases hm : m = 0
  · subst m
    have hedge : #G.edgeFinset = 0 := by
      simpa only [Fintype.sum_empty] using (kst_degree_sum G hG).symm
    rw [hedge, Nat.cast_zero]
    norm_num at hfirst ⊢
    exact hfirst
  · have hmReal : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    by_cases hedge : (#G.edgeFinset : ℝ) ≤ ((t : ℝ) - 1) * m
    · linarith
    · have hedge' : ((t : ℝ) - 1) * m < (#G.edgeFinset : ℝ) := lt_of_not_ge hedge
      have hpow := kst_excess_pow_le G ht htn hs hG hfree hedge'
      have hroot := kst_root_bound ht ha hb hmReal (by linarith) hpow
      linarith

/-- **Kővári–Sós–Turán bound.** Let $m, n, s, t$ be natural numbers with $s \ge 1$ and
$1 \le t \le n$. Let $z(m, n; s, t)$ be the Zarankiewicz number, the largest number of edges in a
bipartite graph with parts of sizes $m$ and $n$ that contains no copy of the complete bipartite
graph $K_{s,t}$. Then
$$z(m, n; s, t) \le (s - 1)^{1/t} (n - t + 1) m^{1 - 1/t} + (t - 1) m.$$

Proof: Double-count common right neighborhoods, apply the power-mean inequality, and take a real
$t$-th root, following Kővári–Sós–Turán (1954) and Jukna, Theorem 2.10.

Proves `Wanted` entry `kovari_sos_turan`.

Source: statement `kovari-sos-turan-s1` from https://en.wikipedia.org/wiki/Zarankiewicz_problem.
-/
public theorem kovari_sos_turan (m n s t : ℕ) (ht : 0 < t) (hs : 1 ≤ s)
    (htn : t ≤ n) :
    (SimpleGraph.zarankiewicz m n s t : ℝ) ≤
      Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - (t : ℝ) + 1) *
        Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) + ((t : ℝ) - 1) * (m : ℝ) := by
  have hsReal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htReal : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htnReal : (t : ℝ) ≤ n := by exact_mod_cast htn
  have ha : 0 ≤ (s : ℝ) - 1 := by linarith
  have hb : 0 ≤ (n : ℝ) - t + 1 := by linarith
  have hfirst :
      0 ≤ Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - t + 1) *
        Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ha _) hb)
      (Real.rpow_nonneg (by positivity) _)
  have hsecond : 0 ≤ ((t : ℝ) - 1) * (m : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  have hrhs :
      0 ≤ Real.rpow ((s : ℝ) - 1) (1 / (t : ℝ)) * ((n : ℝ) - t + 1) *
        Real.rpow (m : ℝ) (1 - 1 / (t : ℝ)) + ((t : ℝ) - 1) * (m : ℝ) :=
    add_nonneg hfirst hsecond
  apply (SimpleGraph.zarankiewicz_le_iff_of_nonneg
    (V := Fin m) (W := Fin n) (α := Fin s) (β := Fin t)
    (by simp) (by simp) (by simp) (by simp) hrhs).2
  intro G _ hG hfree
  exact kst_fixed_graph_bound G ht hs htn hG hfree

end

end MetaMathlibExt
