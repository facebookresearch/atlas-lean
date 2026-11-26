/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander

import Mathlib.Combinatorics.SimpleGraph.Metric
import MathlibExt.Combinatorics.SimpleGraph.SpectralExpanderLaplacian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Alon-Boppana bound for spectral expanders

A radial test vector on a ball has adjacency Rayleigh quotient close to `2 √(d - 1)`.
A linear cutoff in the radial weight lets us bound the error pointwise, even at the
boundary. Subtracting the mean of the test vector costs little when the ball occupies
only a small fraction of the graph.

## References

* A. Nilli, "On the second eigenvalue of a graph", *Discrete Mathematics* 91(2) (1991),
  207–210, proof of the finite-distance bound. Nilli's localized Rayleigh-quotient argument uses
  neighborhoods of two separated edges. The linear taper and the use of a single ball centered
  by subtracting the mean are adaptations in this proof.
* S. Vadhan, *Pseudorandomness*, *Foundations and Trends in Theoretical Computer Science*
  7(1–3) (2012), 1–336, Theorem 4.11, is the source for the statement, not the proof.
-/

@[expose] public section

open Finset Matrix
open MathlibExt.Combinatorics.SpectralExpander

namespace MathlibExt.GraphTheory.SpectralExpanderWanted

/-- The tree profile `(1 + γ i) / s^i`, tapered to zero at distance `L`. -/
private noncomputable def radialWeight (s γ : ℝ) (L i : ℕ) : ℝ :=
  (1 + γ * i) * (↑(L - i) : ℝ) / s ^ i

private lemma radialWeight_nonneg {s γ : ℝ} (hs : 0 ≤ s) (hγ : 0 ≤ γ) (L i : ℕ) :
    0 ≤ radialWeight s γ L i := by
  unfold radialWeight
  positivity

private lemma radialWeight_antitone {s γ : ℝ} (hs : 1 ≤ s) (hγ : 0 ≤ γ)
    (hγs : 1 + γ ≤ s) (L : ℕ) : Antitone (radialWeight s γ L) := by
  have hs₀ : 0 < s := by linarith
  apply antitone_nat_of_succ_le
  intro i
  have hlin : 1 + γ * (↑i + 1) ≤ s * (1 + γ * ↑i) := calc
    _ = 1 + γ + γ * ↑i := by ring
    _ ≤ s + s * (γ * ↑i) :=
      add_le_add hγs (le_mul_of_one_le_left (by positivity) hs)
    _ = _ := by ring
  have hcut : (↑(L - (i + 1)) : ℝ) ≤ ↑(L - i) := by exact_mod_cast (by omega : L - (i + 1) ≤ L - i)
  simp only [radialWeight, pow_succ, Nat.cast_succ]
  rw [div_mul_eq_div_div_swap, div_le_div_iff_of_pos_right (pow_pos hs₀ _), div_le_iff₀ hs₀]
  calc
    _ ≤ (s * (1 + γ * ↑i)) * (↑(L - i) : ℝ) :=
      mul_le_mul hlin hcut (by positivity) (by positivity)
    _ = _ := by ring

private lemma radialWeight_root {s γ D δ : ℝ} {L : ℕ} (hs : 0 < s) (hL : 1 ≤ L)
    (hroot : D * (1 + γ) = 2 * s ^ 2) (hloss : 2 * s ≤ δ * L) :
    (2 * s - δ) * radialWeight s γ L 0 ≤ D * radialWeight s γ L 1 := by
  have heq : D * radialWeight s γ L 1 = 2 * s * ((L : ℝ) - 1) := by
    rw [radialWeight, Nat.cast_one, mul_one, Nat.cast_sub hL, Nat.cast_one, pow_one,
      ← mul_div_assoc, ← mul_assoc, hroot]
    field_simp
  rw [heq]
  simp only [radialWeight, Nat.cast_zero, mul_zero, add_zero, Nat.sub_zero, one_mul, pow_zero,
    div_one]
  linarith only [hloss]

private lemma radialWeight_step {s γ δ : ℝ} {L i : ℕ} (hs : 0 < s) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (hi : i + 2 ≤ L) (hloss : 2 * s ≤ δ * ((L : ℝ) - 1)) :
    (2 * s - δ) * radialWeight s γ L (i + 1) ≤
      radialWeight s γ L i + s ^ 2 * radialWeight s γ L (i + 2) := by
  have hi₀ : i ≤ L := by omega
  have hi₁ : i + 1 ≤ L := by omega
  have hrec : radialWeight s γ L i + s ^ 2 * radialWeight s γ L (i + 2) =
      2 * s * radialWeight s γ L (i + 1) - 2 * s * γ / s ^ (i + 1) := by
    simp only [radialWeight, Nat.cast_sub hi₀, Nat.cast_sub hi₁, Nat.cast_sub hi,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_add, pow_one]
    field_simp [hs.ne']
    ring
  have hiR : (↑i : ℝ) + 2 ≤ L := by exact_mod_cast hi
  have hcut : 0 ≤ (L : ℝ) - (↑i + 1) := by linarith
  -- At every interior layer, `(i + 1) * (L - i - 1) ≥ L - 1`.
  have hprod : (L : ℝ) - 1 ≤ (↑i + 1) * (L - (↑i + 1)) := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) i)
      (show 0 ≤ (L : ℝ) - ↑i - 2 by linarith)]
  have hmass : γ * ((L : ℝ) - 1) ≤ (1 + γ * (↑i + 1)) * (L - (↑i + 1)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hprod hγ, hcut]
  have herror : 2 * s * γ / s ^ (i + 1) ≤ δ * radialWeight s γ L (i + 1) := by
    simp only [radialWeight, Nat.cast_sub hi₁, Nat.cast_succ, ← mul_div_assoc]
    rw [div_le_div_iff_of_pos_right (pow_pos hs _)]
    calc
      _ ≤ δ * ((L : ℝ) - 1) * γ := mul_le_mul_of_nonneg_right hloss hγ
      _ = δ * (γ * ((L : ℝ) - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hδ
  rw [hrec]
  linarith only [herror]

private lemma exists_dist_predecessor {V : Type*} {G : SimpleGraph V} {a v : V}
    (hv : G.Reachable a v) (hne : v ≠ a) : ∃ u, G.Adj v u ∧ G.dist a u + 1 = G.dist a v := by
  obtain ⟨p, hp⟩ := hv.symm.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ u _ hadj p =>
    have h₁ := G.dist_le p
    have h₂ := hadj.reachable.dist_triangle_left a
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h₂
    simp only [SimpleGraph.Walk.length_cons] at hp
    refine ⟨u, hadj, ?_⟩
    rw [SimpleGraph.dist_comm (u := a), SimpleGraph.dist_comm (u := a)]
    omega

/-- The closed ball of radius `r`. Unreachable vertices have natural distance zero,
so membership also requires reachability. -/
private noncomputable def finiteBall {V : Type*} [Fintype V] (G : SimpleGraph V) (a : V)
    (r : ℕ) : Finset V := by
  classical
  exact univ.filter fun v => G.Reachable a v ∧ G.dist a v ≤ r

private lemma mem_finiteBall {V : Type*} [Fintype V] {G : SimpleGraph V} {a v : V} {r : ℕ} :
    v ∈ finiteBall G a r ↔ G.Reachable a v ∧ G.dist a v ≤ r := by
  classical
  simp [finiteBall]

private lemma card_finiteBall_le {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (hreg : G.IsRegularOfDegree d) (a : V) (r : ℕ) :
    (finiteBall G a r).card ≤ (d + 1) ^ r := by
  classical
  induction r with
  | zero =>
    have heq : finiteBall G a 0 = {a} := by
      ext v
      rw [mem_finiteBall, Finset.mem_singleton, Nat.le_zero]
      constructor
      · rintro ⟨hr, hdist⟩
        exact (hr.dist_eq_zero_iff.mp hdist).symm
      · rintro rfl
        exact ⟨SimpleGraph.Reachable.rfl, G.dist_self⟩
    simp [heq]
  | succ r ih =>
    have hsub : finiteBall G a (r + 1) ⊆
        (finiteBall G a r).biUnion (fun v => insert v (G.neighborFinset v)) := by
      intro v hv
      obtain ⟨hr, hdist⟩ := mem_finiteBall.mp hv
      rw [mem_biUnion]
      by_cases hle : G.dist a v ≤ r
      · exact ⟨v, mem_finiteBall.mpr ⟨hr, hle⟩, mem_insert_self ..⟩
      · have hne : v ≠ a := by rintro rfl; simp at hle
        obtain ⟨u, hadj, hu⟩ := exists_dist_predecessor hr hne
        exact ⟨u, mem_finiteBall.mpr ⟨hr.trans hadj.reachable, by omega⟩,
          mem_insert_of_mem ((G.mem_neighborFinset u v).mpr hadj.symm)⟩
    have hinsert (v : V) : (insert v (G.neighborFinset v)).card = d + 1 := by
      rw [card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree, hreg v]
    calc
      _ ≤ _ := card_le_card hsub
      _ ≤ ∑ v ∈ finiteBall G a r, (insert v (G.neighborFinset v)).card := card_biUnion_le
      _ = (finiteBall G a r).card * (d + 1) := by simp [hinsert]
      _ ≤ (d + 1) ^ (r + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ ih

/-- The tapered profile around `a`, extended by zero to all other components. -/
private noncomputable def ballWeight {V : Type*} (G : SimpleGraph V) (a : V) (s γ : ℝ)
    (L : ℕ) (v : V) : ℝ := by
  classical
  exact if G.Reachable a v then radialWeight s γ L (G.dist a v) else 0

private lemma ballWeight_nonneg {V : Type*} {G : SimpleGraph V} {a v : V} {s γ : ℝ}
    (hs : 0 ≤ s) (hγ : 0 ≤ γ) (L : ℕ) : 0 ≤ ballWeight G a s γ L v := by
  classical
  by_cases hv : G.Reachable a v <;> simp [ballWeight, hv, radialWeight_nonneg hs hγ]

private lemma ballWeight_self {V : Type*} (G : SimpleGraph V) (a : V) (s γ : ℝ) (L : ℕ) :
    ballWeight G a s γ L a = L := by
  classical
  simp [ballWeight, radialWeight]

private lemma ballWeight_eq_zero_of_notMem {V : Type*} [Fintype V] {G : SimpleGraph V} {a v : V}
    {s γ : ℝ} {L : ℕ} (hv : v ∉ finiteBall G a L) : ballWeight G a s γ L v = 0 := by
  classical
  by_cases hr : G.Reachable a v
  · have hdist : L ≤ G.dist a v := by
      by_contra! h
      exact hv (mem_finiteBall.mpr ⟨hr, h.le⟩)
    simp [ballWeight, hr, radialWeight, Nat.sub_eq_zero_of_le hdist]
  · simp [ballWeight, hr]

private lemma mul_ballWeight_le_adjMatrix_mulVec {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d L : ℕ} {s γ δ : ℝ}
    (hreg : G.IsRegularOfDegree d) (hs : 1 ≤ s) (hγ : 0 ≤ γ) (hγs : 1 + γ ≤ s)
    (hD : (d : ℝ) = s ^ 2 + 1) (hroot : (d : ℝ) * (1 + γ) = 2 * s ^ 2)
    (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hloss : 2 * s ≤ δ * ((L : ℝ) - 1)) (a v : V) :
    (2 * s - δ) * ballWeight G a s γ L v ≤
      (G.adjMatrix ℝ *ᵥ ballWeight G a s γ L) v := by
  classical
  have hs₀ : 0 < s := by linarith
  let f := ballWeight G a s γ L
  change (2 * s - δ) * f v ≤ (G.adjMatrix ℝ *ᵥ f) v
  rw [G.adjMatrix_mulVec_apply]
  have hnn : ∀ u, 0 ≤ f u := fun _ => ballWeight_nonneg hs₀.le hγ L
  by_cases hv : f v = 0
  · rw [hv, mul_zero]
    exact sum_nonneg fun u _ => hnn u
  have hreach : G.Reachable a v := by
    by_contra h
    exact hv (by simp [f, ballWeight, h])
  have hdist : G.dist a v < L := by
    by_contra! h
    exact hv (by simp [f, ballWeight, hreach, radialWeight, Nat.sub_eq_zero_of_le h])
  have hf (u : V) (hu : G.Reachable a u) : f u = radialWeight s γ L (G.dist a u) := by
    simp [f, ballWeight, hu]
  have hcard (u : V) : (G.neighborFinset u).card = d :=
    (G.card_neighborFinset_eq_degree u).trans (hreg u)
  by_cases hcenter : v = a
  · subst v
    have hsum : ∑ u ∈ G.neighborFinset a, f u = (d : ℝ) * radialWeight s γ L 1 := by
      calc
        _ = ∑ u ∈ G.neighborFinset a, radialWeight s γ L 1 := by
          refine sum_congr rfl fun u hu => ?_
          have hadj := (G.mem_neighborFinset a u).mp hu
          rw [hf u hadj.reachable, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
        _ = _ := by simp [hcard]
    rw [hsum, hf a hreach, G.dist_self]
    exact radialWeight_root hs₀ hL hroot (by linarith only [hloss, hδ])
  · obtain ⟨u, hadj, hu⟩ := exists_dist_predecessor hreach hcenter
    let i := G.dist a u
    change i + 1 = G.dist a v at hu
    have huMem : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hadj
    have hua := hreach.trans hadj.reachable
    have hcards : ((G.neighborFinset v).erase u).card = d - 1 := by
      rw [card_erase_of_mem huMem, hcard]
    have hrest : s ^ 2 * radialWeight s γ L (i + 2) ≤
        ∑ w ∈ (G.neighborFinset v).erase u, f w := by
      have hd : 1 ≤ d := by
        rw [← hcard v]
        exact (card_pos.mpr ⟨u, huMem⟩)
      calc
        _ = ∑ _w ∈ (G.neighborFinset v).erase u, radialWeight s γ L (i + 2) := by
          simp only [sum_const, nsmul_eq_mul, hcards, Nat.cast_sub hd, Nat.cast_one, hD,
            add_sub_cancel_right]
        _ ≤ _ := by
          refine sum_le_sum fun w hw => ?_
          have hvw := (G.mem_neighborFinset v w).mp (mem_of_mem_erase hw)
          rw [hf w (hreach.trans hvw.reachable)]
          apply radialWeight_antitone hs hγ hγs L
          have hh := hvw.reachable.dist_triangle_right a
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw, ← hu] at hh
          simpa [Nat.add_assoc] using hh
    rw [hf v hreach, ← hu, ← sum_erase_add _ _ huMem]
    calc
      _ ≤ radialWeight s γ L i + s ^ 2 * radialWeight s γ L (i + 2) :=
        radialWeight_step hs₀ hγ hδ (by omega) hloss
      _ ≤ _ := by
        rw [hf u hua, add_comm]
        exact add_le_add hrest le_rfl

/-- Centering a vector supported on a fraction `β` of the vertices loses at most `d * β`
in the lower bound obtained from its adjacency Rayleigh quotient. -/
private lemma spectral_bound_of_supported_rayleigh {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {lam c β : ℝ}
    (hG : IsSpectralExpander G d lam) (a : V) (S : Finset V) (f : V → ℝ)
    (ha : f a ≠ 0) (hsupp : ∀ v ∉ S, f v = 0)
    (hsize : (S.card : ℝ) ≤ β * Fintype.card V)
    (hRay : c * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.adjMatrix ℝ *ᵥ f)) : c - d * β ≤ d * lam := by
  classical
  let N : ℝ := Fintype.card V
  let m : ℝ := (∑ v, f v) / N
  let x : V → ℝ := f - m • 1
  let A := G.adjMatrix ℝ
  have hN : 0 < N := by
    have : Nonempty V := ⟨a⟩
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hm : ∑ v, f v = N * m := by
    dsimp [m]
    field_simp
  have h11 : (1 : V → ℝ) ⬝ᵥ 1 = N := by simp [N, dotProduct_one]
  have hx : x ⬝ᵥ 1 = 0 := by
    change (f - m • 1) ⬝ᵥ (1 : V → ℝ) = 0
    rw [sub_dotProduct, smul_dotProduct, h11, dotProduct_one, hm, smul_eq_mul]
    ring
  have hx' : (1 : V → ℝ) ⬝ᵥ x = 0 := by rwa [dotProduct_comm]
  have hf : f = x + m • 1 := by simp [x]
  have hrow : A *ᵥ (1 : V → ℝ) = (d : ℝ) • 1 := by
    funext v
    simpa [A] using G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hG.1 (v := v)
  have hcol : (1 : V → ℝ) ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, show Aᵀ = A from G.transpose_adjMatrix (α := ℝ),
      hrow, smul_dotProduct, hx', smul_zero]
  have hnorm : f ⬝ᵥ f = x ⬝ᵥ x + N * m ^ 2 := by
    conv_lhs => rw [hf]
    simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, hx, hx', h11,
      smul_eq_mul]
    ring
  have hbil : f ⬝ᵥ (A *ᵥ f) = x ⬝ᵥ (A *ᵥ x) + d * (N * m ^ 2) := by
    conv_lhs => rw [hf]
    simp only [mulVec_add, mulVec_smul, hrow, add_dotProduct, dotProduct_add, dotProduct_smul,
      smul_dotProduct, hx, hcol, h11, smul_eq_mul]
    ring
  have hAx : x ⬝ᵥ (A *ᵥ x) ≤ (d : ℝ) * lam * (x ⬝ᵥ x) := by
    have hL : G.lapMatrix ℝ *ᵥ x = (d : ℝ) • x - A *ᵥ x := by
      funext v
      simp [A, SimpleGraph.lapMatrix, sub_mulVec, SimpleGraph.degMatrix_mulVec_apply, hG.1 v]
    have hform : x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) = (d : ℝ) * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
      rw [hL, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hlap := mul_dotProduct_le_lapMatrix hG x hx
    rw [hform] at hlap
    linarith only [hlap]
  have habs : 0 < f ⬝ᵥ f := by
    rw [dotProduct]
    exact (mul_self_pos.mpr ha).trans_le
      (single_le_sum (fun v _ => mul_self_nonneg (f v)) (mem_univ a))
  have hsum : ∑ v ∈ S, f v = ∑ v, f v := sum_subset (subset_univ S) (fun v _ => hsupp v)
  have hsquares : ∑ v ∈ S, f v ^ 2 = f ⬝ᵥ f := by
    simp only [dotProduct, sq]
    exact sum_subset (subset_univ S) (fun v _ hv => by simp [hsupp v hv])
  have hcs : (∑ v, f v) ^ 2 ≤ S.card * (f ⬝ᵥ f) := by
    simpa only [mul_one, one_pow, sum_const, nsmul_eq_mul, hsum, hsquares, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq S f fun _ => (1 : ℝ))
  have hmean : N * m ^ 2 ≤ β * (f ⬝ᵥ f) := by
    apply le_of_mul_le_mul_left _ hN
    calc
      N * (N * m ^ 2) = (∑ v, f v) ^ 2 := by rw [hm]; ring
      _ ≤ S.card * (f ⬝ᵥ f) := hcs
      _ ≤ (β * N) * (f ⬝ᵥ f) := mul_le_mul_of_nonneg_right hsize habs.le
      _ = _ := by ring
  have hxnorm : x ⬝ᵥ x ≤ f ⬝ᵥ f := by rw [hnorm]; exact le_add_of_nonneg_right (by positivity)
  have hlam := hG.2.1
  have hupper : f ⬝ᵥ (A *ᵥ f) ≤ ((d : ℝ) * lam + d * β) * (f ⬝ᵥ f) := calc
    _ = x ⬝ᵥ (A *ᵥ x) + d * (N * m ^ 2) := hbil
    _ ≤ (d : ℝ) * lam * (f ⬝ᵥ f) + d * (β * (f ⬝ᵥ f)) :=
      add_le_add (hAx.trans (mul_le_mul_of_nonneg_left hxnorm (by positivity)))
        (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg d))
    _ = _ := by ring
  linarith only [le_of_mul_le_mul_right (hRay.trans hupper) habs]

/-- **Alon-Boppana bound.** Fix a degree `d`. For every `ε > 0` there is `N₀` such that every
`d`-regular graph on `n ≥ N₀` vertices that is a spectral expander with parameter `λ` has
`λ ≥ 2 √(d - 1) / d - ε`: the spectral parameter of large `d`-regular graphs is at least
`2 √(d - 1) / d - o(1)` as the number of vertices tends to infinity (S. Vadhan,
*Pseudorandomness* (2012), Theorem 4.11, stated there for multigraphs; this is the case of simple
graphs; due to Alon and Boppana, with a short proof by A. Nilli, Discrete Math. 91 (1991)). -/
theorem alon_boppana (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : ℝ),
      IsSpectralExpander G d lam → 2 * Real.sqrt ((d : ℝ) - 1) / d - ε ≤ lam := by
  by_cases hd : 2 ≤ d
  · let D := (d : ℝ)
    let s := Real.sqrt (D - 1)
    let γ := (D - 2) / D
    let δ := D * (ε / 2)
    have hD₂ : 2 ≤ D := by
      dsimp [D]
      exact_mod_cast hd
    have hD₀ : 0 < D := by linarith
    have hsq : s ^ 2 = D - 1 := Real.sq_sqrt (by linarith)
    have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
    have hs : 1 ≤ s := by nlinarith only [hsq, hD₂, hs₀, sq_nonneg s]
    have hD : D = s ^ 2 + 1 := by linarith only [hsq]
    have hγ : 0 ≤ γ := div_nonneg (by linarith) hD₀.le
    have hroot : D * (1 + γ) = 2 * s ^ 2 := by
      dsimp [γ]
      rw [hsq]
      field_simp
      ring
    have hγs : 1 + γ ≤ s := by
      apply le_of_mul_le_mul_left _ hD₀
      rw [hroot, hD]
      nlinarith only [mul_nonneg hs₀ (sq_nonneg (s - 1))]
    have hδ : 0 < δ := mul_pos hD₀ (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * s / δ)
    let L := m + 2
    have hL : 1 ≤ L := by dsimp [L]; omega
    have hm' : 2 * s ≤ δ * (m : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).mp hm |>.le
    have hL' : 2 * s ≤ δ * ((L : ℝ) - 1) := by
      have hLm : (m : ℝ) ≤ (L : ℝ) - 1 := by dsimp [L]; push_cast; linarith
      exact hm'.trans (mul_le_mul_of_nonneg_left hLm hδ.le)
    let B := (d + 1) ^ L
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B / (ε / 2) : ℝ)
    refine ⟨max 1 N₀, ?_⟩
    intro n hn G _ lam hG
    classical
    let a : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N₀).trans hn)⟩
    let S := finiteBall G a L
    let f := ballWeight G a s γ L
    have ha : f a ≠ 0 := by
      dsimp [f]
      rw [ballWeight_self]
      exact_mod_cast (show L ≠ 0 by omega)
    have hsize : (S.card : ℝ) ≤ ε / 2 * Fintype.card (Fin n) := by
      have hBn : (B : ℝ) ≤ (ε / 2) * n := by
        have hn' : (N₀ : ℝ) ≤ n := by exact_mod_cast ((le_max_right 1 N₀).trans hn)
        have hε₂ : 0 < ε / 2 := by positivity
        calc
          _ ≤ (N₀ : ℝ) * (ε / 2) := (div_lt_iff₀ hε₂).mp hN₀ |>.le
          _ = (ε / 2) * (N₀ : ℝ) := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hn' hε₂.le
      simpa only [Fintype.card_fin] using
        (Nat.cast_le.mpr (card_finiteBall_le hG.1 a L)).trans hBn
    have hRay : (2 * s - δ) * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.adjMatrix ℝ *ᵥ f) := by
      simp only [dotProduct, mul_sum]
      refine sum_le_sum fun v _ => ?_
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left
        (mul_ballWeight_le_adjMatrix_mulVec hG.1 hs hγ hγs hD hroot hL hδ.le hL' a v)
        (ballWeight_nonneg hs₀ hγ L)
    have hbound := spectral_bound_of_supported_rayleigh hG a S f ha
      (fun _ hv => ballWeight_eq_zero_of_notMem hv) hsize hRay
    change 2 * s / D - ε ≤ lam
    rw [sub_le_iff_le_add, div_le_iff₀ hD₀]
    change 2 * s - D * (ε / 2) - D * (ε / 2) ≤ D * lam at hbound
    linarith only [hbound]
  · refine ⟨0, ?_⟩
    intro n _ G _ lam hG
    have hlam := hG.2.1
    interval_cases d
    · simpa using (show -ε ≤ lam by linarith)
    · simpa using (show -ε ≤ lam by linarith)

end MathlibExt.GraphTheory.SpectralExpanderWanted
