/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary

import MathlibExt.Combinatorics.EndpointMapMultigraph.Conductance
import MathlibExt.Probability.CanonicalPaths
import MathlibExt.Probability.PoincareMixing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cheeger's inequality for reversible Markov chains

A conductance lower bound `Φ` gives the spectral gap bound `1 - μ ≥ Φ² / 2` for each real
eigenvalue `μ ≠ 1`. We apply the weighted multigraph threshold-cut theorem to the positive
part of a suitably signed eigenvector.
-/

public section

open Finset Matrix ProbabilityTheory EndpointMapMultigraph
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.PoincareMixing

namespace MathlibExt.Probability.MulticommodityFlowWanted

section

variable {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ} {P : Matrix S S ℝ}

/-- Each orientation gets half the stationary flow, so the undirected degree is `π`,
including at vertices with self-loops. -/
private noncomputable def edgeWeight (π : S → ℝ) (P : Matrix S S ℝ) (e : S × S) : ℝ :=
  π e.1 * P e.1 e.2 / 2

private lemma chain_degree (hP : P ∈ rowStochastic ℝ S) (hrev : IsDetailedBalance π P) (x : S) :
    weightedDegree Prod.fst Prod.snd (edgeWeight π P) x = π x := by
  have hrow (u : S) : ∑ v, edgeWeight π P (u, v) = π u / 2 := by
    simp [edgeWeight, ← sum_div, ← mul_sum, sum_row_of_mem_rowStochastic hP]
  have hcol : ∑ u, edgeWeight π P (u, x) = π x / 2 := by
    rw [← hrow]
    exact sum_congr rfl fun u _ => congrArg (· / 2) (hrev u x)
  rw [weightedDegree, Fintype.sum_prod_type]
  simp only [mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib]
  rw [sum_comm (f := fun u v => if u = x then edgeWeight π P (u, v) else 0)]
  simp [hrow, hcol]

private lemma chain_cut (hrev : IsDetailedBalance π P) (A : Finset S) :
    ∑ e ∈ cut Prod.fst Prod.snd A, edgeWeight π P e =
      ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v := by
  have hcut : cut Prod.fst Prod.snd A = (A ×ˢ Aᶜ) ∪ (Aᶜ ×ˢ A) := by
    ext ⟨u, v⟩
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu, hv]
  have hd : Disjoint (A ×ˢ Aᶜ) (Aᶜ ×ˢ A) :=
    disjoint_left.mpr fun e h₁ h₂ => (mem_compl.mp (mem_product.mp h₂).1) (mem_product.mp h₁).1
  rw [hcut, sum_union hd, sum_product, sum_product, sum_comm (s := Aᶜ)]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun v _ => by simp [edgeWeight, ← hrev u v]

omit [DecidableEq S] in
private lemma exists_small_positive_side (hπ1 : ∑ x, π x = 1) (hπ : ∀ x, 0 < π x)
    {μ : ℝ} {f : S → ℝ} (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) :
    ∃ g : S → ℝ, g ≠ 0 ∧ P *ᵥ g = μ • g ∧
      ∑ x ∈ univ.filter (fun x => 0 < g x), π x ≤ 1 / 2 := by
  by_cases h : ∑ x ∈ univ.filter (fun x => 0 < f x), π x ≤ 1 / 2
  · exact ⟨f, hf, heig, h⟩
  refine ⟨-f, neg_ne_zero.mpr hf, by rw [mulVec_neg, heig, smul_neg], ?_⟩
  have hsub : univ.filter (fun x => 0 < (-f) x) ⊆ univ.filter (fun x => ¬0 < f x) := by
    intro x hx
    simpa using (show f x ≤ 0 from (neg_pos.mp (mem_filter.mp hx).2).le)
  have hle := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => (hπ x).le)
  have htot := sum_filter_add_sum_filter_not univ (fun x => 0 < f x) π
  linarith

/-- Truncating an eigenvector to its positive part bounds its graph Rayleigh quotient by
`1 - μ`. Stochasticity gives `P g ≤ P g⁺`, and only vertices with `g > 0` contribute. -/
private lemma positive_part_energy_le (hπ : ∀ x, 0 < π x) (hP : P ∈ rowStochastic ℝ S)
    (hrev : IsDetailedBalance π P) {μ : ℝ} {g : S → ℝ} (heig : P *ᵥ g = μ • g) :
    let z := fun x => max (g x) 0
    z ⬝ᵥ (laplacian Prod.fst Prod.snd (edgeWeight π P) *ᵥ z) ≤
      (1 - μ) * ∑ x, π x * z x ^ 2 := by
  intro z
  have hdir := sum_mul_sub_mulVec_eq (sum_row_of_mem_rowStochastic hP) hrev z
  have henergy : z ⬝ᵥ (laplacian Prod.fst Prod.snd (edgeWeight π P) *ᵥ z) =
      ∑ x, π x * z x * (z x - (P *ᵥ z) x) := by
    rw [dotProduct_mulVec_laplacian, Fintype.sum_prod_type, hdir]
    simp only [mul_sum]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by dsimp [edgeWeight]; ring
  rw [henergy, mul_sum]
  refine sum_le_sum fun x _ => ?_
  by_cases hx : 0 ≤ g x
  · have hmono : (P *ᵥ g) x ≤ (P *ᵥ z) x :=
      sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (le_max_left ..)
        (nonneg_of_mem_rowStochastic hP)
    rw [heig, Pi.smul_apply, smul_eq_mul] at hmono
    rw [show z x = g x from max_eq_left hx]
    calc π x * g x * (g x - (P *ᵥ z) x) ≤ π x * g x * (g x - μ * g x) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left hmono _) (mul_nonneg (hπ x).le hx)
      _ = _ := by ring
  · simp [z, max_eq_right (le_of_not_ge hx)]

end

/-- **Cheeger's inequality for reversible Markov chains, upper bound** (A. Sinclair and
M. Jerrum, *Inform. and Comput.* 82 (1989), Lemma 3.3; A. Sinclair, *Combin. Probab. Comput.* 1
(1992), Theorem 2: `λ₁ ≤ 1 - Φ²/2`). Let `P` be a stochastic matrix satisfying detailed balance
with respect to a probability vector `π > 0`. Let `Φ ≥ 0` be at most the conductance, i.e.
`Φ π(A) ≤ Q(A, Aᶜ) = ∑_{u ∈ A, v ∉ A} π(u) P(u, v)` whenever `0 < π(A) ≤ 1/2`. Then every real
eigenvalue `μ ≠ 1` of `P` satisfies `μ ≤ 1 - Φ²/2`. -/
theorem le_one_sub_sq_div_two_of_eigenvector {S : Type*} [Fintype S] [DecidableEq S]
    {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hrev : IsDetailedBalance π P) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ A : Finset S, 0 < ∑ x ∈ A, π x → ∑ x ∈ A, π x ≤ 1 / 2 →
      Φ * ∑ x ∈ A, π x ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v)
    {μ : ℝ} {f : S → ℝ} (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    μ ≤ 1 - Φ ^ 2 / 2 := by
  obtain ⟨g, hg, he, hsmall⟩ := exists_small_positive_side hπ1 hπ hf heig
  have hmean := sum_mul_eq_zero_of_eigenvector (sum_row_of_mem_rowStochastic hP) hrev he hμ
  let z := fun x => max (g x) 0
  let w := edgeWeight π P
  have hw : 0 ≤ w := fun e => div_nonneg (mul_nonneg (hπ _).le (nonneg_of_mem_rowStochastic hP))
    (by norm_num)
  have hvol (A : Finset S) : volume Prod.fst Prod.snd w A = ∑ x ∈ A, π x := by
    simp only [volume, w, chain_degree hP hrev]
  -- The positive part is nonzero because a nonzero mean-zero vector takes both signs.
  have hpos : ∃ x, 0 < g x := by
    by_contra! hn
    apply hg
    funext x
    have hall := (sum_eq_zero_iff_of_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (hπ i).le (hn i)).mp hmean
    exact (mul_eq_zero.mp (hall x (mem_univ _))).resolve_left (hπ x).ne'
  have hnorm : 0 < ∑ x, π x * z x ^ 2 := by
    obtain ⟨x, hx⟩ := hpos
    exact sum_pos' (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _))
      ⟨x, mem_univ _, mul_pos (hπ x) (sq_pos_of_pos (hx.trans_le (le_max_left ..)))⟩
  obtain ⟨t, hmin, hcut⟩ := exists_threshold_cut_le_sqrt Prod.fst Prod.snd hw z
    (by simpa [hvol, hπ1, z] using hsmall)
    (by simp [hvol, hπ1, z])
    (by simpa only [w, chain_degree hP hrev] using hnorm)
  let A := univ.filter (fun x => z x < t)
  let mass (B : Finset S) := ∑ x ∈ B, π x
  let flow (B : Finset S) := ∑ u ∈ B, ∑ v ∈ Bᶜ, π u * P u v
  simp only [← compl_eq_univ_sdiff, hvol] at hmin
  change 0 < min (mass A) (mass Aᶜ) at hmin
  have htotal : mass A + mass Aᶜ = 1 := (sum_add_sum_compl A π).trans hπ1
  have hlower : Φ * min (mass A) (mass Aᶜ) ≤ flow A := by
    rcases le_total (mass A) (mass Aᶜ) with h | h
    · rw [min_eq_left h]
      exact hΦ A (lt_min_iff.mp hmin).1 (by change mass A ≤ _; linarith)
    · rw [min_eq_right h]
      have hflip : flow Aᶜ = flow A := by
        simp only [flow, compl_compl]
        rw [sum_comm]
        exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => hrev v u
      rw [← hflip]
      exact hΦ Aᶜ (lt_min_iff.mp hmin).2 (by change mass Aᶜ ≤ _; linarith)
  let energy := z ⬝ᵥ (laplacian Prod.fst Prod.snd w *ᵥ z)
  let normSq := ∑ x, π x * z x ^ 2
  have hE : 0 ≤ energy := by
    dsimp only [energy]
    rw [dotProduct_mulVec_laplacian]
    exact sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  have hquot : Φ ≤ Real.sqrt (2 * energy / normSq) := by
    apply le_of_mul_le_mul_right _ hmin
    apply hlower.trans
    simpa only [← compl_eq_univ_sdiff, hvol, w, chain_degree hP hrev, chain_cut hrev] using hcut
  have hbound : energy ≤ (1 - μ) * normSq := positive_part_energy_le hπ hP hrev he
  have : Φ ^ 2 ≤ 2 * (1 - μ) := calc
    Φ ^ 2 ≤ 2 * energy / normSq :=
      (Real.le_sqrt hΦ0 (div_nonneg (by positivity) hnorm.le)).mp hquot
    _ ≤ 2 * (1 - μ) := (div_le_iff₀ hnorm).mpr (by linarith only [hbound])
  linarith

end MathlibExt.Probability.MulticommodityFlowWanted
