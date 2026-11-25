/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.OrderClosed

/-!
# Theta of strong powers and Lovász's bound on the Shannon capacity

Tensor products of orthogonal labelings are orthogonal labelings of strong products, and costs
multiply. Hence `α(G^{⊠k}) ≤ ϑ(G)^k` for the `k`-fold strong power, and the Shannon capacity
`Θ(G) = lim α(G^{⊠k})^{1/k}` is at most `ϑ(G)`. We state these for any graph `H` on words
`Fin k → V` in which distinct non-adjacent words differ at some position in distinct
non-adjacent vertices of `G`; the strong power of `G` is such a graph, and so is any graph with
more edges.

Sources: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979),
1-7; D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), §20 (strong products, eqs. (20.6)-(20.8)).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

open scoped RealInnerProductSpace
open Finset

variable {V : Type*}

/-- **Tensor product of `k` vectors.** For `f : Fin k → ℝ^d`, the vector of `ℝ^(Fin k → Fin d)`
whose coordinate at `j` is `∏ᵢ fᵢ(jᵢ)`, i.e. `f₀ ⊗ ⋯ ⊗ f_{k-1}` (Knuth, *The Sandwich Theorem*,
1994, eq. (20.6), the Hadamard product, iterated `k` times). -/
noncomputable def tensorVec {k d : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin k → Fin d) :=
  WithLp.toLp 2 (fun j => ∏ i, f i (j i))

/-- **Inner products of tensor products factor.**
`⟪f₀ ⊗ ⋯ ⊗ f_{k-1}, g₀ ⊗ ⋯ ⊗ g_{k-1}⟫ = ∏ᵢ ⟪fᵢ, gᵢ⟫`
(Knuth, *The Sandwich Theorem*, 1994, eq. (20.7)). -/
theorem inner_tensorVec {k d : ℕ} (f g : Fin k → EuclideanSpace ℝ (Fin d)) :
    ⟪tensorVec f, tensorVec g⟫ = ∏ i, ⟪f i, g i⟫ := by
  simp only [tensorVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← sum_prod_piFinset, Fintype.piFinset_univ]

/-- **Feasible values multiply along strong powers.** Let `H` be a graph on words `Fin k → V` in
which two distinct non-adjacent words differ, at some position, in two distinct non-adjacent
vertices of `G` (true for the strong power `G^{⊠k}`). If `t` is a feasible value of the theta
program for `G`, then `t^k` is one for `H`: tensor products of an orthogonal labeling of `G` form
one of `H`, and costs multiply (Knuth, *The Sandwich Theorem*, 1994, §20, eqs. (20.6)-(20.8)). -/
theorem pow_mem_thetaFeasible {G : SimpleGraph V} {k : ℕ} {H : SimpleGraph (Fin k → V)}
    (hH : ∀ x y, x ≠ y → ¬ H.Adj x y → ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i)) {t : ℝ}
    (ht : t ∈ thetaFeasible G) : t ^ k ∈ thetaFeasible H := by
  obtain ⟨ht0, d, a, c, hc, ha, hcost⟩ := ht
  have hcost_tensorVec : ∀ x : Fin k → V,
      cost (tensorVec fun _ => c) (tensorVec fun i => a (x i)) = ∏ i, cost c (a (x i)) := by
    intro x
    simp only [cost, ← real_inner_self_eq_norm_sq, inner_tensorVec]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply mem_thetaFeasible_of_finiteDimensional (pow_nonneg ht0 k)
    (fun x => tensorVec fun i => a (x i))
    (tensorVec fun _ => c)
  · intro h0
    have h := congrArg (fun z => ⟪z, z⟫) h0
    simp only [inner_tensorVec, inner_zero_left] at h
    have : ∏ _i : Fin k, ⟪c, c⟫ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => by
        rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
    exact this h
  · intro x y hxy hadj
    obtain ⟨i, hi, hni⟩ := hH x y hxy hadj
    rw [inner_tensorVec]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ha hi hni)
  · intro x
    rw [hcost_tensorVec]
    calc (1 : ℝ) = ∏ _i : Fin k, (1 : ℝ) := by simp
      _ ≤ ∏ i, t * cost c (a (x i)) :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hcost (x i))
      _ = t ^ k * ∏ i, cost c (a (x i)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Independence numbers of strong powers are at most `ϑ^k`.** For a finite graph `G` and a graph
`H` on words `Fin k → V` as in `pow_mem_thetaFeasible` (for instance the strong power `G^{⊠k}`),
`α(H) ≤ ϑ(G)^k` (Lovász 1979; Knuth, *The Sandwich Theorem*, 1994, §20). -/
theorem indepNum_le_lovaszTheta_pow [Finite V] (G : SimpleGraph V) {k : ℕ}
    {H : SimpleGraph (Fin k → V)}
    (hH : ∀ x y, x ≠ y → ¬ H.Adj x y → ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i)) :
    (H.indepNum : ℝ) ≤ lovaszTheta G ^ k := by
  have hne : (thetaFeasible G).Nonempty :=
    ⟨_, natCast_mem_thetaFeasible_of_colorable (Gᶜ.colorable_chromaticNumber_of_fintype)⟩
  have hbound : ∀ t ∈ thetaFeasible G, (H.indepNum : ℝ) ≤ t ^ k := fun t ht =>
    indepNum_le_of_mem_thetaFeasible (pow_mem_thetaFeasible hH ht)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    obtain ⟨t, ht⟩ := hne
    simpa using hbound t ht
  have hα : (0 : ℝ) ≤ H.indepNum := Nat.cast_nonneg _
  have hk0 : k ≠ 0 := hk.ne'
  have hroot : (H.indepNum : ℝ) ^ ((k : ℝ)⁻¹) ≤ lovaszTheta G := by
    apply le_csInf hne
    intro t ht
    have := Real.rpow_le_rpow hα (hbound t ht) (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast ht.1 hk0] at this
  have h := pow_le_pow_left₀ (Real.rpow_nonneg hα _) hroot k
  rwa [Real.rpow_inv_natCast_pow hα hk0] at h

/-- **Lovász's bound on the Shannon capacity.** For a finite graph `G` and graphs `H k` on words
`Fin (k + 1) → V` as in `pow_mem_thetaFeasible` (for instance the strong powers), if
`α(H k)^(1/(k+1))` converges to `θ`, then `θ ≤ ϑ(G)`. With `H k` the strong powers, `θ` is the
Shannon capacity `Θ(G)`, and this is Lovász's theorem `Θ(G) ≤ ϑ(G)` (L. Lovász, "On the Shannon
capacity of a graph", IEEE Trans. Inform. Theory 25 (1979), 1-7). -/
theorem le_lovaszTheta_of_tendsto [Finite V] (G : SimpleGraph V)
    (H : ∀ k : ℕ, SimpleGraph (Fin (k + 1) → V))
    (hH : ∀ k x y, x ≠ y → ¬ (H k).Adj x y → ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i)) {θ : ℝ}
    (hθ : Filter.Tendsto (fun k : ℕ => ((H k).indepNum : ℝ) ^ (((k : ℝ) + 1)⁻¹))
      Filter.atTop (nhds θ)) :
    θ ≤ lovaszTheta G := by
  apply le_of_tendsto' hθ
  intro k
  have h := indepNum_le_lovaszTheta_pow G (hH k)
  have hα : (0 : ℝ) ≤ (H k).indepNum := Nat.cast_nonneg _
  have := Real.rpow_le_rpow hα h (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹)
  have e : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  rw [← e, Real.pow_rpow_inv_natCast (lovaszTheta_nonneg G) (Nat.succ_ne_zero k)] at this
  rwa [← e]

end MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
