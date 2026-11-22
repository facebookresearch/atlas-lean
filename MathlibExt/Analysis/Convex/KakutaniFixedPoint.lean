/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Constructions
import MathlibExt.Analysis.Convex.BrouwerFixedPoint
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Kakutani's fixed-point theorem

Let `K` be a nonempty compact convex subset of a finite-dimensional real normed space, and let
`Φ` assign to each `x ∈ K` a nonempty convex subset of `K`, with closed graph
`{(x, y) | x ∈ K ∧ y ∈ Φ x}`. Then `x ∈ Φ x` for some `x ∈ K`. For a correspondence into a compact
set, a closed graph is the upper-hemicontinuity hypothesis of Mas-Colell–Whinston–Green,
Theorem M.I.2.

The proof applies Brouwer's theorem to continuous approximate selections built from a partition
of unity on finite `ε`-covers of `K`, and passes to the limit with Carathéodory's theorem and the
closed graph. `exists_mem_self_of_brouwer` takes Brouwer's theorem for `K` as a hypothesis;
`exists_mem_self` discharges it with `BrouwerFixedPoint.exists_fixedPoint`.

## Main results

* `exists_mem_self`: Kakutani's fixed-point theorem.

## References

* S. Kakutani, *A generalization of Brouwer's fixed point theorem*, Duke Math. J. 8 (1941),
  457–459.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Mathematical Appendix, Theorem M.I.2.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.KakutaniFixedPoint

open Finset Metric

private theorem exists_approx_fixedPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty)
    (hB : ∀ g : E → E, ContinuousOn g K → Set.MapsTo g K K → ∃ x ∈ K, g x = x)
    {Φ : E → Set E} (hΦne : ∀ x ∈ K, (Φ x).Nonempty)
    (hΦK : ∀ x ∈ K, Φ x ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset E) (b : E → E) (w : E → E → ℝ) (x : E),
      (↑s : Set E) ⊆ K ∧ (∀ j ∈ s, b j ∈ Φ j) ∧
      (∀ j ∈ s, ∀ y ∈ K, 0 ≤ w j y) ∧ (∀ y ∈ K, ∑ j ∈ s, w j y = 1) ∧
      x ∈ K ∧ x = ∑ j ∈ s, w j x • b j ∧ (∀ j ∈ s, w j x ≠ 0 → dist x j < ε) := by
  classical
  obtain ⟨t, htK, htfin, htcover⟩ := hKc.finite_cover_balls hε
  set s : Finset E := htfin.toFinset with hsdef
  have hcoe : (↑s : Set E) = t := htfin.coe_toFinset
  have hsK : (↑s : Set E) ⊆ K := by rw [hcoe]; exact htK
  have hcover : ∀ y ∈ K, ∃ a ∈ s, y ∈ ball a ε := by
    intro y hy
    have hyU := htcover hy
    simp only [Set.mem_iUnion] at hyU
    obtain ⟨a, ha_t, hya⟩ := hyU
    exact ⟨a, htfin.mem_toFinset.mpr ha_t, hya⟩
  obtain ⟨x₀, hx₀K⟩ := hKne
  obtain ⟨y₀, hy₀⟩ := hΦne x₀ hx₀K
  set b : E → E := fun j => if hj : j ∈ K then Classical.choose (hΦne j hj) else y₀ with hbdef
  have hbmem : ∀ j ∈ s, b j ∈ Φ j := by
    intro j hjs
    have hjK : j ∈ K := hsK (Finset.mem_coe.mpr hjs)
    simp only [hbdef]
    rw [dite_eq_left hjK]
    exact Classical.choose_spec (hΦne j hjK)
  have hbK : ∀ j ∈ s, b j ∈ K := by
    intro j hjs
    have hjK : j ∈ K := hsK (Finset.mem_coe.mpr hjs)
    exact hΦK j hjK (hbmem j hjs)
  set ψ : E → E → ℝ := fun j x => max 0 (ε - dist x j) with hψdef
  set S : E → ℝ := fun x => ∑ k ∈ s, ψ k x with hSdef
  have hdist_cont : ∀ j : E, Continuous (fun x : E => dist x j) :=
    fun j => Continuous.dist continuous_id continuous_const
  have hψcont : ∀ j : E, Continuous (ψ j) := by
    intro j
    have h1 : Continuous (fun x : E => max 0 (ε - dist x j)) :=
      continuous_const.max (continuous_const.sub (hdist_cont j))
    simpa [hψdef] using h1
  have hScont : Continuous S := by
    simpa [hSdef] using continuous_finsetSum s (fun k _ => hψcont k)
  have hψnn : ∀ (k : E) (x : E), 0 ≤ ψ k x := by
    intro k x
    simp only [hψdef]
    exact le_max_left 0 _
  have hSpos : ∀ x ∈ K, 0 < S x := by
    intro x hxK
    obtain ⟨a, ha_s, hxa⟩ := hcover x hxK
    have hdist : dist x a < ε := (Metric.mem_ball.mp hxa)
    have hsub : (0 : ℝ) < ε - dist x a := sub_pos.mpr hdist
    have hpos : (0 : ℝ) < ψ a x := by
      simp only [hψdef]
      exact lt_max_iff.mpr (Or.inr hsub)
    have hle : ∀ k ∈ s, (0 : ℝ) ≤ ψ k x := fun k _ => hψnn k x
    have hex : ∃ k ∈ s, (0 : ℝ) < ψ k x := ⟨a, ha_s, hpos⟩
    have hsum : (0 : ℝ) < ∑ k ∈ s, ψ k x := Finset.sum_pos' hle hex
    simpa [hSdef] using hsum
  have hSne : ∀ x ∈ K, S x ≠ 0 := fun x hx => ne_of_gt (hSpos x hx)
  set w : E → E → ℝ := fun j x => ψ j x / S x with hwdef
  have hwcont : ∀ j : E, ContinuousOn (w j) K := by
    intro j
    have h1 : ContinuousOn (ψ j) K := (hψcont j).continuousOn
    have h2 : ContinuousOn S K := hScont.continuousOn
    have h3 : ContinuousOn ((ψ j) / S) K := ContinuousOn.div h1 h2 hSne
    simpa [hwdef, Pi.div_def] using h3
  have hw_nn : ∀ j ∈ s, ∀ y ∈ K, 0 ≤ w j y := by
    intro j _ y hyK
    simp only [hwdef]
    exact div_nonneg (hψnn j y) (le_of_lt (hSpos y hyK))
  have hw_sum : ∀ y ∈ K, ∑ j ∈ s, w j y = 1 := by
    intro y hyK
    simp only [hwdef]
    rw [← Finset.sum_div]
    have hSeq : (∑ j ∈ s, ψ j y) = S y := rfl
    rw [hSeq]
    exact div_self (hSne y hyK)
  set g : E → E := fun x => ∑ j ∈ s, w j x • b j with hgdef
  have hgcont : ContinuousOn g K := by
    have h_each : ∀ j ∈ s, ContinuousOn (fun x : E => w j x • b j) K := by
      intro j _
      have h1 : ContinuousOn (w j) K := hwcont j
      have h2 : ContinuousOn (fun _ : E => b j) K := continuous_const.continuousOn
      have h3 : ContinuousOn ((w j) • (fun _ : E => b j)) K := ContinuousOn.smul h1 h2
      exact h3
    simpa [hgdef] using continuousOn_finsetSum s h_each
  have hgmaps : Set.MapsTo g K K := by
    intro x hxK
    simp only [hgdef]
    have h0 : ∀ i ∈ s, (0 : ℝ) ≤ w i x := fun i hi => hw_nn i hi x hxK
    have h1 : ∑ i ∈ s, w i x = 1 := hw_sum x hxK
    have hz : ∀ i ∈ s, b i ∈ K := fun i hi => hbK i hi
    exact hKcv.sum_mem h0 h1 hz
  obtain ⟨x, hxK, hgx⟩ := hB g hgcont hgmaps
  refine ⟨s, b, w, x, hsK, hbmem, hw_nn, hw_sum, hxK, ?_, ?_⟩
  · simp only [hgdef] at hgx
    rw [hgx]
  · intro j hjs hwx
    have hSx : S x ≠ 0 := hSne x hxK
    simp only [hwdef] at hwx
    have hψne : ψ j x ≠ 0 := by
      intro h0
      apply hwx
      rw [h0, zero_div]
    have hψnn' : (0 : ℝ) ≤ ψ j x := hψnn j x
    have hψpos : (0 : ℝ) < ψ j x := lt_of_le_of_ne hψnn' (Ne.symm hψne)
    simp only [hψdef] at hψpos
    have hsub : (0 : ℝ) < ε - dist x j := by
      rcases (lt_max_iff.mp hψpos) with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    exact sub_pos.mp hsub

private theorem exists_fixedDim_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty)
    (hB : ∀ g : E → E, ContinuousOn g K → Set.MapsTo g K K → ∃ x ∈ K, g x = x)
    {Φ : E → Set E} (hΦne : ∀ x ∈ K, (Φ x).Nonempty)
    (hΦK : ∀ x ∈ K, Φ x ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B : Fin (Module.finrank ℝ E + 1) → E)
      (Λ : Fin (Module.finrank ℝ E + 1) → ℝ) (x : E),
      x ∈ K ∧ (∀ i, A i ∈ K) ∧ (∀ i, B i ∈ K) ∧
      (∀ i, 0 ≤ Λ i) ∧ (∑ i, Λ i = 1) ∧ x = ∑ i, Λ i • B i ∧
      (∀ i, B i ∈ Φ (A i)) ∧ (∀ i, dist x (A i) < ε) := by
  classical
  obtain ⟨s, b, w, x, hsK, hbmem, hw_nn, hw_sum, hxK, hxx, hdist⟩ :=
    exists_approx_fixedPoint hKc hKcv hKne hB hΦne hΦK hε
  -- support: indices with nonzero weight
  set supp : Finset E := s.filter (fun j => w j x ≠ 0) with hsuppdef
  have hsupp_sub : supp ⊆ s := Finset.filter_subset _ s
  have hsupp_mem : ∀ j ∈ supp, j ∈ s := fun j hj => hsupp_sub hj
  have hw_supp_ne : ∀ j ∈ supp, w j x ≠ 0 := by
    intro j hj
    simp only [hsuppdef, Finset.mem_filter] at hj
    exact hj.2
  have hx_eq_supp : x = ∑ j ∈ supp, w j x • b j := by
    have hsub : ∑ j ∈ supp, w j x • b j = ∑ j ∈ s, w j x • b j := by
      apply Finset.sum_subset hsupp_sub
      intro j hjs hjnsupp
      simp only [hsuppdef, Finset.mem_filter] at hjnsupp
      have hw0 : w j x = 0 := by
        by_contra hne
        exact hjnsupp ⟨hjs, hne⟩
      rw [hw0, zero_smul]
    rw [hsub, ← hxx]
  have hw_supp_sum : ∑ j ∈ supp, w j x = 1 := by
    have hsub : ∑ j ∈ supp, w j x = ∑ j ∈ s, w j x := by
      apply Finset.sum_subset hsupp_sub
      intro j hjs hjnsupp
      simp only [hsuppdef, Finset.mem_filter] at hjnsupp
      by_contra hne
      exact hjnsupp ⟨hjs, hne⟩
    rw [hsub]
    exact hw_sum x hxK
  -- x in convexHull of b-image of support
  set Sset : Set E := b '' ↑supp with hSsetdef
  have hb_mem_supp : ∀ j ∈ supp, b j ∈ Sset := by
    intro j hj
    simp only [hSsetdef, Set.mem_image]
    exact ⟨j, Finset.mem_coe.mpr hj, rfl⟩
  have hw_supp_nn : ∀ j ∈ supp, (0 : ℝ) ≤ w j x := by
    intro j hj
    exact hw_nn j (hsupp_mem j hj) x hxK
  have hw_supp_pos : (0 : ℝ) < ∑ j ∈ supp, w j x := by
    rw [hw_supp_sum]
    exact zero_lt_one
  have hcm_mem : supp.centerMass (fun j => w j x) b ∈ convexHull ℝ Sset :=
    Finset.centerMass_mem_convexHull supp hw_supp_nn hw_supp_pos hb_mem_supp
  have hcm_eq : supp.centerMass (fun j => w j x) b = ∑ j ∈ supp, w j x • b j :=
    Finset.centerMass_eq_of_sum_1 supp b hw_supp_sum
  have hx_mem : x ∈ convexHull ℝ Sset := by
    rw [hx_eq_supp, ← hcm_eq]
    exact hcm_mem
  obtain ⟨ι, _hfin, z, w2, hrange, hind, hpos, hsum1, hsumx⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_mem
  -- bound card ι ≤ finrank + 1
  have hcard_le : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
    have h1 : Fintype.card ι ≤
        Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z)) + 1 :=
      hind.card_le_finrank_succ
    have h2 : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ E :=
      Submodule.finrank_le _
    exact le_trans h1 (Nat.add_le_add_right h2 1)
  set N : ℕ := Module.finrank ℝ E + 1 with hNdef
  have hcardN : Fintype.card ι ≤ Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    simpa [hNdef] using hcard_le
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardN
  -- for each j, z j = b (a j) for some a j in support
  have hex : ∀ j : ι, ∃ a ∈ supp, z j = b a := by
    intro j
    have hjmem : z j ∈ Sset := hrange (Set.mem_range_self j)
    simp only [hSsetdef, Set.mem_image] at hjmem
    obtain ⟨a, ha_supp, hab⟩ := hjmem
    have ha_fin : a ∈ supp := Finset.mem_coe.mp ha_supp
    exact ⟨a, ha_fin, hab.symm⟩
  choose a ha using hex
  -- ha j : a j ∈ supp ∧ z j = b (a j)
  have ha_supp : ∀ j, a j ∈ supp := fun j => (ha j).1
  have hz_eq : ∀ j, z j = b (a j) := fun j => (ha j).2
  have ha_s : ∀ j, a j ∈ s := fun j => hsupp_mem _ (ha_supp j)
  have haK : ∀ j, a j ∈ K := fun j => hsK (Finset.mem_coe.mpr (ha_s j))
  have hw_a_ne : ∀ j, w (a j) x ≠ 0 := fun j => hw_supp_ne _ (ha_supp j)
  have hdist_a : ∀ j, dist x (a j) < ε := fun j => hdist _ (ha_s j) (hw_a_ne j)
  have hb_a_mem : ∀ j, b (a j) ∈ Φ (a j) := fun j => hbmem _ (ha_s j)
  have hz_mem : ∀ j, z j ∈ Φ (a j) := by
    intro j
    rw [hz_eq j]
    exact hb_a_mem j
  have hzK : ∀ j, z j ∈ K := by
    intro j
    rw [hz_eq j]
    exact hΦK _ (haK j) (hb_a_mem j)
  -- dummy point in Φ x
  obtain ⟨yx, hyx⟩ := hΦne x hxK
  have hyxK : yx ∈ K := hΦK x hxK hyx
  -- padded functions via Function.extend
  set A : Fin N → E := Function.extend e a (fun _ => x) with hAdef
  set B : Fin N → E := Function.extend e z (fun _ => yx) with hBdef
  set Λ : Fin N → ℝ := Function.extend e w2 (fun _ => 0) with hΛdef
  have he_inj : Function.Injective e := e.injective
  have hA_emb : ∀ j : ι, A (e j) = a j := fun j => he_inj.extend_apply a _ j
  have hB_emb : ∀ j : ι, B (e j) = z j := fun j => he_inj.extend_apply z _ j
  have hΛ_emb : ∀ j : ι, Λ (e j) = w2 j := fun j => he_inj.extend_apply w2 _ j
  have hA_dummy : ∀ i : Fin N, (¬∃ j : ι, e j = i) → A i = x := by
    intro i hi
    simpa [hAdef] using Function.extend_apply' a (fun _ => x) i hi
  have hB_dummy : ∀ i : Fin N, (¬∃ j : ι, e j = i) → B i = yx := by
    intro i hi
    simpa [hBdef] using Function.extend_apply' z (fun _ => yx) i hi
  have hΛ_dummy : ∀ i : Fin N, (¬∃ j : ι, e j = i) → Λ i = 0 := by
    intro i hi
    simpa [hΛdef] using Function.extend_apply' w2 (fun _ => 0) i hi
  have hAK : ∀ i, A i ∈ K := by
    intro i
    by_cases h : ∃ j : ι, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hA_emb j]
      exact haK j
    · rw [hA_dummy i h]
      exact hxK
  have hBK : ∀ i, B i ∈ K := by
    intro i
    by_cases h : ∃ j : ι, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hB_emb j]
      exact hzK j
    · rw [hB_dummy i h]
      exact hyxK
  have hBmem : ∀ i, B i ∈ Φ (A i) := by
    intro i
    by_cases h : ∃ j : ι, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hA_emb j, hB_emb j]
      exact hz_mem j
    · rw [hA_dummy i h, hB_dummy i h]
      exact hyx
  have hdistA : ∀ i, dist x (A i) < ε := by
    intro i
    by_cases h : ∃ j : ι, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hA_emb j]
      exact hdist_a j
    · rw [hA_dummy i h, dist_self]
      exact hε
  have hΛnn : ∀ i, 0 ≤ Λ i := by
    intro i
    by_cases h : ∃ j : ι, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hΛ_emb j]
      exact le_of_lt (hpos j)
    · rw [hΛ_dummy i h]
  -- sums via image
  set s_img : Finset (Fin N) := Finset.univ.image e with hs_imgdef
  have he_injOn : Set.InjOn e ↑(Finset.univ : Finset ι) := he_inj.injOn
  have hsum_img : ∑ i ∈ s_img, Λ i = ∑ j ∈ Finset.univ, Λ (e j) :=
    Finset.sum_image he_injOn
  have hsum_emb_w2 : ∑ j ∈ Finset.univ, Λ (e j) = ∑ j ∈ Finset.univ, w2 j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hΛ_emb j]
  have hsum_w2_univ : ∑ j ∈ Finset.univ, w2 j = 1 := hsum1
  have hsum_img_eq1 : ∑ i ∈ s_img, Λ i = 1 := by
    rw [hsum_img, hsum_emb_w2, hsum_w2_univ]
  have hΛ_zero_out : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ s_img → Λ i = 0 := by
    intro i _ hi
    have hne : ¬∃ j : ι, e j = i := by
      intro hex
      obtain ⟨j, hj⟩ := hex
      apply hi
      simp only [hs_imgdef, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, hj⟩
    exact hΛ_dummy i hne
  have hsum_univ_eq_img : ∑ i ∈ Finset.univ, Λ i = ∑ i ∈ s_img, Λ i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s_img)
    intro i _ hi
    exact hΛ_zero_out i (Finset.mem_univ i) hi
  have hΛ_sum : (∑ i, Λ i) = 1 := by
    have h1 : (∑ i, Λ i) = ∑ i ∈ Finset.univ, Λ i := rfl
    rw [h1, hsum_univ_eq_img, hsum_img_eq1]
  have hsum_img_smul : ∑ i ∈ s_img, Λ i • B i = ∑ j ∈ Finset.univ, Λ (e j) • B (e j) :=
    Finset.sum_image he_injOn
  have hsum_emb_wz : ∑ j ∈ Finset.univ, Λ (e j) • B (e j) =
      ∑ j ∈ Finset.univ, w2 j • z j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hΛ_emb j, hB_emb j]
  have hsum_wz_univ : ∑ j ∈ Finset.univ, w2 j • z j = x := hsumx
  have hsum_img_eqx : ∑ i ∈ s_img, Λ i • B i = x := by
    rw [hsum_img_smul, hsum_emb_wz, hsum_wz_univ]
  have hsmul_zero_out : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ s_img →
      Λ i • B i = 0 := by
    intro i _ hi
    have hΛ0 : Λ i = 0 := hΛ_zero_out i (Finset.mem_univ i) hi
    rw [hΛ0, zero_smul]
  have hsum_univ_eq_img_smul : ∑ i ∈ Finset.univ, Λ i • B i =
      ∑ i ∈ s_img, Λ i • B i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s_img)
    intro i _ hi
    exact hsmul_zero_out i (Finset.mem_univ i) hi
  have hx_eq_sum : x = ∑ i, Λ i • B i := by
    have h1 : (∑ i, Λ i • B i) = ∑ i ∈ Finset.univ, Λ i • B i := rfl
    rw [h1, hsum_univ_eq_img_smul, hsum_img_eqx]
  exact ⟨A, B, Λ, x, hxK, hAK, hBK, hΛnn, hΛ_sum, hx_eq_sum, hBmem, hdistA⟩

/-- Kakutani's fixed-point theorem, derived from Brouwer's theorem on the same domain: let `K` be
a nonempty compact convex subset of a finite-dimensional real normed space, and suppose every
continuous self-map of `K` has a fixed point (Brouwer). Then every correspondence `Φ` from `K`
to itself with nonempty convex values and closed graph has a fixed point `x ∈ Φ x`. -/
theorem exists_mem_self_of_brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty)
    (hB : ∀ g : E → E, ContinuousOn g K → Set.MapsTo g K K → ∃ x ∈ K, g x = x)
    {Φ : E → Set E} (hΦne : ∀ x ∈ K, (Φ x).Nonempty) (hΦcv : ∀ x ∈ K, Convex ℝ (Φ x))
    (hΦK : ∀ x ∈ K, Φ x ⊆ K) (hΦgraph : IsClosed {q : E × E | q.1 ∈ K ∧ q.2 ∈ Φ q.1}) :
    ∃ x ∈ K, x ∈ Φ x := by
  classical
  -- sequences with ε_n = 1/(n+1)
  have hεn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    positivity
  have hall : ∀ n : ℕ, ∃ (A B : Fin (Module.finrank ℝ E + 1) → E)
      (Λ : Fin (Module.finrank ℝ E + 1) → ℝ) (x : E),
      x ∈ K ∧ (∀ i, A i ∈ K) ∧ (∀ i, B i ∈ K) ∧
      (∀ i, 0 ≤ Λ i) ∧ (∑ i, Λ i = 1) ∧ x = ∑ i, Λ i • B i ∧
      (∀ i, B i ∈ Φ (A i)) ∧ (∀ i, dist x (A i) < 1 / ((n : ℝ) + 1)) := by
    intro n
    exact exists_fixedDim_approx hKc hKcv hKne hB hΦne hΦK (hεn n)
  choose A B Λ x hallP using hall
  have hxK : ∀ n, x n ∈ K := fun n => (hallP n).1
  have hAK : ∀ n i, A n i ∈ K := fun n i => (hallP n).2.1 i
  have hBK : ∀ n i, B n i ∈ K := fun n i => (hallP n).2.2.1 i
  have hΛnn : ∀ n i, 0 ≤ Λ n i := fun n i => (hallP n).2.2.2.1 i
  have hΛsum : ∀ n, (∑ i, Λ n i) = 1 := fun n => (hallP n).2.2.2.2.1
  have hxeq : ∀ n, x n = ∑ i, Λ n i • B n i := fun n => (hallP n).2.2.2.2.2.1
  have hBmem : ∀ n i, B n i ∈ Φ (A n i) := fun n i => (hallP n).2.2.2.2.2.2.1 i
  have hdist : ∀ n i, dist (x n) (A n i) < 1 / ((n : ℝ) + 1) :=
    fun n i => (hallP n).2.2.2.2.2.2.2 i
  -- compact product extraction
  set piK : Set (Fin (Module.finrank ℝ E + 1) → E) := {f | ∀ i, f i ∈ K} with hpiKdef
  have hpiKc : IsCompact piK := isCompact_pi_infinite (fun _ => hKc)
  have hSx_c : IsCompact (stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))) :=
    isCompact_stdSimplex ℝ _
  set C : Set (E × ((Fin (Module.finrank ℝ E + 1) → E) ×
      ((Fin (Module.finrank ℝ E + 1) → E) × (Fin (Module.finrank ℝ E + 1) → ℝ)))) :=
    K ×ˢ (piK ×ˢ (piK ×ˢ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)))) with hCdef
  have hCc : IsCompact C := hKc.prod (hpiKc.prod (hpiKc.prod hSx_c))
  set S : ℕ → (E × ((Fin (Module.finrank ℝ E + 1) → E) ×
      ((Fin (Module.finrank ℝ E + 1) → E) × (Fin (Module.finrank ℝ E + 1) → ℝ)))) :=
    fun n => (x n, (A n, (B n, Λ n))) with hSdef
  have hA_mem : ∀ n, A n ∈ piK := fun n i => hAK n i
  have hB_mem : ∀ n, B n ∈ piK := fun n i => hBK n i
  have hΛ_mem : ∀ n, Λ n ∈ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)) := by
    intro n
    simp only [stdSimplex]
    exact ⟨hΛnn n, hΛsum n⟩
  have hS_mem : ∀ n, S n ∈ C := by
    intro n
    simp only [hSdef, hCdef, Set.mem_prod]
    exact ⟨hxK n, hA_mem n, hB_mem n, hΛ_mem n⟩
  obtain ⟨a, haC, φ, hφmono, hφlim⟩ := hCc.tendsto_subseq hS_mem
  simp only [hCdef, Set.mem_prod] at haC
  obtain ⟨hx_star, hA_star, hB_star, hΛ_star⟩ := haC
  -- projections: convergence of components
  have hx_lim : Filter.Tendsto (fun n => x (φ n)) Filter.atTop (nhds a.1) :=
    (continuous_fst.tendsto a).comp hφlim
  have hA_lim : Filter.Tendsto (fun n => A (φ n)) Filter.atTop (nhds a.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto a).comp hφlim
  have hB_lim : Filter.Tendsto (fun n => B (φ n)) Filter.atTop (nhds a.2.2.1) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto a).comp hφlim
  have hΛ_lim : Filter.Tendsto (fun n => Λ (φ n)) Filter.atTop (nhds a.2.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto a).comp hφlim
  -- pointwise for each i
  have hA_pt : ∀ i, Filter.Tendsto (fun n => A (φ n) i) Filter.atTop (nhds (a.2.1 i)) :=
    fun i => ((continuous_apply i).tendsto _).comp hA_lim
  have hB_pt : ∀ i, Filter.Tendsto (fun n => B (φ n) i) Filter.atTop (nhds (a.2.2.1 i)) :=
    fun i => ((continuous_apply i).tendsto _).comp hB_lim
  have hΛ_pt : ∀ i, Filter.Tendsto (fun n => Λ (φ n) i) Filter.atTop (nhds (a.2.2.2 i)) :=
    fun i => ((continuous_apply i).tendsto _).comp hΛ_lim
  -- x* = sum via continuity of sum
  have hterm_lim : ∀ i, Filter.Tendsto (fun n => Λ (φ n) i • B (φ n) i) Filter.atTop
      (nhds (a.2.2.2 i • a.2.2.1 i)) :=
    fun i => (hΛ_pt i).smul (hB_pt i)
  have hsum_lim : Filter.Tendsto (fun n => ∑ i, Λ (φ n) i • B (φ n) i) Filter.atTop
      (nhds (∑ i, a.2.2.2 i • a.2.2.1 i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hterm_lim i)
  have hx_lim2 : Filter.Tendsto (fun n => x (φ n)) Filter.atTop
      (nhds (∑ i, a.2.2.2 i • a.2.2.1 i)) := by
    have heq : (fun n => x (φ n)) = (fun n => ∑ i, Λ (φ n) i • B (φ n) i) :=
      funext fun n => hxeq (φ n)
    rw [heq]
    exact hsum_lim
  have hx_eq : a.1 = ∑ i, a.2.2.2 i • a.2.2.1 i := tendsto_nhds_unique hx_lim hx_lim2
  -- A* = x* for all i via dist → 0
  have hε_lim : Filter.Tendsto (fun n : ℕ => 1 / (((φ n : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop
  have hA_eq : ∀ i, a.2.1 i = a.1 := by
    intro i
    have hdist_lim : Filter.Tendsto (fun n => dist (x (φ n)) (A (φ n) i)) Filter.atTop
        (nhds (dist a.1 (a.2.1 i))) :=
      hx_lim.dist (hA_pt i)
    have hdist_zero : Filter.Tendsto (fun n => dist (x (φ n)) (A (φ n) i)) Filter.atTop
        (nhds 0) := by
      apply squeeze_zero (fun _ => dist_nonneg) _ hε_lim
      intro n
      exact le_of_lt (hdist (φ n) i)
    have hdist_eq : dist a.1 (a.2.1 i) = 0 := tendsto_nhds_unique hdist_lim hdist_zero
    have heq : a.1 = a.2.1 i := dist_eq_zero.mp hdist_eq
    exact heq.symm
  -- B* ∈ Φ(x*) via closed graph
  have hB_star_mem : ∀ i, a.2.2.1 i ∈ Φ a.1 := by
    intro i
    have hprod_lim : Filter.Tendsto (fun n => (A (φ n) i, B (φ n) i)) Filter.atTop
        (nhds (a.2.1 i, a.2.2.1 i)) :=
      (hA_pt i).prodMk_nhds (hB_pt i)
    rw [hA_eq i] at hprod_lim
    -- hprod_lim : Tendsto ... (nhds (a.1, B* i))
    have hmem_each : ∀ n, (A (φ n) i, B (φ n) i) ∈ {q : E × E | q.1 ∈ K ∧ q.2 ∈ Φ q.1} := by
      intro n
      simp only [Set.mem_ofPred_eq]
      exact ⟨hAK (φ n) i, hBmem (φ n) i⟩
    have hlim_mem : (a.1, a.2.2.1 i) ∈ {q : E × E | q.1 ∈ K ∧ q.2 ∈ Φ q.1} :=
      hΦgraph.mem_of_tendsto hprod_lim (Filter.Eventually.of_forall hmem_each)
    simp only [Set.mem_ofPred_eq] at hlim_mem
    exact hlim_mem.2
  -- x* ∈ Φ(x*) via convexity
  have hΛ_star_nn : ∀ i, 0 ≤ a.2.2.2 i := by
    have hmem : a.2.2.2 ∈ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)) := hΛ_star
    simp only [stdSimplex, Set.mem_ofPred_eq] at hmem
    exact hmem.1
  have hΛ_star_sum : (∑ i, a.2.2.2 i) = 1 := by
    have hmem : a.2.2.2 ∈ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)) := hΛ_star
    simp only [stdSimplex, Set.mem_ofPred_eq] at hmem
    exact hmem.2
  have hconv : Convex ℝ (Φ a.1) := hΦcv a.1 hx_star
  have hsum_mem : (∑ i, a.2.2.2 i • a.2.2.1 i) ∈ Φ a.1 := by
    have h0 : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ a.2.2.2 i := fun i _ => hΛ_star_nn i
    have h1 : ∑ i ∈ Finset.univ, a.2.2.2 i = 1 := hΛ_star_sum
    have hz : ∀ i ∈ Finset.univ, a.2.2.1 i ∈ Φ a.1 := fun i _ => hB_star_mem i
    have hmem : ∑ i ∈ Finset.univ, a.2.2.2 i • a.2.2.1 i ∈ Φ a.1 :=
      hconv.sum_mem h0 h1 hz
    have heq : (∑ i, a.2.2.2 i • a.2.2.1 i) = ∑ i ∈ Finset.univ, a.2.2.2 i • a.2.2.1 i := rfl
    rw [heq]
    exact hmem
  rw [← hx_eq] at hsum_mem
  exact ⟨a.1, hx_star, hsum_mem⟩

end MathlibExt.Analysis.Convex.KakutaniFixedPoint

namespace MathlibExt.Analysis.Convex.KakutaniFixedPoint

/-- Kakutani's fixed-point theorem: every upper hemicontinuous correspondence from a nonempty
compact convex set to itself with nonempty convex values has a fixed point. -/
theorem exists_mem_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty)
    {Φ : E → Set E} (hΦne : ∀ x ∈ K, (Φ x).Nonempty) (hΦcv : ∀ x ∈ K, Convex ℝ (Φ x))
    (hΦK : ∀ x ∈ K, Φ x ⊆ K) (hΦgraph : IsClosed {q : E × E | q.1 ∈ K ∧ q.2 ∈ Φ q.1}) :
    ∃ x ∈ K, x ∈ Φ x :=
  exists_mem_self_of_brouwer hKc hKcv hKne
    (fun _ hg hgm =>
      MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint hKc hKcv hKne hg hgm)
    hΦne hΦcv hΦK hΦgraph

end MathlibExt.Analysis.Convex.KakutaniFixedPoint
