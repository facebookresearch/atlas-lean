/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Combination
import Mathlib.Order.Filter.AtTopBot.Archimedean

@[expose] public section

open Set

namespace MathlibExt.Analysis.FunctionalAnalysis.MarkovKakutani

private theorem affSubAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ᴬ[ℝ] E) (x y : E) :
    T x - T y = T.toAffineMap.linear (x - y) := by
  have h := AffineMap.map_vadd T.toAffineMap y (x - y)
  simp only [vadd_eq_add, sub_add_cancel] at h
  have h2 : T.toAffineMap x - T.toAffineMap y = T.toAffineMap.linear (x - y) := by
    rw [h]
    exact add_sub_cancel_right _ _
  exact h2

private theorem convexFixAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ᴬ[ℝ] E) : Convex ℝ {x : E | T x = x} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at hx hy ⊢
  have hTz : ∀ z : E, T z = T 0 + T.toAffineMap.linear z := by
    intro z
    have h := affSubAux T z 0
    rw [sub_zero] at h
    rw [← h, add_sub_cancel]
  have hLx : T.toAffineMap.linear x = x - T 0 := by
    have h := affSubAux T x 0
    rw [sub_zero, hx] at h
    exact h.symm
  have hLy : T.toAffineMap.linear y = y - T 0 := by
    have h := affSubAux T y 0
    rw [sub_zero, hy] at h
    exact h.symm
  have hT0 : T 0 = a • T 0 + b • T 0 := by
    rw [← add_smul, hab, one_smul]
  rw [hTz, map_add, map_smul, map_smul, hLx, hLy, smul_sub, smul_sub]
  nth_rewrite 1 [hT0]
  abel

private theorem existsFixAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K)
    (T : E →ᴬ[ℝ] E) (hT : MapsTo T K K) :
    ∃ x ∈ K, T x = x := by
  obtain ⟨x0, hx0⟩ := hK_nonempty
  have hmem : ∀ n : ℕ, ∀ y ∈ K, (⇑T)^[n] y ∈ K := by
    intro n
    induction n with
    | zero => intro y hy; rw [Function.iterate_zero_apply]; exact hy
    | succ n ih =>
      intro y hy
      have e : (⇑T)^[n + 1] y = (⇑T)^[n] (T y) := Function.iterate_succ_apply _ _ _
      rw [e]
      exact ih _ (hT hy)
  obtain ⟨B, hB⟩ := hK_compact.isBounded.exists_norm_le
  have hsum1 : ∀ m : ℕ, m ≠ 0 → ∑ _k ∈ Finset.range m, (m : ℝ)⁻¹ = 1 := by
    intro m hm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm)]
  have havg : ∀ m : ℕ, m ≠ 0 → (m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0 ∈ K := by
    intro m hm
    rw [Finset.smul_sum]
    refine hK_convex.sum_mem (fun k _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (hsum1 m hm) ?_
    intro k _
    exact hmem k x0 hx0
  have hTz : ∀ z : E, T z = T 0 + T.toAffineMap.linear z := by
    intro z
    have h := affSubAux T z 0
    rw [sub_zero] at h
    rw [← h, add_sub_cancel]
  have hLz : ∀ z : E, T.toAffineMap.linear z = T z - T 0 := by
    intro z
    have h := affSubAux T z 0
    rw [sub_zero] at h
    exact h.symm
  have hshift : ∀ k : ℕ, T ((⇑T)^[k] x0) = (⇑T)^[k + 1] x0 :=
    fun k => (Function.iterate_succ_apply' ⇑T k x0).symm
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, T ((⇑T)^[k] x0)
      = (∑ k ∈ Finset.range m, (⇑T)^[k] x0) + ((⇑T)^[m] x0 - x0) := by
    intro m
    have e2 : (∑ k ∈ Finset.range m, (⇑T)^[k] x0) + (⇑T)^[m] x0
        = (∑ k ∈ Finset.range m, (⇑T)^[k + 1] x0) + x0 := by
      have r1 := Finset.sum_range_succ' (fun k => (⇑T)^[k] x0) m
      have r2 := Finset.sum_range_succ (fun k => (⇑T)^[k] x0) m
      simp only [Function.iterate_zero_apply] at r1
      exact r2.symm.trans r1
    have hS : (∑ k ∈ Finset.range m, (⇑T)^[k + 1] x0)
        = (∑ k ∈ Finset.range m, (⇑T)^[k] x0) + ((⇑T)^[m] x0 - x0) := by
      have hS' : (∑ k ∈ Finset.range m, (⇑T)^[k + 1] x0)
          = ((∑ k ∈ Finset.range m, (⇑T)^[k] x0) + (⇑T)^[m] x0) - x0 := by
        rw [e2, add_sub_cancel_right]
      rw [hS']
      abel
    simp only [hshift]
    exact hS
  have key : ∀ m : ℕ, m ≠ 0 → T ((m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0)
      = ((m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0)
        + (m : ℝ)⁻¹ • ((⇑T)^[m] x0 - x0) := by
    intro m hm
    have hLsum : T.toAffineMap.linear (∑ k ∈ Finset.range m, (⇑T)^[k] x0)
        = (∑ k ∈ Finset.range m, T ((⇑T)^[k] x0)) - m • T 0 := by
      rw [map_sum]
      simp only [hLz]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hcast : (m : ℕ) • T 0 = (m : ℝ) • T 0 := (Nat.cast_smul_eq_nsmul ℝ m (T 0)).symm
    have hcancel : (m : ℝ)⁻¹ • ((m : ℕ) • T 0) = T 0 := by
      rw [hcast, ← mul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul]
    calc T ((m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0)
        = T 0 + T.toAffineMap.linear ((m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0) := hTz _
      _ = T 0 + (m : ℝ)⁻¹ • T.toAffineMap.linear (∑ k ∈ Finset.range m, (⇑T)^[k] x0) := by
          rw [map_smul]
      _ = T 0 + (m : ℝ)⁻¹ • ((∑ k ∈ Finset.range m, T ((⇑T)^[k] x0)) - m • T 0) := by
          rw [hLsum]
      _ = T 0 + ((m : ℝ)⁻¹ • (∑ k ∈ Finset.range m, T ((⇑T)^[k] x0)) - T 0) := by
          rw [smul_sub, hcancel]
      _ = (m : ℝ)⁻¹ • (∑ k ∈ Finset.range m, T ((⇑T)^[k] x0)) := by
          rw [add_sub_cancel]
      _ = ((m : ℝ)⁻¹ • ∑ k ∈ Finset.range m, (⇑T)^[k] x0)
          + (m : ℝ)⁻¹ • ((⇑T)^[m] x0 - x0) := by
          rw [hsum m, smul_add]
  set a : ℕ → E := fun n => ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), (⇑T)^[k] x0 with ha
  have hamem : ∀ n, a n ∈ K := fun n => by
    simpa [ha] using havg (n + 1) (Nat.succ_ne_zero n)
  obtain ⟨z, hzK, φ, hφmono, hφlim⟩ := hK_compact.tendsto_subseq hamem
  have hTlim : Filter.Tendsto (fun j => T (a (φ j))) Filter.atTop (nhds (T z)) :=
    (T.cont.tendsto z).comp hφlim
  have hphi : Filter.Tendsto (fun j => ((φ j + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun j => φ j + 1) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun j => ?_) strictMono_id.tendsto_atTop
      exact (hφmono.le_apply).trans (Nat.le_succ _)
    exact tendsto_natCast_atTop_atTop.comp h1
  have hinv : Filter.Tendsto (fun j => (((φ j + 1 : ℕ)) : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hphi
  have hcorr : Filter.Tendsto (fun j => ((φ j + 1 : ℕ) : ℝ)⁻¹ • ((⇑T)^[φ j + 1] x0 - x0))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun j => (B + ‖x0‖) * ((((φ j + 1 : ℕ)) : ℝ)⁻¹)) (fun j => ?_) ?_
    · have e1 : ‖((φ j + 1 : ℕ) : ℝ)⁻¹ • ((⇑T)^[φ j + 1] x0 - x0)‖
          = ‖(⇑T)^[φ j + 1] x0 - x0‖ * (((φ j + 1 : ℕ)) : ℝ)⁻¹ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
          mul_comm]
      rw [e1]
      exact mul_le_mul_of_nonneg_right
        (calc ‖(⇑T)^[φ j + 1] x0 - x0‖ ≤ ‖(⇑T)^[φ j + 1] x0‖ + ‖x0‖ := norm_sub_le _ _
          _ ≤ B + ‖x0‖ := by
            have hle := hB ((⇑T)^[φ j + 1] x0) (hmem (φ j + 1) x0 hx0)
            linarith)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    · have hbm : Filter.Tendsto (fun j => (B + ‖x0‖) * ((((φ j + 1 : ℕ)) : ℝ)⁻¹)) Filter.atTop
          (nhds ((B + ‖x0‖) * 0)) :=
        hinv.const_mul _
      rw [mul_zero] at hbm
      exact hbm
  have hkeyφ : ∀ j, T (a (φ j))
      = a (φ j) + ((φ j + 1 : ℕ) : ℝ)⁻¹ • ((⇑T)^[φ j + 1] x0 - x0) := by
    intro j
    have h := key (φ j + 1) (Nat.succ_ne_zero (φ j))
    simpa [ha] using h
  have hlim2 : Filter.Tendsto (fun j => T (a (φ j))) Filter.atTop (nhds z) := by
    have h2 : Filter.Tendsto (fun j => a (φ j)
        + ((φ j + 1 : ℕ) : ℝ)⁻¹ • ((⇑T)^[φ j + 1] x0 - x0)) Filter.atTop (nhds (z + 0)) :=
      hφlim.add hcorr
    simp only [← hkeyφ, add_zero] at h2
    exact h2
  exact ⟨z, hzK, tendsto_nhds_unique hTlim hlim2⟩

private theorem finInterAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K)
    {ι : Type*} (F : ι → E →ᴬ[ℝ] E)
    (hF_maps : ∀ i, MapsTo (F i) K K)
    (hF_comm : ∀ i j : ι, ∀ x : E, F i (F j x) = F j (F i x)) :
    ∀ s : Finset ι, ∃ x ∈ K, ∀ i ∈ s, F i x = x := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · obtain ⟨x, hx⟩ := hK_nonempty
    exact ⟨x, hx, fun i hi => (Finset.notMem_empty i hi).elim⟩
  · intro a t hat ih
    obtain ⟨y, hyK, hyfix⟩ := ih
    have hCclosed : IsClosed {x ∈ K | ∀ i ∈ t, (F i) x = x} := by
      have heq : {x ∈ K | ∀ i ∈ t, (F i) x = x}
          = K ∩ ⋂ i ∈ t, {x : E | (F i) x = x} := by
        ext x
        simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
      rw [heq]
      exact hK_compact.isClosed.inter
        (isClosed_biInter fun i _ => isClosed_eq (F i).cont continuous_id)
    have hCconvex : Convex ℝ {x ∈ K | ∀ i ∈ t, (F i) x = x} := by
      intro x hx y hy c d hc hd hcd
      simp only [mem_sep_iff] at hx hy ⊢
      refine ⟨hK_convex hx.1 hy.1 hc hd hcd, fun i hi => ?_⟩
      have hci := convexFixAux (F i)
      exact hci (hx.2 i hi) (hy.2 i hi) hc hd hcd
    have hCmaps : ∀ j, MapsTo (F j) {x ∈ K | ∀ i ∈ t, (F i) x = x}
        {x ∈ K | ∀ i ∈ t, (F i) x = x} := by
      intro j x hx
      simp only [mem_sep_iff] at hx ⊢
      refine ⟨hF_maps j hx.1, fun i hi => ?_⟩
      rw [hF_comm i j x, hx.2 i hi]
    have hyC : y ∈ {x ∈ K | ∀ i ∈ t, (F i) x = x} := ⟨hyK, hyfix⟩
    obtain ⟨z, hzC, hzfix⟩ := existsFixAux ⟨y, hyC⟩
      (hK_compact.of_isClosed_subset hCclosed (fun x hx => (mem_sep_iff.mp hx).1))
      hCconvex (F a) (hCmaps a)
    refine ⟨z, (mem_sep_iff.mp hzC).1, fun i hi => ?_⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hit
    · exact hzfix
    · exact (mem_sep_iff.mp hzC).2 i hit

/--
**Markov–Kakutani fixed-point theorem.** Let $K$ be a nonempty compact convex subset of a real
normed space $E$, and let $(F_i)_{i \in I}$ be a family of continuous affine maps $E \to E$ such
that each $F_i$ maps $K$ into $K$ and $F_i(F_j(x)) = F_j(F_i(x))$ for all $i, j \in I$ and all
$x \in E$. Then there is $x \in K$ with $F_i(x) = x$ for every $i \in I$.

Commutation is required on all of $E$, not only on $K$.

Proves `Wanted` entry `markovKakutani_commonFixedPoint`.

Source: A. Markov, C. R. Acad. Sci. URSS 1936 and S. Kakutani, Proc. Imp. Acad. Tokyo 14 (1938)
242-245, Markov-Kakutani fixed-point theorem; Lean states real normed nonempty compact convex case
with globally commuting `E →ᴬ[ℝ] E` family.
-/
theorem markovKakutani_commonFixedPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K)
    {ι : Type*} (F : ι → E →ᴬ[ℝ] E)
    (hF_maps : ∀ i, MapsTo (F i) K K)
    (hF_comm : ∀ i j : ι, ∀ x : E, F i (F j x) = F j (F i x)) :
    ∃ x ∈ K, ∀ i, F i x = x := by
  classical
  set t : Finset ι → Set E := fun s => {x ∈ K | ∀ i ∈ s, (F i) x = x} with ht
  have hclosed : ∀ s, IsClosed (t s) := by
    intro s
    have heq : t s = K ∩ ⋂ i ∈ s, {x : E | (F i) x = x} := by
      ext x
      simp only [ht, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    rw [heq]
    exact hK_compact.isClosed.inter
      (isClosed_biInter fun i _ => isClosed_eq (F i).cont continuous_id)
  have hsub : ∀ s, t s ⊆ K := by
    intro s x hx
    simp only [ht, mem_sep_iff] at hx
    exact hx.1
  have hne : ∀ s, (t s).Nonempty := by
    intro s
    obtain ⟨x, hxK, hxfix⟩ :=
      finInterAux hK_nonempty hK_compact hK_convex F hF_maps hF_comm s
    refine ⟨x, ?_⟩
    simp only [ht, mem_sep_iff]
    exact ⟨hxK, hxfix⟩
  have hinter : (⋂ s, t s).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hcover : K ⊆ ⋃ s, (t s)ᶜ := by
      intro x hx
      simp only [mem_iUnion, mem_compl_iff]
      by_contra hmem
      have hxmem : x ∈ ⋂ s, t s := by
        rw [mem_iInter]
        intro s
        by_contra hs
        exact hmem ⟨s, hs⟩
      rw [hcon] at hxmem
      exact Set.notMem_empty x hxmem
    obtain ⟨u, hu⟩ :=
      hK_compact.elim_finite_subcover _ (fun s => (hclosed s).isOpen_compl) hcover
    obtain ⟨w, hwmem⟩ := hne (u.biUnion id)
    have hwK : w ∈ K := hsub _ hwmem
    have huw : w ∈ ⋃ s ∈ u, (t s)ᶜ := hu hwK
    simp only [mem_iUnion, mem_compl_iff] at huw
    obtain ⟨s, hsu, hws⟩ := huw
    have hws' : w ∈ t s := by
      simp only [ht, mem_sep_iff] at hwmem ⊢
      refine ⟨hwmem.1, fun i hi => hwmem.2 i ?_⟩
      exact Finset.mem_biUnion.mpr ⟨s, hsu, hi⟩
    exact hws hws'
  obtain ⟨x, hx⟩ := hinter
  refine ⟨x, hsub ∅ (mem_iInter.mp hx ∅), fun i => ?_⟩
  have hi : x ∈ t {i} := mem_iInter.mp hx {i}
  simp only [ht, mem_sep_iff] at hi
  exact hi.2 i (Finset.mem_singleton_self i)

end MathlibExt.Analysis.FunctionalAnalysis.MarkovKakutani
