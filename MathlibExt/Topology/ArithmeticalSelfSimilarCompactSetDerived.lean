/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSet
import Mathlib.SetTheory.Ordinal.Topology

/-!
# Enumerating the derived sets of a self-similar compact set

The decreasing enumeration of the `n`-th derived set is obtained from the original enumeration
by reindexing with ordinal multiplication.
-/

namespace MetaMathlibExt

open Ordinal Order Set

namespace isSelfSimilarCompactSet_derivedSet_enum

private theorem image_derivedSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) (s : Set X) :
    derivedSet (f '' s) = f '' derivedSet s := by
  apply Subset.antisymm _ (hf.continuous.image_derivedSet hf.injective)
  intro y hy
  have hy_range : y ∈ range f :=
    hf.isClosed_range.closure_subset
      (closure_mono (image_subset_range f s) (derivedSet_subset_closure _ hy))
  obtain ⟨x, rfl⟩ := hy_range
  refine ⟨x, ?_, rfl⟩
  simp only [mem_derivedSet, accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hy ⊢
  rwa [← Set.image_singleton, ← Set.image_sdiff hf.injective, hf.closure_image_eq,
    hf.injective.mem_set_image] at hy

private theorem index_strictMono (m : ℕ) :
    StrictMono fun α : Ordinal.{0} => ω ^ (m : Ordinal) * (1 + α) :=
  (isNormal_mul_right (opow_pos _ omega0_pos)).strictMono.comp add_right_strictMono

private theorem index_top (m : ℕ) :
    ω ^ (m : Ordinal) * (1 + (ω ^ ω : Ordinal.{0})) = ω ^ ω := by
  have hω : ω ≤ (ω ^ ω : Ordinal.{0}) := by
    calc
      ω = ω ^ (1 : Ordinal) := (opow_one _).symm
      _ ≤ ω ^ ω := opow_le_opow_right omega0_pos one_lt_omega0.le
  rw [one_add_of_omega0_le hω, ← opow_add, natCast_add_omega0]

private theorem index_mapsTo (m : ℕ) :
    MapsTo (fun α : Ordinal.{0} => ω ^ (m : Ordinal) * (1 + α)) (Iic (ω ^ ω)) (Iic (ω ^ ω)) :=
  fun _ hα => ((index_strictMono m).monotone hα).trans (index_top m).le

private theorem ordinal_derivedSet :
    derivedSet (Iic (ω ^ ω : Ordinal.{0})) = (fun α => ω * (1 + α)) '' Iic (ω ^ ω) := by
  ext β
  constructor
  · intro hβ
    have hlim := (mem_derivedSet.mp hβ).isSuccLimit
    have hle : β ≤ ω ^ ω := (isClosed_iff_derivedSet_subset _).mp isClosed_Iic hβ
    obtain ⟨γ, hγ⟩ := isSuccPrelimit_iff_omega0_dvd.mp hlim.isSuccPrelimit
    have hγpos : 0 < γ := by
      by_contra! h
      exact hlim.bot_lt.ne' (by simpa [le_zero_iff.mp h] using hγ)
    have heq : ω * (1 + (γ - 1)) = β := by
      rw [Ordinal.add_sub_cancel_of_le (one_le_iff_pos.mpr hγpos), ← hγ]
    refine ⟨γ - 1, ?_, heq⟩
    have hmono : StrictMono fun α : Ordinal.{0} => ω * (1 + α) := by
      simpa only [Nat.cast_one, opow_one] using index_strictMono 1
    have htop : ω * (1 + (ω ^ ω : Ordinal.{0})) = ω ^ ω := by
      simpa only [Nat.cast_one, opow_one] using index_top 1
    exact hmono.le_iff_le.mp (by rwa [heq, htop])
  · rintro ⟨α, hα, rfl⟩
    have hlim : IsSuccLimit (ω * (1 + α)) :=
      isSuccLimit_mul_left isSuccLimit_omega0 (zero_lt_one.trans_le le_self_add)
    have hle : ω * (1 + α) ≤ ω ^ ω := by
      simpa only [Nat.cast_one, opow_one, mem_Iic] using index_mapsTo 1 hα
    rw [mem_derivedSet, SuccOrder.accPt_principal]
    refine ⟨hlim.not_isMin, fun β hβ => ?_⟩
    obtain ⟨γ, hγ⟩ := (hlim.lt_iff_nonempty_Ioo).mp hβ
    exact ⟨γ, hγ.2.le.trans hle, hγ⟩

private theorem derivedSet_image_index_one {K : Set ℝ} (hK : IsCompact K)
    {f : Ordinal.{0} → ℝ} (hf : StrictAntiOn f (Iic (ω ^ ω))) (hfK : f '' Iic (ω ^ ω) = K) :
    derivedSet K = (fun α => f (ω * (1 + α))) '' Iic (ω ^ ω) := by
  let e : Iic (ω ^ ω : Ordinal.{0}) ≃o Kᵒᵈ :=
    StrictMono.orderIsoOfSurjective
      (fun a => ⟨f a, hfK ▸ mem_image_of_mem f a.property⟩)
      (fun a b hab => hf a.property b.property hab)
      (by
        intro y
        have hy : (OrderDual.ofDual y).val ∈ f '' Iic (ω ^ ω) :=
          hfK.symm ▸ (OrderDual.ofDual y).property
        obtain ⟨a, ha, h⟩ := hy
        exact ⟨⟨a, ha⟩, Subtype.ext h⟩)
  -- The inverse is continuous because it pulls ordinal rays back to open rays in the subtype.
  have he : Continuous e.symm := by
    refine OrderTopology.continuous_iff.mpr fun a => ⟨?_, ?_⟩
    · have h : e.symm ⁻¹' Ioi a = Ioi (e a) := by ext b; simp
      rw [h]
      change IsOpen (Subtype.val ⁻¹' Iio (OrderDual.ofDual (e a)).val)
      exact isOpen_Iio.preimage continuous_subtype_val
    · have h : e.symm ⁻¹' Iio a = Iio (e a) := by ext b; simp
      rw [h]
      change IsOpen (Subtype.val ⁻¹' Ioi (OrderDual.ofDual (e a)).val)
      exact isOpen_Ioi.preimage continuous_subtype_val
  let : CompactSpace Kᵒᵈ := isCompact_iff_compactSpace.mp hK
  let H : Kᵒᵈ ≃ₜ Iic (ω ^ ω : Ordinal.{0}) :=
    e.symm.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap
  have hreal : Topology.IsClosedEmbedding (fun a : Iic (ω ^ ω : Ordinal.{0}) => f a) :=
    hK.isClosed.isClosedEmbedding_subtypeVal.comp H.symm.isClosedEmbedding
  have hord := image_derivedSet
    (isClosed_Iic (a := (ω ^ ω : Ordinal.{0}))).isClosedEmbedding_subtypeVal univ
  rw [image_univ, Subtype.range_coe_subtype] at hord
  change derivedSet (Iic (ω ^ ω : Ordinal.{0})) = _ at hord
  rw [ordinal_derivedSet] at hord
  have hreal_image : (fun a : Iic (ω ^ ω : Ordinal.{0}) => f a) '' univ = K := by
    rw [image_univ, ← hfK]
    exact Set.range_domRestrict f _
  rw [← hreal_image, image_derivedSet hreal, ← image_image f Subtype.val, ← hord, image_image]

end isSelfSimilarCompactSet_derivedSet_enum

open isSelfSimilarCompactSet_derivedSet_enum in
/-- **Enumerating the derived sets of a self-similar compact set.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, let $n \ge 1$, and write $K^{(n)}$ for the $n$-th
derived set of $K$. Let $\alpha \mapsto K[\alpha]$ and $\alpha \mapsto K^{(n)}[\alpha]$ be
strictly decreasing maps from the ordinals $\alpha \le \omega^\omega$ onto $K$ and onto
$K^{(n)}$, respectively. Then $K^{(n)}[\alpha] = K[\omega^n (1 + \alpha)]$ (ordinal
arithmetic) for every ordinal $\alpha \le \omega^\omega$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem isSelfSimilarCompactSet_derivedSet_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {n : ℕ} (hn : 1 ≤ n) {f g : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (hg : StrictAntiOn g (Set.Iic (ω ^ ω))) (hgK : g '' Set.Iic (ω ^ ω) = derivedSet^[n] K)
    {α : Ordinal.{0}} (hα : α ≤ ω ^ ω) :
    g α = f (ω ^ (n : Ordinal) * (1 + α)) := by
  let s := Iic (ω ^ ω : Ordinal.{0})
  have hcompact (m : ℕ) : IsCompact (derivedSet^[m] K) := by
    induction m with
    | zero => exact hK.2.2.1
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.of_isClosed_subset (isClosed_derivedSet _)
        ((isClosed_iff_derivedSet_subset _).mp ih.isClosed)
  have himage (m : ℕ) (hm : 1 ≤ m) :
      (fun β => f (ω ^ (m : Ordinal) * (1 + β))) '' s = derivedSet^[m] K := by
    induction m, hm using Nat.le_induction with
    | base =>
      simpa only [Nat.cast_one, opow_one, Function.iterate_one] using
        (derivedSet_image_index_one hK.2.2.1 hf hfK).symm
    | succ m _ ih =>
      rw [Function.iterate_succ_apply']
      rw [derivedSet_image_index_one (hcompact m)
        (hf.comp_strictMonoOn ((index_strictMono m).strictMonoOn s) (index_mapsTo m)) ih]
      congr 1
      funext β
      have hω : ω ≤ ω * (1 + β) := le_mul_left _ (zero_lt_one.trans_le le_self_add)
      rw [Function.comp_apply, one_add_of_omega0_le hω, Nat.cast_succ, opow_add_one, mul_assoc]
  let g' : s → ℝᵒᵈ := fun β => OrderDual.toDual (g β)
  let f' : s → ℝᵒᵈ := fun β => OrderDual.toDual (f (ω ^ (n : Ordinal) * (1 + β)))
  have hg' : StrictMono g' := fun a b hab => hg a.property b.property hab
  have hf' : StrictMono f' := fun a b hab =>
    hf (index_mapsTo n a.property) (index_mapsTo n b.property) (index_strictMono n hab)
  have hrange : range g' = range f' := by
    change range (s.domRestrict g) = range (s.domRestrict fun β => f (ω ^ (n : Ordinal) * (1 + β)))
    rw [Set.range_domRestrict, Set.range_domRestrict, hgK, himage n hn]
  exact congrFun ((hg'.range_inj_of_wellFoundedLT hf').mp hrange) ⟨α, hα⟩

end MetaMathlibExt
