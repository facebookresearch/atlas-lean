/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
-- Brings `RCLike.innerProductSpace` into scope, so the `NormedSpace 𝕜 𝕜` instance in the
-- statement is `InnerProductSpace.toNormedSpace`, as it is under `import Mathlib`.
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

namespace MetaMathlibExt

open Set Metric

/-- The norm of a scalar is the real part of its product with some unit scalar. -/
private theorem exists_norm_eq_one_re_mul_eq_norm {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) :
    ∃ u : 𝕜, ‖u‖ = 1 ∧ RCLike.re (u * c) = ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, norm_one, by simp⟩
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hne : ‖c‖ ≠ 0 := ne_of_gt hpos
    refine ⟨(↑(‖c‖⁻¹) : 𝕜) * starRingEnd 𝕜 c, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hne]
    · have hcc : starRingEnd 𝕜 c * c = (↑‖c‖ : 𝕜) ^ 2 := by
        rw [mul_comm]
        exact RCLike.mul_conj c
      have hreal : ‖c‖⁻¹ * ‖c‖ ^ 2 = ‖c‖ := by
        rw [sq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      have hmul2 : (↑(‖c‖⁻¹) : 𝕜) * ((↑‖c‖ : 𝕜) ^ 2) = (↑‖c‖ : 𝕜) := by
        have h : (↑(‖c‖⁻¹ * ‖c‖ ^ 2) : 𝕜) = (↑‖c‖ : 𝕜) := by rw [hreal]
        rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, h]
      rw [mul_assoc, hcc, hmul2, RCLike.ofReal_re]

/-- The operator norm of a continuous linear functional is the supremum of real parts
over the closed unit ball. -/
private theorem norm_eq_sSup_re_closedBall {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (y : StrongDual 𝕜 E) :
    ‖y‖ = sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) := by
  have hbdd : BddAbove ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) := by
    refine ⟨‖y‖, ?_⟩
    rintro s ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff] at hx
    calc RCLike.re (y x) ≤ ‖y x‖ := RCLike.re_le_norm _
      _ ≤ ‖y‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖y‖ * 1 := mul_le_mul_of_nonneg_left hx (ContinuousLinearMap.opNorm_nonneg _)
      _ = ‖y‖ := mul_one _
  have hne : ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1).Nonempty :=
    ⟨RCLike.re (y 0), 0, mem_closedBall_zero_iff.mpr (by simp), rfl⟩
  have hM : 0 ≤ sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) := by
    have h0 : RCLike.re (y 0) = 0 := by simp
    rw [← h0]
    exact le_csSup hbdd ⟨0, mem_closedBall_zero_iff.mpr (by simp), rfl⟩
  apply ContinuousLinearMap.opNorm_eq_of_bounds hM
  · intro x
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨u, hu1, hu2⟩ := exists_norm_eq_one_re_mul_eq_norm (y ((↑(‖x‖⁻¹) : 𝕜) • x))
      have hvnorm : ‖(↑(‖x‖⁻¹) : 𝕜) • x‖ = 1 := by
        rw [norm_smul, RCLike.norm_ofReal,
          abs_of_nonneg (le_of_lt (inv_pos.mpr (norm_pos_iff.mpr hx0))),
          inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hx0))]
      have hmul1 : (↑‖x‖ : 𝕜) * (↑(‖x‖⁻¹) : 𝕜) = 1 := by
        rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr hx0)),
          RCLike.ofReal_one]
      have hxuv : (↑‖x‖ : 𝕜) • ((↑(‖x‖⁻¹) : 𝕜) • x) = x := by
        rw [← mul_smul, hmul1, one_smul]
      have hmem : u • ((↑(‖x‖⁻¹) : 𝕜) • x) ∈ Metric.closedBall (0 : E) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, hu1, hvnorm, mul_one]
      have hre : RCLike.re (y (u • ((↑(‖x‖⁻¹) : 𝕜) • x)))
          = ‖y ((↑(‖x‖⁻¹) : 𝕜) • x)‖ := by
        rw [map_smul, smul_eq_mul, hu2]
      have hle : ‖y ((↑(‖x‖⁻¹) : 𝕜) • x)‖
          ≤ sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) := by
        rw [← hre]
        exact le_csSup hbdd ⟨_, hmem, rfl⟩
      have e1 : (↑‖x‖ : 𝕜) • (y ((↑(‖x‖⁻¹) : 𝕜) • x)) = y x := by
        rw [← map_smul, hxuv]
      have hnorm : ‖y x‖ = ‖x‖ * ‖y ((↑(‖x‖⁻¹) : 𝕜) • x)‖ := by
        rw [← e1, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      calc ‖y x‖ = ‖x‖ * ‖y ((↑(‖x‖⁻¹) : 𝕜) • x)‖ := hnorm
        _ ≤ ‖x‖ * sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) * ‖x‖ :=
          mul_comm _ _
  · intro N hNge hN
    apply csSup_le hne
    rintro s ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff] at hx
    calc RCLike.re (y x) ≤ ‖y x‖ := RCLike.re_le_norm _
      _ ≤ N * ‖x‖ := hN x
      _ ≤ N * 1 := mul_le_mul_of_nonneg_left hx hNge
      _ = N := mul_one _

/-- A real scalar acts on the weak-star bidual as its image in `𝕜`. -/
private theorem ofReal_smul_weakDual {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (r : ℝ) (w : WeakDual 𝕜 (StrongDual 𝕜 E)) :
    (↑r : 𝕜) • w = r • w := by
  have : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakBilin.instIsScalarTower (topDualPairing 𝕜 (StrongDual 𝕜 E))
  have h : ((r • (1 : 𝕜)) • w) = (r • ((1 : 𝕜) • w)) :=
    IsScalarTower.smul_assoc _ _ _
  rw [one_smul] at h
  have h1 : r • (1 : 𝕜) = (↑r : 𝕜) := by
    rw [Algebra.smul_def, mul_one]
  rw [h1] at h
  exact h

private theorem convex_closure_image_closedBall
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Convex ℝ (closure ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
      Metric.closedBall (0 : E) 1)) := by
  refine Convex.closure (𝕜 := ℝ) (E := WeakDual 𝕜 (StrongDual 𝕜 E)) ?_
  rintro y₁ ⟨x₁, hx₁, rfl⟩ y₂ ⟨x₂, hx₂, rfl⟩ a b ha hb hab
  refine ⟨(↑a : 𝕜) • x₁ + (↑b : 𝕜) • x₂, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff] at hx₁
    rw [mem_closedBall_zero_iff] at hx₂
    rw [mem_closedBall_zero_iff]
    calc ‖(↑a : 𝕜) • x₁ + (↑b : 𝕜) • x₂‖
          ≤ ‖(↑a : 𝕜) • x₁‖ + ‖(↑b : 𝕜) • x₂‖ := norm_add_le _ _
        _ = a * ‖x₁‖ + b * ‖x₂‖ := by
          rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
            abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * 1 + b * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hx₁ ha
          · exact mul_le_mul_of_nonneg_left hx₂ hb
        _ = 1 := by rw [mul_one, mul_one, hab]
  · simp only [Function.comp_apply]
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    simp only [ofReal_smul_weakDual]

private theorem closure_image_closedBall_subset
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    closure
        ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
          Metric.closedBall (0 : E) 1)
      ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall
          (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
  apply closure_minimal
  · rintro w ⟨x, hx, rfl⟩
    change WeakDual.toStrongDual
        ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) x)
      ∈ Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1
    rw [Function.comp_apply, StrongDual.toStrongDual_toWeakDual]
    have hLi : (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)) x
        = (NormedSpace.inclusionInDoubleDual 𝕜 E) x := rfl
    have hnorm := (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map x
    rw [hLi] at hnorm
    have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hnorm1 : ‖(NormedSpace.inclusionInDoubleDual 𝕜 E) x‖ ≤ 1 := by
      rw [hnorm]
      exact hxnorm
    apply Metric.mem_closedBall.mpr
    have e : dist ((NormedSpace.inclusionInDoubleDual 𝕜 E) x) 0
        = ‖(NormedSpace.inclusionInDoubleDual 𝕜 E) x‖ :=
      dist_zero_right ((NormedSpace.inclusionInDoubleDual 𝕜 E) x)
    rw [e]
    exact hnorm1
  · exact WeakDual.isClosed_closedBall 0 1

/-- A point of the weak-star bidual outside the closure of the image of the unit ball is
separated from that image by a functional of `StrongDual 𝕜 E`. -/
private theorem exists_separating_strongDual
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (z : WeakDual 𝕜 (StrongDual 𝕜 E))
    (hzne : z ∉ closure ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
      Metric.closedBall (0 : E) 1)) :
    ∃ y : StrongDual 𝕜 E, ∃ u : ℝ,
      (∀ x ∈ Metric.closedBall (0 : E) 1, RCLike.re (y x) < u)
        ∧ u < RCLike.re (z y) := by
  have : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakBilin.instIsScalarTower (topDualPairing 𝕜 (StrongDual 𝕜 E))
  have : LocallyConvexSpace ℝ (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WithSeminorms.toLocallyConvexSpace (WeakDual.withSeminorms 𝕜 (StrongDual 𝕜 E))
  have hconv := convex_closure_image_closedBall (𝕜 := 𝕜) (E := E)
  have hclosed : IsClosed
      (closure ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
        Metric.closedBall (0 : E) 1)) := isClosed_closure
  obtain ⟨φ, u, hφlt, hφu⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv hclosed hzne
  have hsurj := LinearMap.dualEmbedding_surjective (𝕜 := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 E)) (F := StrongDual 𝕜 E)
    (topDualPairing 𝕜 (StrongDual 𝕜 E))
  obtain ⟨y, hy⟩ := hsurj φ
  have hφ : ∀ w : WeakDual 𝕜 (StrongDual 𝕜 E), φ w = w y := fun w => by rw [← hy]; rfl
  refine ⟨y, u, ?_, ?_⟩
  · intro x hx
    have hmem : (StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) x
        ∈ closure ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
          Metric.closedBall (0 : E) 1) :=
      subset_closure ⟨x, hx, rfl⟩
    have hlt := hφlt _ hmem
    have heq : RCLike.re (φ ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) x))
        = RCLike.re (y x) := by
      rw [hφ, Function.comp_apply, StrongDual.toWeakDual_apply,
        NormedSpace.dual_def]
    rw [heq] at hlt
    exact hlt
  · have hφz : φ z = z y := hφ z
    rw [hφz] at hφu
    exact hφu

private theorem closedBall_subset_closure_image_closedBall
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WeakDual.toStrongDual ⁻¹' Metric.closedBall
          (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1
      ⊆ closure
        ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
          Metric.closedBall (0 : E) 1) := by
  intro z hz
  by_contra hzne
  obtain ⟨y, u, hlt, hu⟩ := exists_separating_strongDual z hzne
  have hz01 : ‖WeakDual.toStrongDual z‖ ≤ 1 := by
    have hmem := Set.mem_preimage.mp hz
    have hdist : dist (WeakDual.toStrongDual z) 0 ≤ 1 :=
      Metric.mem_closedBall.mp hmem
    have e : dist (WeakDual.toStrongDual z) 0 = ‖WeakDual.toStrongDual z‖ :=
      dist_zero_right (WeakDual.toStrongDual z)
    rw [e] at hdist
    exact hdist
  have hre : RCLike.re (z y) ≤ ‖y‖ := by
    have hzy : z y = (WeakDual.toStrongDual z) y := rfl
    rw [hzy]
    calc RCLike.re ((WeakDual.toStrongDual z) y) ≤ ‖(WeakDual.toStrongDual z) y‖ :=
          RCLike.re_le_norm _
      _ ≤ ‖WeakDual.toStrongDual z‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hz01 (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have hsup : sSup ((fun x => RCLike.re (y x)) '' Metric.closedBall (0 : E) 1) ≤ u := by
    apply csSup_le
    · exact ⟨RCLike.re (y 0), 0, mem_closedBall_zero_iff.mpr (by simp), rfl⟩
    · rintro s ⟨x, hx, rfl⟩
      exact le_of_lt (hlt x hx)
  have hnorm := norm_eq_sSup_re_closedBall y
  linarith

/--
**Goldstine's theorem.** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
let $E^{**}$ be its bidual and let $J : E \to E^{**}$ be the canonical embedding. In the
weak-star topology of $E^{**}$, the closure of the image under $J$ of the closed unit ball of $E$
is exactly the closed unit ball of $E^{**}$.

Proves `Wanted` entry `goldstine`.

Source: H. H. Goldstine, Weakly complete Banach spaces,
Duke Math. J. 4 (1938), DOI 10.1215/S0012-7094-38-00410-7; Rudin, Functional Analysis, 2nd
ed.; Lean states `RCLike` field case with metric closedBall formulation.
-/
theorem goldstine
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    closure
        ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
          Metric.closedBall (0 : E) 1)
      = WeakDual.toStrongDual ⁻¹' Metric.closedBall
          (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 :=
  le_antisymm closure_image_closedBall_subset closedBall_subset_closure_image_closedBall

end MetaMathlibExt
