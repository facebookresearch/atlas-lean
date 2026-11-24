/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CanonicalApproximateUnit
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedMultiplierStrict
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual coefficient nondegeneracy on the same-seminorm completion

The original coefficient approximate-unit filter acts uniformly on the
compact coefficient range of each actual Haar-core function. Its literal
finite-on-compacts integral bound gives convergence in the original L1
gauge, and then in every admissible seminorm completion. These actual
coefficient images belong to the literal coefficient range span. The
proved dense core gives density of that span on the same completed carrier.

The computed strict multiplier pair therefore receives its actual
coefficient-nondegeneracy field. No approximate-unit, norm, density,
faithful embedding or desired pair is supplied as an output model.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped Topology MultiplierAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

section OriginalL1

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : PointNormCStarAction G A)

/-- A uniform original coefficient error on its compact support bounds its literal L1 integral. -/
theorem l1Gauge_coefficientLeft_sub_le (a : A) (f : Carrier μ α) (δ : ℝ) (hδ : 0 ≤ δ)
    (hBound : ∀ s ∈ tsupport (toCc μ α f), ‖a * f s - f s‖ ≤ δ) :
    l1Gauge μ α (coefficientLeft μ α a f - f) ≤ μ.real (tsupport (toCc μ α f)) * δ := by
  let F := toCc μ α f
  let K := tsupport F
  let E := toCc μ α (coefficientLeft μ α a f - f)
  have hzero (s : G) (hs : s ∉ K) : ‖E s‖ = 0 := by
    have hFzero : F s = 0 := image_eq_zero_of_notMem_tsupport hs
    change ‖a * F s - F s‖ = 0
    rw [hFzero, mul_zero, sub_self, norm_zero]
  have hCompact : HasCompactSupport (fun s : G => ‖E s‖) :=
    E.hasCompactSupport.comp_left (g := fun x : A => ‖x‖) norm_zero
  have hInt : Integrable (fun s : G => ‖E s‖) μ :=
    (map_continuous E).norm.integrable_of_hasCompactSupport hCompact
  have hAll (s : G) : ‖E s‖ ≤ δ := by
    by_cases hs : s ∈ K
    · change ‖a * f s - f s‖ ≤ δ
      exact hBound s hs
    · rw [hzero s hs]
      exact hδ
  calc
    _ = ∫ s : G, ‖E s‖ ∂μ := rfl
    _ = ∫ s in K, ‖E s‖ ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ ∫ _ in K, δ ∂μ :=
      integral_mono hInt.integrableOn (integrableOn_const F.hasCompactSupport.measure_ne_top) hAll
    _ = μ.real K * δ := by rw [setIntegral_const, smul_eq_mul]

/-- The computed original coefficient approximate unit converges in the literal Haar-core L1 gauge. -/
theorem tendsto_l1Gauge_coefficientLeft_sub (f : Carrier μ α) :
    Tendsto (fun a : A => l1Gauge μ α (coefficientLeft μ α a f - f))
      (CStarAlgebra.canonicalApproximateUnit A) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let F := toCc μ α f
  let K := tsupport F
  let M := μ.real K
  let δ := ε / (M + 1)
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hDen : 0 < M + 1 := add_pos_of_nonneg_of_pos hM zero_lt_one
  have hδ : 0 < δ := div_pos hε hDen
  have hImage : IsCompact (F '' K) := F.hasCompactSupport.image (map_continuous F)
  have hUniform := CStarAlgebra.canonicalApproximateUnit_eventually_compact_mul_sub_lt
    A (F '' K) hImage δ hδ
  filter_upwards [hUniform] with a ha
  have hBound : l1Gauge μ α (coefficientLeft μ α a f - f) ≤ M * δ :=
    l1Gauge_coefficientLeft_sub_le μ α a f δ hδ.le fun s hs => (ha (F s) ⟨s, hs, rfl⟩).le
  have hSmall : M * δ < ε := by
    calc
      M * δ < (M + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one M) hδ
      _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hDen.ne']
  simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (l1Gauge_nonneg μ α (coefficientLeft μ α a f - f))] using hBound.trans_lt hSmall

end OriginalL1

section CompletedCoefficient

variable [IsTopologicalGroup G] [LocallyCompactSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- The literal complex span of the computed coefficient multiplier ranges on the actual completion. -/
def coefficientMultiplierSpan : Submodule ℂ p.NonUnitalCompletion :=
  Submodule.span ℂ (Set.range fun z : A × p.NonUnitalCompletion =>
    (coefficientMultiplierHom μ α p z.1).fst z.2)

omit [μ.Regular] in
/-- Each actual completed coefficient value belongs to its original coefficient range span. -/
theorem coefficientMultiplier_fst_mem_span (a : A) (x : p.NonUnitalCompletion) :
    (coefficientMultiplierHom μ α p a).fst x ∈ coefficientMultiplierSpan μ α p :=
  Submodule.subset_span ⟨(a, x), rfl⟩

variable (hp : p ∈ admissibleCStarSeminorms μ α)
include hp

omit [μ.Regular] in
/-- The computed coefficient approximate unit tends to the original source image in every admissible p. -/
theorem tendsto_toNonUnitalCompletion_coefficientLeft (f : Carrier μ α) :
    Tendsto (fun a : A => p.toNonUnitalCompletion (coefficientLeft μ α a f))
      (CStarAlgebra.canonicalApproximateUnit A) (𝓝 (p.toNonUnitalCompletion f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_l1Gauge_coefficientLeft_sub μ α f).eventually (gt_mem_nhds hε)] with a ha
  have hBound : dist (p.toNonUnitalCompletion (coefficientLeft μ α a f))
      (p.toNonUnitalCompletion f) ≤ l1Gauge μ α (coefficientLeft μ α a f - f) := by
    rw [dist_eq_norm, ← map_sub, CStarSeminorm.norm_toNonUnitalCompletion]
    exact hp _
  exact hBound.trans_lt ha

omit [μ.Regular] in
/-- Every original core image lies in the closure of the actual coefficient multiplier range span. -/
theorem toNonUnitalCompletion_mem_coefficientMultiplierSpan_closure (f : Carrier μ α) :
    p.toNonUnitalCompletion f ∈ (coefficientMultiplierSpan μ α p).topologicalClosure := by
  let _ : (CStarAlgebra.canonicalApproximateUnit A).NeBot :=
    CStarAlgebra.canonicalApproximateUnit_neBot A
  change p.toNonUnitalCompletion f ∈ closure (coefficientMultiplierSpan μ α p : Set p.NonUnitalCompletion)
  apply mem_closure_of_tendsto (tendsto_toNonUnitalCompletion_coefficientLeft μ α p hp f)
  exact Eventually.of_forall fun a => by
    rw [SetLike.mem_coe]
    simpa only [coefficientMultiplierHom_apply, coefficientMultiplier_fst_apply] using
      coefficientMultiplier_fst_mem_span μ α p a (p.toNonUnitalCompletion f)

omit [μ.Regular] in
/-- The computed coefficient multiplier is nondegenerate on the same actual admissible completion. -/
theorem dense_coefficientMultiplierSpan :
    Dense (coefficientMultiplierSpan μ α p : Set p.NonUnitalCompletion) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  intro x _
  refine p.denseRange_toNonUnitalCompletion.induction_on x ?_ ?_
  · exact (coefficientMultiplierSpan μ α p).isClosed_topologicalClosure
  · intro f
    exact toNonUnitalCompletion_mem_coefficientMultiplierSpan_closure μ α p hp f

/-- The original computed strict pair with its internally proved actual coefficient nondegeneracy. -/
def canonicalNondegenerateStrictMultiplierPair :
    { pair : (A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion)) ×
        (G →* unitary 𝓜(ℂ, p.NonUnitalCompletion)) //
      (∀ g : G, ∀ a : A,
        (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) * pair.1 a *
          star (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) = pair.1 (α g a)) ∧
      DoubleCentralizer.StrictContinuous (fun g : G => (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion))) ∧
      Dense ((Submodule.span ℂ (Set.range fun z : A × p.NonUnitalCompletion =>
        (pair.1 z.1).fst z.2)) : Set p.NonUnitalCompletion) } :=
  ⟨(canonicalStrictMultiplierPair μ α p hp).val,
    (canonicalStrictMultiplierPair μ α p hp).property.1,
    (canonicalStrictMultiplierPair μ α p hp).property.2, by
      change Dense (coefficientMultiplierSpan μ α p : Set p.NonUnitalCompletion)
      exact dense_coefficientMultiplierSpan μ α p hp⟩

/-- The nondegenerate pair keeps the exact original coefficient and group multiplier maps. -/
@[simp]
theorem canonicalNondegenerateStrictMultiplierPair_val :
    (canonicalNondegenerateStrictMultiplierPair μ α p hp).val =
      (canonicalStrictMultiplierPair μ α p hp).val := rfl

/-- The actual pair carries the proved density of the original coefficient ranges. -/
theorem canonicalNondegenerateStrictMultiplierPair_nondegenerate :
    Dense ((Submodule.span ℂ (Set.range fun z : A × p.NonUnitalCompletion =>
      ((canonicalNondegenerateStrictMultiplierPair μ α p hp).val.1 z.1).fst z.2)) :
        Set p.NonUnitalCompletion) :=
  (canonicalNondegenerateStrictMultiplierPair μ α p hp).property.2.2

/-- The actual nondegenerate pair retains the original strict group continuity. -/
theorem canonicalNondegenerateStrictMultiplierPair_strictContinuous :
    DoubleCentralizer.StrictContinuous (fun g : G =>
      ((canonicalNondegenerateStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion))) :=
  (canonicalNondegenerateStrictMultiplierPair μ α p hp).property.2.1

/-- The actual nondegenerate pair retains the original conjugation covariance. -/
theorem canonicalNondegenerateStrictMultiplierPair_covariance (g : G) (a : A) :
    ((canonicalNondegenerateStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) *
        (canonicalNondegenerateStrictMultiplierPair μ α p hp).val.1 a *
          star ((canonicalNondegenerateStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) =
      (canonicalNondegenerateStrictMultiplierPair μ α p hp).val.1 (α g a) :=
  (canonicalNondegenerateStrictMultiplierPair μ α p hp).property.1 g a

end CompletedCoefficient

end

end HaarTwistedCore
