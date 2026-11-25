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

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Continuity of the Haar modular character

The actual modular character is a compact test-function integral quotient.
Continuity follows by restricting nearby right translates to one compact
support. The argument applies to arbitrary locally compact topological groups.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped Topology NNReal

namespace MeasureTheory.Measure

universe uG

/-- Let `G` be a locally compact topological group. Its modular character takes values in the
nonnegative real numbers with their usual topology.

The existing Haar modular character is continuous without countability assumptions. -/
theorem continuous_modularCharacter
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] :
    Continuous (modularCharacter : G → ℝ≥0) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := haar
  obtain ⟨ψ, hψcomp, hψnonneg, hψone⟩ := exists_continuous_nonneg_pos (1 : G)
  let I : ℝ := ∫ x : G, ψ x ∂μ
  have hI : I ≠ 0 := ne_of_gt
    (ψ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hψcomp hψnonneg hψone)
  have hIntegral : Continuous (fun g : G => ∫ x : G, ψ (x * g) ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨U, hUcompact, hUneigh⟩ := exists_compact_mem_nhds g₀
    let K : Set G := (fun p : G × G => p.1 * p.2⁻¹) ''
      (tsupport (ψ : G → ℝ) ×ˢ U)
    have hψK : IsCompact (tsupport (ψ : G → ℝ)) := hψcomp
    have hK : IsCompact K :=
      (hψK.prod hUcompact).image (continuous_fst.mul continuous_snd.inv)
    have hsupport : ∀ g x : G, g ∈ U → x ∉ K → ψ (x * g) = 0 := by
      intro g x hg hx
      by_contra hne
      apply hx
      refine ⟨(x * g, g), ⟨?_, hg⟩, ?_⟩
      · exact subset_closure hne
      · change (x * g) * g⁻¹ = x
        rw [mul_assoc, mul_inv_cancel, mul_one]
    have hcont : ContinuousOn (fun g : G => ∫ x : G, ψ (x * g) ∂μ) U := by
      have h := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (μ := μ) (ContinuousLinearMap.mul ℝ ℝ)
        (f := fun g x : G => ψ (x * g)) (s := U) (k := K)
        (g := fun _ : G => (1 : ℝ)) hK
        (ψ.continuous.comp (continuous_snd.mul continuous_fst)).continuousOn
        hsupport (integrableOn_const hK.measure_ne_top)
      simpa only [ContinuousLinearMap.mul_apply', one_mul] using h
    exact hcont.continuousAt hUneigh
  have hformula (g : G) : (modularCharacter g : ℝ) =
      (∫ x : G, ψ (x * g) ∂μ) / I := by
    calc
      (modularCharacter g : ℝ) = (haarScalarFactor (map (· * g) μ) μ : ℝ) :=
        congrArg (fun r : ℝ≥0 => (r : ℝ))
          (modularCharacterFun_eq_haarScalarFactor μ g)
      _ = (∫ x : G, ψ x ∂map (· * g) μ) / I :=
        haarScalarFactor_eq_integral_div _ _ ψ.continuous hψcomp hI
      _ = (∫ x : G, ψ (x * g) ∂μ) / I := by
        rw [integral_map (AEMeasurable.mul_const aemeasurable_id' g)
          ψ.continuous.aestronglyMeasurable]
  have hscalar : Continuous (fun g : G => (modularCharacter g : ℝ)) := by
    simpa only [hformula] using hIntegral.div_const I
  exact continuous_induced_rng.2 hscalar

end MeasureTheory.Measure
