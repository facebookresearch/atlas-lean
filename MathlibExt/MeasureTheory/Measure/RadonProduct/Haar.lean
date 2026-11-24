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

public import MathlibExt.MeasureTheory.Measure.RadonProduct.CompactSupport
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.UrysohnsLemma

/-!
# Haar invariance of the actual Borel Radon product

The compact-support integral formula and the original coordinate Haar
invariance prove invariance under actual product left translation. Positive
compact-support factor integrals prove that the constructed product is
nonzero. Its existing regularity then supplies open positivity, giving a
genuine Haar measure on the Borel sigma-algebra of the topological product.

No countability, s-finiteness or product-sigma-algebra identification is
used. The variable-coordinate shear and reverse-order compact-support
Fubini theorem remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped CompactlySupported

namespace MeasureTheory.Measure

noncomputable section

universe uG uK

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [T2Space K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure G) (ν : Measure K) [μ.Regular] [ν.Regular]

/-- The literal Borel measurable space of the topological product. -/
local instance instHaarRadonProductMeasurableSpace : MeasurableSpace (G × K) := borel (G × K)
local instance instHaarRadonProductBorelSpace : BorelSpace (G × K) := ⟨rfl⟩

section Invariance

variable [IsMulLeftInvariant μ] [IsMulLeftInvariant ν]

/-- Actual left translation in both coordinates preserves the original Borel Radon product. -/
theorem map_mulLeft_radonProd (a : G × K) :
    Measure.map (a * ·) (radonProd μ ν) = radonProd μ ν := by
  let e : (G × K) ≃ₜ (G × K) := Homeomorph.mulLeft a
  change Measure.map e (radonProd μ ν) = radonProd μ ν
  let : (Measure.map e (radonProd μ ν)).Regular := Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [e.measurableEmbedding.integral_map]
  let f' : C_c(G × K, ℝ) :=
    ⟨⟨fun z => f (e z), f.continuous.comp e.continuous⟩,
      f.hasCompactSupport.comp_homeomorph e⟩
  change (∫ z : G × K, f' z ∂(radonProd μ ν)) =
    ∫ z : G × K, f z ∂(radonProd μ ν)
  rw [integral_radonProd μ ν f', integral_radonProd μ ν f]
  change (∫ s : G, ∫ t : K, f (a.1 * s, a.2 * t) ∂ν ∂μ) =
    ∫ s : G, ∫ t : K, f (s, t) ∂ν ∂μ
  calc
    (∫ s : G, ∫ t : K, f (a.1 * s, a.2 * t) ∂ν ∂μ) =
        ∫ s : G, ∫ t : K, f (a.1 * s, t) ∂ν ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s =>
        integral_mul_left_eq_self (μ := ν) (fun t : K => f (a.1 * s, t)) a.2
    _ = ∫ s : G, ∫ t : K, f (s, t) ∂ν ∂μ :=
      integral_mul_left_eq_self (μ := μ) (fun s : G => ∫ t : K, f (s, t) ∂ν) a.1

/-- The original Radon product is left invariant for the literal product group. -/
instance isMulLeftInvariant_radonProd : IsMulLeftInvariant (radonProd μ ν) where
  map_mul_left_eq_self := map_mulLeft_radonProd μ ν

/-- The actual product left translation is measure preserving on the full Borel carrier. -/
theorem measurePreserving_mulLeft_radonProd (a : G × K) :
    MeasurePreserving (a * ·) (radonProd μ ν) (radonProd μ ν) :=
  ⟨(Homeomorph.mulLeft a).measurable, map_mulLeft_radonProd μ ν a⟩

end Invariance

section Nonzero

variable [μ.IsHaarMeasure] [ν.IsHaarMeasure]

private theorem exists_compactSupport_integral_pos
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (η : Measure X) [η.Regular] [η.IsOpenPosMeasure] (x : X) :
    ∃ f : C_c(X, ℝ), 0 < ∫ z : X, f z ∂η := by
  obtain ⟨f, hfCompact, hfNonneg, hfx⟩ := exists_continuous_nonneg_pos x
  let F : C_c(X, ℝ) := ⟨f, hfCompact⟩
  exact ⟨F, integral_pos_of_integrable_nonneg_nonzero f.continuous F.integrable hfNonneg hfx⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
/-- Positive original factor integrals make the actual Radon product nonzero. -/
theorem radonProd_ne_zero : radonProd μ ν ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_compactSupport_integral_pos μ (1 : G)
  obtain ⟨g, hg⟩ := exists_compactSupport_integral_pos ν (1 : K)
  have hpos : 0 < ∫ z : G × K, CompactlySupportedContinuousMap.mulProd f g z ∂(radonProd μ ν) := by
    rw [integral_mulProd μ ν f g]
    exact mul_pos hf hg
  intro hzero
  rw [hzero] at hpos
  simp only [integral_zero_measure] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The constructed Borel Radon product of the original regular Haar measures is a Haar measure. -/
instance isHaarMeasure_radonProd : (radonProd μ ν).IsHaarMeasure := by
  let : NeZero (radonProd μ ν) := ⟨radonProd_ne_zero μ ν⟩
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }

end Nonzero

end

end MeasureTheory.Measure
