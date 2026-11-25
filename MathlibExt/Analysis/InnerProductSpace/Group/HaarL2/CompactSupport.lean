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

public import MathlibExt.MeasureTheory.Function.CompactApproximation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The actual compact-support inclusion into Hilbert-valued Haar L2

Continuous compact-support vectors map into the original Lp H 2 measure
carrier with their literal almost-everywhere values and original integral
inner product. Compact-local Radon approximation proves dense range without
global normality, countability, separability or sigma-finiteness assumptions.

The construction works for regular Radon measures and specializes to the
original Haar measure on every locally compact group. Its target stays the
actual Lp space; no completed-tensor comparison is selected as data here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ENNReal NNReal Topology CompactlySupported InnerProductSpace

namespace MeasureTheory
namespace HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The compact-support linear inclusion into the Hilbert-valued L2 space. -/
def compactSupportInclusion : C_c(G, H) →ₗ[ℂ] Lp H 2 μ where
  toFun f :=
    ((map_continuous f).memLp_of_hasCompactSupport f.hasCompactSupport).toLp (f : G → H)
  map_add' f g := by
    exact MemLp.toLp_add
      ((map_continuous f).memLp_of_hasCompactSupport f.hasCompactSupport)
      ((map_continuous g).memLp_of_hasCompactSupport g.hasCompactSupport)
  map_smul' c f := by
    have hf : MemLp (f : G → H) 2 μ :=
      (map_continuous f).memLp_of_hasCompactSupport f.hasCompactSupport
    have hcf : MemLp ((c • f : C_c(G, H)) : G → H) 2 μ :=
      (map_continuous (c • f)).memLp_of_hasCompactSupport (c • f).hasCompactSupport
    apply Lp.ext
    filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul c (hf.toLp (f : G → H))] with s h₁ h₂ h₃
    rw [RingHom.id_apply, h₁, h₃]
    change c • f s = c • (hf.toLp (f : G → H)) s
    rw [h₂]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The inclusion has the exact compact-support representative almost everywhere. -/
theorem compactSupportInclusion_ae_eq (f : C_c(G, H)) :
    compactSupportInclusion (H := H) μ f =ᵐ[μ] (f : G → H) :=
  MemLp.coeFn_toLp ((map_continuous f).memLp_of_hasCompactSupport f.hasCompactSupport)

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The compact-support integral is the L2 inner product, linear in the second variable. -/
theorem compactSupportInclusion_inner (f g : C_c(G, H)) :
    ⟪compactSupportInclusion (H := H) μ f, compactSupportInclusion μ g⟫_ℂ =
      ∫ s : G, ⟪f s, g s⟫_ℂ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactSupportInclusion_ae_eq μ f,
    compactSupportInclusion_ae_eq μ g] with s hf hg
  rw [hf, hg]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The inclusion preserves the exact squared integral norm. -/
theorem norm_compactSupportInclusion_sq (f : C_c(G, H)) :
    ‖compactSupportInclusion (H := H) μ f‖ ^ 2 = ∫ s : G, ‖f s‖ ^ 2 ∂μ := by
  let ζ := compactSupportInclusion (H := H) μ f
  calc
    ‖ζ‖ ^ 2 = (RCLike.re (inner ℂ ζ ζ) : ℝ) :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) ζ
    _ = RCLike.re (∫ s : G, inner ℂ (ζ s) (ζ s) ∂μ) := rfl
    _ = ∫ s : G, (RCLike.re (inner ℂ (ζ s) (ζ s)) : ℝ) ∂μ :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) ζ ζ)).symm
    _ = ∫ s : G, ‖ζ s‖ ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s =>
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (ζ s)).symm)
    _ = ∫ s : G, ‖f s‖ ^ 2 ∂μ :=
      integral_congr_ae ((compactSupportInclusion_ae_eq μ f).mono fun s hs =>
        congrArg (fun z : H => ‖z‖ ^ 2) hs)

variable [R1Space G] [LocallyCompactSpace G]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `G` is locally compact and R₁.

Compact-support vectors are dense in the Hilbert-valued L2 space for a regular measure. -/
theorem denseRange_compactSupportInclusion :
    DenseRange (compactSupportInclusion (H := H) μ) := by
  intro ξ
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨f, hfcomp, happrox, hfcont, hf⟩ :=
    MeasureTheory.locallyCompactVectorApprox μ ENNReal.ofNat_ne_top (Lp.memLp ξ)
      (ENNReal.ofReal_pos.mpr hhalf).ne'
  let F : C_c(G, H) := ⟨⟨f, hfcont⟩, hfcomp⟩
  have hF : compactSupportInclusion (H := H) μ F = hf.toLp f := by
    apply Lp.ext
    exact (compactSupportInclusion_ae_eq μ F).trans hf.coeFn_toLp.symm
  have hedist : edist ξ (compactSupportInclusion (H := H) μ F) =
      eLpNorm ((ξ : G → H) - f) 2 μ := by
    rw [hF]
    simpa only [Lp.toLp_coeFn] using
      (Lp.edist_toLp_toLp (ξ : G → H) f (Lp.memLp ξ) hf)
  have hdist : dist ξ (compactSupportInclusion (H := H) μ F) ≤ ε / 2 := by
    have h : ENNReal.ofReal (dist ξ (compactSupportInclusion (H := H) μ F)) ≤
        ENNReal.ofReal (ε / 2) := by
      rw [← edist_dist, hedist]
      exact happrox
    exact (ENNReal.ofReal_le_ofReal_iff hhalf.le).mp h
  exact ⟨compactSupportInclusion (H := H) μ F, ⟨F, rfl⟩, hdist.trans_lt (half_lt_self hε)⟩

end

end HaarL2
end MeasureTheory
