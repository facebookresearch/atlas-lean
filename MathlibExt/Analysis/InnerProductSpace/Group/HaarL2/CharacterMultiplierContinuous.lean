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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CharacterMultiplier
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Strong continuity of compact-open character multiplication

For a locally compact Borel topological group, regular measure `μ` and complete complex Hilbert
space `H`, the character multipliers have norm-continuous vector orbits `χ ↦ U_χξ` on `Lp H 2
μ`.

They form a strongly continuous unitary representation of the compact-open character group. Haar
invariance, countability, separability and sigma-finiteness are not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ENNReal Topology CompactlySupported InnerProductSpace

namespace MeasureTheory
namespace HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Norm-continuous character orbit of an L² vector.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular measure and `H` a complete
complex Hilbert space. Let `U_χξ(s)=χ(s) • ξ(s)` on `Lp H 2 μ`, with compact-open topology
on the character group. for every `ξ∈Lp H 2 μ`, `χ ↦ characterMultiplier μ χ ξ` is
continuous in the Hilbert norm. -/
theorem characterMultiplier_continuous (ξ : Lp H 2 μ) :
    Continuous fun χ : PontryaginDual G => characterMultiplier (H := H) μ χ ξ := by
  have hcompact (f : C_c(G, H)) :
      Continuous fun χ : PontryaginDual G =>
        characterMultiplier (H := H) μ χ (compactSupportInclusion μ f) := by
    have heval : Continuous fun p : PontryaginDual G × G => ((p.1 p.2 : Circle) : ℂ) := by
      change Continuous (fun p : (G →ₜ* Circle) × G => ((p.1 p.2 : Circle) : ℂ))
      exact continuous_subtype_val.comp (continuous_fst.eval continuous_snd)
    let F : PontryaginDual G → G → H := fun χ s => ((χ s : Circle) : ℂ) • f s
    have hF : Continuous F.uncurry := heval.smul ((map_continuous f).comp continuous_snd)
    rw [continuous_iff_continuousAt]
    intro χ₀
    let I : PontryaginDual G → ℝ := fun χ => ∫ s : G, ‖F χ s - F χ₀ s‖ ^ 2 ∂μ
    have hF₀ : Continuous (fun p : PontryaginDual G × G => F χ₀ p.2) :=
      ((continuous_subtype_val.comp (map_continuous χ₀)).comp continuous_snd).smul
        ((map_continuous f).comp continuous_snd)
    have hdiff : Continuous (fun p : PontryaginDual G × G => ‖F p.1 p.2 - F χ₀ p.2‖ ^ 2) :=
      (hF.sub hF₀).norm.pow 2
    have hsupp : ∀ χ s, χ ∈ (Set.univ : Set (PontryaginDual G)) → s ∉ tsupport f →
        ‖F χ s - F χ₀ s‖ ^ 2 = 0 := by
      intro χ s _ hs
      have hfs : f s = 0 := image_eq_zero_of_notMem_tsupport hs
      simp only [F, hfs, smul_zero, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hI : ContinuousAt I χ₀ :=
      (continuousOn_integral_of_compact_support (μ := μ) f.hasCompactSupport
        hdiff.continuousOn hsupp).continuousAt Filter.univ_mem
    have hN (χ : PontryaginDual G) :
        dist (characterMultiplier μ χ (compactSupportInclusion μ f))
          (characterMultiplier μ χ₀ (compactSupportInclusion μ f)) ^ 2 = I χ := by
      rw [dist_eq_norm]
      let ζ := characterMultiplier μ χ (compactSupportInclusion μ f) -
        characterMultiplier μ χ₀ (compactSupportInclusion μ f)
      change ‖ζ‖ ^ 2 = I χ
      calc
        ‖ζ‖ ^ 2 = (RCLike.re (inner ℂ ζ ζ) : ℝ) :=
          InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) ζ
        _ = ∫ s : G, ‖ζ s‖ ^ 2 ∂μ := by
          rw [L2.inner_def]
          rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) ζ ζ)]
          exact integral_congr_ae (Eventually.of_forall fun s =>
            (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (ζ s)).symm)
        _ = I χ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (characterMultiplier μ χ (compactSupportInclusion μ f))
              (characterMultiplier μ χ₀ (compactSupportInclusion μ f)),
            characterMultiplier_ae_eq μ χ (compactSupportInclusion μ f),
            characterMultiplier_ae_eq μ χ₀ (compactSupportInclusion μ f),
            compactSupportInclusion_ae_eq μ f] with s h₁ h₂ h₃ h₄
          rw [h₁]
          change ‖characterMultiplier μ χ (compactSupportInclusion μ f) s -
            characterMultiplier μ χ₀ (compactSupportInclusion μ f) s‖ ^ 2 = ‖F χ s - F χ₀ s‖ ^ 2
          rw [h₂, h₃, h₄]
    have hzero : I χ₀ = 0 := by
      simp only [I, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero]
    have htendsto : Tendsto I (𝓝 χ₀) (𝓝 0) := by
      simpa only [ContinuousAt, hzero] using hI
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have hevent := (Metric.tendsto_nhds.mp htendsto) (ε ^ 2) (sq_pos_of_pos hε)
    filter_upwards [hevent] with χ hχ
    have hsq : dist (characterMultiplier μ χ (compactSupportInclusion μ f))
        (characterMultiplier μ χ₀ (compactSupportInclusion μ f)) ^ 2 < ε ^ 2 := by
      rw [hN]
      exact (le_abs_self (I χ)).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hχ)
    exact (sq_lt_sq₀ dist_nonneg hε.le).mp hsq
  rw [continuous_iff_continuousAt]
  intro χ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨η, ⟨f, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (denseRange_compactSupportInclusion (H := H) μ ξ) (ε / 4) hquarter
  have hηcont : ContinuousAt (fun χ : PontryaginDual G =>
      characterMultiplier (H := H) μ χ (compactSupportInclusion μ f)) χ₀ := (hcompact f).continuousAt
  have hevent := (Metric.tendsto_nhds.mp hηcont) (ε / 2) (half_pos hε)
  have hisometry (χ : PontryaginDual G) (u v : Lp H 2 μ) :
      dist (characterMultiplier μ χ u) (characterMultiplier μ χ v) = dist u v :=
    (Unitary.linearIsometryEquiv (characterMultiplierUnitary (H := H) μ χ)).isometry.dist_eq u v
  filter_upwards [hevent] with χ hχ
  calc
    _ ≤ dist (characterMultiplier μ χ ξ) (characterMultiplier μ χ (compactSupportInclusion μ f)) +
      dist (characterMultiplier μ χ (compactSupportInclusion μ f)) (characterMultiplier μ χ₀ ξ) :=
        dist_triangle _ _ _
    _ ≤ dist (characterMultiplier μ χ ξ) (characterMultiplier μ χ (compactSupportInclusion μ f)) +
      (dist (characterMultiplier μ χ (compactSupportInclusion μ f))
        (characterMultiplier μ χ₀ (compactSupportInclusion μ f)) +
      dist (characterMultiplier μ χ₀ (compactSupportInclusion μ f)) (characterMultiplier μ χ₀ ξ)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
    _ = dist ξ (compactSupportInclusion μ f) +
      (dist (characterMultiplier μ χ (compactSupportInclusion μ f))
        (characterMultiplier μ χ₀ (compactSupportInclusion μ f)) +
      dist (compactSupportInclusion μ f) ξ) := by rw [hisometry, hisometry]
    _ < ε := by rw [dist_comm (compactSupportInclusion μ f) ξ]; linarith

/-- **Strongly continuous character representation on Hilbert-valued L².** Let `G` be a
locally compact topological group with its Borel structure, `μ` a regular measure and `H`
a complete complex Hilbert space. Let `U_χξ(s)=χ(s) • ξ(s)` on `Lp H 2 μ`, with
compact-open topology on the character group. `characterMultiplierRepresentation μ :
PontryaginDual G → U(Lp H 2 μ)` has operator value `χ ↦ U_χ`. -/
def characterMultiplierRepresentation :
    StronglyContinuousUnitaryRepresentation (PontryaginDual G) (Lp H 2 μ) where
  toMonoidHom := characterMultiplierUnitaryHom (H := H) μ
  continuous_orbit ξ := by
    change Continuous fun χ : PontryaginDual G => characterMultiplier (H := H) μ χ ξ
    exact characterMultiplier_continuous μ ξ

end

end HaarL2
end MeasureTheory
