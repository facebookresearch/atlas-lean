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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterCompletion
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Point-norm continuity of the original full Haar character action

The compact-open character pairing is jointly continuous. Its difference
against a fixed character, multiplied by the original compact-support
coefficient, has one fixed compact support. The unrestricted compact-support
parametric-integral theorem gives continuity of its original L1 distance,
without first/second countability of the group or dual parameter space.

The original full norm is bounded by L1 on the dense raw core. The computed
completed character automorphisms are isometries, so the standard dense-core
estimate proves every full-completion orbit continuous. These are only the
facts needed to construct the original dual action; no Takai or compactness
comparison theorem is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped CStarAlgebra

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

attribute [local instance] fullCovariantCompletionCStarAlgebra

omit [IsTopologicalGroup G] [mu.Regular] in
/-- The original L1 character-distance integral is continuous on the full compact-open dual. -/
theorem continuous_l1CharacterDistance (chi0 : PontryaginDual G) (f : Carrier mu alpha) :
    Continuous (fun chi : PontryaginDual G =>
      l1Gauge mu alpha (characterModulation mu alpha chi f - characterModulation mu alpha chi0 f)) := by
  let F : PontryaginDual G → G → ℝ := fun chi s =>
    ‖((chi s : ℂ) - (chi0 s : ℂ)) • f s‖
  have heval : Continuous (fun p : PontryaginDual G × G => (p.1 p.2 : ℂ)) := by
    change Continuous (fun p : (G →ₜ* Circle) × G => (p.1 p.2 : ℂ))
    exact continuous_subtype_val.comp continuous_eval
  have hfixed : Continuous (fun p : PontryaginDual G × G => (chi0 p.2 : ℂ)) :=
    (continuous_subtype_val.comp (map_continuous chi0)).comp continuous_snd
  have hF : Continuous (Function.uncurry F) :=
    ((heval.sub hfixed).smul ((map_continuous (toCc mu alpha f)).comp continuous_snd)).norm
  have hsupport : ∀ chi s, chi ∈ (Set.univ : Set (PontryaginDual G)) →
      s ∉ tsupport (toCc mu alpha f) → F chi s = 0 := by
    intro chi s _ hs
    dsimp only [F]
    rw [image_eq_zero_of_notMem_tsupport hs, smul_zero, norm_zero]
  have hIntegral := continuousOn_integral_of_compact_support
    (f := F) (s := Set.univ) (μ := mu) (toCc mu alpha f).hasCompactSupport
    hF.continuousOn hsupport
  have hEq (chi : PontryaginDual G) :
      l1Gauge mu alpha (characterModulation mu alpha chi f - characterModulation mu alpha chi0 f) =
        ∫ s : G, F chi s ∂mu := by
    unfold l1Gauge
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      change ‖(chi s : ℂ) • f s - (chi0 s : ℂ) • f s‖ = F chi s
      rw [← sub_smul]
  exact (continuousOn_univ.mp hIntegral).congr (fun chi => (hEq chi).symm)

omit [mu.Regular] in
/-- The actual completed raw-vector character distance is bounded by the original L1 distance. -/
theorem dist_completedCharacterEquiv_core_le
    (chi eta : PontryaginDual G) (f : Carrier mu alpha) :
    dist (completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f))
        (completedCharacterEquiv mu alpha eta (toFullCovariantCompletion mu alpha f)) ≤
      l1Gauge mu alpha (characterModulation mu alpha chi f - characterModulation mu alpha eta f) := by
  rw [completedCharacterEquiv_apply, completedCharacterEquiv_apply, dist_eq_norm, ← map_sub]
  change ‖(maximalCStarSeminorm mu alpha).toNonUnitalCompletion
    (characterModulation mu alpha chi f - characterModulation mu alpha eta f)‖ ≤ _
  rw [CStarSeminorm.norm_toNonUnitalCompletion]
  exact maximalCStarSeminorm_le_l1Gauge mu alpha _

omit [mu.Regular] in
/-- Every original dense-core character orbit is continuous in the actual full norm. -/
theorem continuous_completedCharacterEquiv_core (f : Carrier mu alpha) :
    Continuous (fun chi : PontryaginDual G =>
      completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f)) := by
  rw [continuous_iff_continuousAt]
  intro chi0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hzero : l1Gauge mu alpha
      (characterModulation mu alpha chi0 f - characterModulation mu alpha chi0 f) = 0 := by
    rw [sub_self, l1Gauge_zero]
  have hnear := ((continuous_l1CharacterDistance mu alpha chi0 f).continuousAt
    (x := chi0)).tendsto
  rw [hzero] at hnear
  filter_upwards [(Metric.tendsto_nhds.mp hnear) epsilon hepsilon] with chi hchi
  have hsmall : l1Gauge mu alpha
      (characterModulation mu alpha chi f - characterModulation mu alpha chi0 f) < epsilon := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (l1Gauge_nonneg mu alpha _)] using hchi
  exact (dist_completedCharacterEquiv_core_le mu alpha chi chi0 f).trans_lt hsmall

omit [mu.Regular] in
/-- Every original full-completion character orbit is point-norm continuous. -/
theorem continuous_completedCharacterEquiv_orbit (x : FullCovariantCompletion mu alpha) :
    Continuous (fun chi : PontryaginDual G => completedCharacterEquiv mu alpha chi x) := by
  rw [continuous_iff_continuousAt]
  intro chi0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := div_pos hepsilon (by norm_num)
  obtain ⟨f, hf⟩ := (denseRange_toFullCovariantCompletion mu alpha).exists_dist_lt x hthird
  have hf' : dist (toFullCovariantCompletion mu alpha f) x < epsilon / 3 := by
    simpa only [dist_comm] using hf
  have hdist (chi : PontryaginDual G) (y z : FullCovariantCompletion mu alpha) :
      dist (completedCharacterEquiv mu alpha chi y) (completedCharacterEquiv mu alpha chi z) = dist y z :=
    (StarAlgEquiv.isometry (completedCharacterEquiv mu alpha chi)).dist_eq y z
  have hcore := (continuous_completedCharacterEquiv_core mu alpha f).continuousAt (x := chi0)
  filter_upwards [(Metric.tendsto_nhds.mp hcore.tendsto) (epsilon / 3) hthird] with chi hchi
  calc
    dist (completedCharacterEquiv mu alpha chi x) (completedCharacterEquiv mu alpha chi0 x) ≤
      dist (completedCharacterEquiv mu alpha chi x)
          (completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f)) +
        dist (completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f))
          (completedCharacterEquiv mu alpha chi0 x) := dist_triangle _ _ _
    _ ≤ dist x (toFullCovariantCompletion mu alpha f) +
        (dist (completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f))
          (completedCharacterEquiv mu alpha chi0 (toFullCovariantCompletion mu alpha f)) +
          dist (toFullCovariantCompletion mu alpha f) x) := by
      rw [hdist]
      exact add_le_add le_rfl (by
        simpa only [hdist] using dist_triangle
          (completedCharacterEquiv mu alpha chi (toFullCovariantCompletion mu alpha f))
          (completedCharacterEquiv mu alpha chi0 (toFullCovariantCompletion mu alpha f))
          (completedCharacterEquiv mu alpha chi0 x))
    _ < epsilon / 3 + (epsilon / 3 + epsilon / 3) := add_lt_add hf (add_lt_add hchi hf')
    _ = epsilon := by ring

end HaarTwistedCore
