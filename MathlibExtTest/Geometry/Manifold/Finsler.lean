/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Finsler
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Tests for Finsler metrics

* The Euclidean norm is a reversible Finsler metric.
* `FinslerTests.tilted`, `F(x, v) = |v| - v / 3` on `ℝ`, is an irreversible Finsler metric
  (`tilted_not_isReversible`), so the axioms do not force absolute homogeneity. Its distance is
  `tilted.edist a b = tiltNorm (b - a)` (`tilted_edist`): `2/3` from `0` to `1` but `4/3` from
  `1` to `0` (`tilted_edist_lt`), which pins that `edist` integrates `F` at the forward velocity.
* A statement shape for closed geodesics of an irreversible Finsler metric on `S²`.
-/

open Manifold Filter Set MeasureTheory
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

/-- The Euclidean metric of `ℝ²` is a reversible Finsler metric. -/
example : (FinslerMetric.euclidean : FinslerMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace ℝ (Fin 2))).IsReversible :=
  FinslerMetric.euclidean_isReversible

/-- Statement shape: an irreversible Finsler metric on `S²` has two or infinitely many closed
geodesics. Closed geodesics are taken with unit speed, so that rescaled parametrizations and
iterates are the same curve, and counted up to time shift (orientation matters: the reverse of a
geodesic of an irreversible metric need not be a geodesic). -/
example : Prop :=
  ∀ F : FinslerMetric (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1), ¬ F.IsReversible →
    let S := {γ : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      F.IsClosedGeodesic γ ∧ F.IsGeodesicOnWithSpeed γ Set.univ 1}
    let r : S → S → Prop := fun γ δ ↦ ∃ s : ℝ, ∀ t, δ.1 t = γ.1 (t + s)
    (∃ γ δ : S, ¬ r γ δ ∧ ∀ ε : S, r γ ε ∨ r δ ε) ∨
      ∀ n : ℕ, ∃ f : Fin n → S, Pairwise fun i j ↦ ¬ r (f i) (f j)

namespace FinslerTests

/-! ### A one-dimensional Randers norm -/

/-- The Minkowski norm `y ↦ |y| - y / 3` on `ℝ`: moving in the positive direction costs `2/3` per
unit of displacement, moving in the negative direction `4/3`. -/
def tiltNorm (y : ℝ) : ℝ := |y| - y / 3

theorem tiltNorm_of_nonneg {y : ℝ} (hy : 0 ≤ y) : tiltNorm y = 2 / 3 * y := by
  rw [tiltNorm, abs_of_nonneg hy]
  ring

theorem tiltNorm_of_nonpos {y : ℝ} (hy : y ≤ 0) : tiltNorm y = -(4 / 3) * y := by
  rw [tiltNorm, abs_of_nonpos hy]
  ring

/-- `tiltNorm` is the larger of its two linear branches. -/
theorem tiltNorm_eq_max (y : ℝ) : tiltNorm y = max (2 / 3 * y) (-(4 / 3) * y) := by
  rcases le_total 0 y with hy | hy
  · rw [tiltNorm_of_nonneg hy, max_eq_left (by linarith)]
  · rw [tiltNorm_of_nonpos hy, max_eq_right (by linarith)]

theorem tiltNorm_nonneg (y : ℝ) : 0 ≤ tiltNorm y := by
  rw [tiltNorm_eq_max]
  rcases le_total 0 y with hy | hy
  · exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by linarith)

theorem tiltNorm_pos {y : ℝ} (hy : y ≠ 0) : 0 < tiltNorm y := by
  rcases hy.lt_or_gt with hy | hy
  · rw [tiltNorm_of_nonpos hy.le]
    linarith
  · rw [tiltNorm_of_nonneg hy.le]
    linarith

theorem tiltNorm_mul {c : ℝ} (hc : 0 < c) (y : ℝ) : tiltNorm (c * y) = c * tiltNorm y := by
  rw [tiltNorm, tiltNorm, abs_mul, abs_of_pos hc]
  ring

theorem continuous_tiltNorm : Continuous tiltNorm :=
  continuous_abs.sub (continuous_id.div_const 3)

/-- Away from `0`, `tiltNorm` is linear near the point. -/
theorem tiltNorm_eventuallyEq_mul {y : ℝ} (hy : y ≠ 0) :
    ∃ s : ℝ, s ≠ 0 ∧ tiltNorm =ᶠ[𝓝 y] fun u ↦ s * u := by
  rcases hy.lt_or_gt with hy | hy
  · refine ⟨-(4 / 3), by norm_num, ?_⟩
    filter_upwards [Iio_mem_nhds hy] with u hu
    exact tiltNorm_of_nonpos (le_of_lt hu)
  · refine ⟨2 / 3, by norm_num, ?_⟩
    filter_upwards [Ioi_mem_nhds hy] with u hu
    exact tiltNorm_of_nonneg (le_of_lt hu)

/-- If `g` agrees near `v` with `u ↦ c ‖u‖²`, the second derivative of `g` at `v` is the bilinear
form `2 c ⟪·, ·⟫`. -/
theorem fderiv_fderiv_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {g : E → ℝ} {v : E} {c : ℝ} (h : g =ᶠ[𝓝 v] fun u ↦ c * ‖u‖ ^ 2) :
    fderiv ℝ (fderiv ℝ g) v = (2 * c) • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
  set L : E →L[ℝ] E →L[ℝ] ℝ := (2 * c) • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) with hL
  have hq (u : E) : HasFDerivAt (fun u ↦ c * ‖u‖ ^ 2) (L u) u := by
    convert (hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul c using 1
    ext w
    simp only [hL, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    change 2 * c * inner ℝ u w = c * (2 * inner ℝ u w)
    ring
  have hd : fderiv ℝ g =ᶠ[𝓝 v] L := by
    filter_upwards [h.eventuallyEq_nhds] with u hu
    exact ((hq u).congr_of_eventuallyEq hu).fderiv
  exact (L.hasFDerivAt.congr_of_eventuallyEq hd).fderiv

/-- The irreversible Finsler metric `F(x, v) = |v| - v / 3` on `ℝ`. -/
def tilted : FinslerMetric 𝓘(ℝ, ℝ) ℝ where
  toFun v := tiltNorm v.2
  continuous_toFun := continuous_tiltNorm.comp
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ) (n := 0)).continuous
  contMDiffOn_toFun := by
    intro v hv
    obtain ⟨s, -, hs⟩ := tiltNorm_eventuallyEq_mul (show @id ℝ v.2 ≠ 0 from hv)
    have h1 : ContDiffAt ℝ ∞ tiltNorm (@id ℝ v.2) :=
      (contDiffAt_const.mul contDiffAt_id).congr_of_eventuallyEq hs
    have h2 := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ) (n := ∞)).contMDiffAt (x := v)
    exact (h1.contMDiffAt.comp v h2).contMDiffWithinAt
  pos v hv := tiltNorm_pos hv
  homogeneous x v c hc := tiltNorm_mul hc v
  hessian_pos x v w hv hw := by
    obtain ⟨s, hs0, hs⟩ := tiltNorm_eventuallyEq_mul hv
    have hsq : (fun u : ℝ ↦ tiltNorm u ^ 2) =ᶠ[𝓝 v] fun u ↦ s ^ 2 * ‖u‖ ^ 2 := by
      filter_upwards [hs] with u hu
      rw [hu, Real.norm_eq_abs, sq_abs]
      ring
    change 0 < fderiv ℝ (fderiv ℝ fun u : ℝ ↦ tiltNorm u ^ 2) v w w
    rw [fderiv_fderiv_eq_of_eventuallyEq hsq]
    have hww : 0 < inner ℝ w w := real_inner_self_pos.mpr hw
    have hs2 : 0 < s ^ 2 := by positivity
    exact mul_pos (mul_pos two_pos hs2) hww

theorem tilted_apply (x y : ℝ) : tilted (⟨x, y⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) = tiltNorm y := rfl

/-- `tilted` is not reversible: `F(0, -1) = 4/3` but `F(0, 1) = 2/3`. In particular the axioms of
`FinslerMetric` do not force absolute homogeneity `F(c v) = |c| F(v)`. -/
theorem tilted_not_isReversible : ¬ tilted.IsReversible := fun h ↦ by
  have h1 : tiltNorm (-1) = tiltNorm 1 := h ⟨(0 : ℝ), (1 : ℝ)⟩
  rw [tiltNorm_of_nonpos (by norm_num), tiltNorm_of_nonneg (by norm_num)] at h1
  norm_num at h1

/-! ### Distances of `tilted` -/

/-- The velocity of a path `γ` in `ℝ` at time `t`, as a real number. -/
def velocity {a b : ℝ} (γ : Path a b) (t : I) : ℝ := mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) γ t 1

/-- The velocity of a path is the derivative, within `[0, 1]`, of its extension to `ℝ`. -/
theorem velocity_eq_derivWithin {a b : ℝ} (γ : Path a b) (t : I) :
    velocity γ t = derivWithin (γ ∘ projIcc 0 1 zero_le_one) (Icc 0 1) t := by
  rw [velocity, ← mfderivWithin_comp_projIcc_one, mfderivWithin_eq_fderivWithin]
  rfl

theorem contDiffOn_comp_projIcc {a b : ℝ} {γ : Path a b} (hγ : CMDiff 1 γ) :
    ContDiffOn ℝ 1 (γ ∘ projIcc 0 1 zero_le_one) (Icc 0 1) :=
  contMDiffOn_iff_contDiffOn.mp (contMDiffOn_comp_projIcc_iff.mpr hγ)

theorem continuous_velocity {a b : ℝ} {γ : Path a b} (hγ : CMDiff 1 γ) :
    Continuous (velocity γ) := by
  have hd := (contDiffOn_comp_projIcc hγ).continuousOn_derivWithin
    (uniqueDiffOn_Icc zero_lt_one) le_rfl
  rw [show velocity γ = fun t : I ↦ derivWithin (γ ∘ projIcc 0 1 zero_le_one) (Icc 0 1) t from
    funext (velocity_eq_derivWithin γ)]
  exact hd.comp_continuous continuous_subtype_val Subtype.prop

/-- Displacement: the velocity of a `C¹` path from `a` to `b` integrates to `b - a`. -/
theorem integral_velocity {a b : ℝ} {γ : Path a b} (hγ : CMDiff 1 γ) :
    ∫ t, velocity γ t = b - a := by
  set e := γ ∘ projIcc 0 1 zero_le_one
  calc ∫ t, velocity γ t = ∫ t : Icc (0 : ℝ) 1, derivWithin e (Icc 0 1) t
        ∂(Measure.comap Subtype.val volume) := by
        simp_rw [velocity_eq_derivWithin]
        rfl
    _ = ∫ s in Icc (0 : ℝ) 1, derivWithin e (Icc 0 1) s :=
        integral_subtype_comap measurableSet_Icc _
    _ = ∫ s in (0 : ℝ)..1, derivWithin e (Icc 0 1) s := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    _ = e 1 - e 0 :=
        intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc (contDiffOn_comp_projIcc hγ)
          zero_le_one
    _ = b - a := by simp [e]

/-- The affine path `t ↦ a + t (b - a)` from `a` to `b`. -/
def segmentPath (a b : ℝ) : Path a b where
  toFun t := a + (t : ℝ) * (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem segmentPath_comp_projIcc (a b : ℝ) :
    EqOn (segmentPath a b ∘ projIcc 0 1 zero_le_one) (fun s ↦ a + s * (b - a)) (Icc 0 1) :=
  fun s hs ↦ by simp [segmentPath, projIcc_of_mem zero_le_one hs]

theorem contMDiff_segmentPath (a b : ℝ) : CMDiff 1 (segmentPath a b : I → ℝ) := by
  refine contMDiffOn_comp_projIcc_iff.mp (contMDiffOn_iff_contDiffOn.mpr ?_)
  exact (by fun_prop : ContDiff ℝ 1 fun s : ℝ ↦ a + s * (b - a)).contDiffOn.congr
    (segmentPath_comp_projIcc a b)

theorem velocity_segmentPath (a b : ℝ) (t : I) : velocity (segmentPath a b) t = b - a := by
  rw [velocity_eq_derivWithin,
    derivWithin_congr (segmentPath_comp_projIcc a b) (segmentPath_comp_projIcc a b t.2)]
  have hd : HasDerivAt (fun s : ℝ ↦ a + s * (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id (t : ℝ)).mul_const (b - a)).const_add a
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one _ t.2)

/-- A linear lower bound `k y ≤ tiltNorm y` integrates to a lower bound `k (b - a)` on the
`tilted`-length of every `C¹` path from `a` to `b`. -/
theorem ofReal_le_length {a b k : ℝ} {γ : Path a b} (hγ : CMDiff 1 γ)
    (hk : ∀ y, k * y ≤ tiltNorm y) :
    ENNReal.ofReal (k * (b - a)) ≤ ∫⁻ t, ENNReal.ofReal (tiltNorm (velocity γ t)) := by
  have hv := continuous_velocity hγ
  have hvi : Integrable (velocity γ) :=
    hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hni : Integrable fun t ↦ tiltNorm (velocity γ t) :=
    (continuous_tiltNorm.comp hv).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hni (ae_of_all _ fun t ↦ tiltNorm_nonneg _),
    ← integral_velocity hγ, ← integral_const_mul]
  exact ENNReal.ofReal_le_ofReal (integral_mono (hvi.const_mul k) hni fun t ↦ hk _)

/-- The distances of `tilted`: `d(a, b) = tiltNorm (b - a)`, which is `2/3 (b - a)` for `a ≤ b`
and `4/3 (a - b)` for `b ≤ a`. The affine path realizes it; every `C¹` path is at least as long,
by `ofReal_le_length` applied to both linear branches of `tiltNorm`. -/
theorem tilted_edist (a b : ℝ) : tilted.edist a b = ENNReal.ofReal (tiltNorm (b - a)) := by
  refine le_antisymm ?_ ?_
  · refine (iInf₂_le (segmentPath a b) (contMDiff_segmentPath a b)).trans_eq ?_
    change ∫⁻ t, ENNReal.ofReal (tiltNorm (velocity (segmentPath a b) t)) = _
    simp [velocity_segmentPath]
  · refine le_iInf₂ fun γ hγ ↦ ?_
    change _ ≤ ∫⁻ t, ENNReal.ofReal (tiltNorm (velocity γ t))
    rw [tiltNorm_eq_max, ENNReal.ofReal_max]
    refine max_le (ofReal_le_length hγ fun y ↦ ?_) (ofReal_le_length hγ fun y ↦ ?_) <;>
      rw [tiltNorm_eq_max]
    exacts [le_max_left _ _, le_max_right _ _]

theorem tilted_edist_zero_one : tilted.edist 0 1 = ENNReal.ofReal (2 / 3) := by
  rw [tilted_edist, sub_zero, tiltNorm_of_nonneg zero_le_one, mul_one]

theorem tilted_edist_one_zero : tilted.edist 1 0 = ENNReal.ofReal (4 / 3) := by
  rw [tilted_edist, zero_sub, tiltNorm_of_nonpos (by norm_num)]
  norm_num

/-- The forward and reverse distances between `0` and `1` differ, so `edist` integrates `F` at the
forward velocity: with the reversed velocity both values would swap. -/
theorem tilted_edist_lt : tilted.edist 0 1 < tilted.edist 1 0 := by
  rw [tilted_edist_zero_one, tilted_edist_one_zero, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end FinslerTests
