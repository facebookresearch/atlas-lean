/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Symmetric

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite frames in Hilbert spaces

A finite frame is a finite family of vectors that spans a Hilbert space in a
stable way: the squared norms of the inner products with the family are
comparable to the squared norm of the vector. Frames generalize orthonormal
bases by allowing redundancy: unlike a basis, a frame need not be linearly
independent, and the same vector can be expanded in many ways. The frame
operator `S x = ∑ i, ⟪f i, x⟫_𝕜 • f i` is self-adjoint and invertible, and its
inverse produces the canonical dual frame and the reconstruction formula
`x = ∑ i, ⟪f i, S⁻¹ x⟫_𝕜 • f i`.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the Bessel inequality, Parseval's identity, the spectral theorem for compact
self-adjoint operators, and the Fredholm alternative), not one of the 72 v1
targets: v1 covers orthonormal bases (targets 51-54, 60) but has no frames,
no frame operator, and no reconstruction formula. It is not in the pinned
Mathlib or in base MathlibExt: Mathlib has orthonormal bases, the Bessel /
Parseval identities, and rank-one operators, but no frame operator or dual
frame. See e.g. Christensen, *An Introduction to Frames and Riesz Bases*,
Chapter 5, for the classical statements.

## Main declarations

* `FiniteFrame.IsFrame` : the frame inequalities with bounds `A`, `B`.
* `FiniteFrame.frameOperator` : the frame operator `∑ i, rankOne (f i) (f i)`.
* `FiniteFrame.isSelfAdjoint_frameOperator` : the frame operator is self-adjoint.
* `FiniteFrame.isUnit_frameOperator` : the frame operator is a unit.
* `FiniteFrame.frameOperatorInv` : the inverse frame operator `S⁻¹`.
* `FiniteFrame.frame_reconstruction` : `x = ∑ i, ⟪f i, S⁻¹ x⟫_𝕜 • f i`.
* `FiniteFrame.dualFrame` : the canonical dual frame `S⁻¹ (f i)`.
* `FiniteFrame.isFrame_dualFrame` : the dual frame is a frame with reciprocal
  bounds `1 / B`, `1 / A`.
* `FiniteFrame.frameOperator_eq_smul_one_of_isTightFrame` : a tight frame
  (equal bounds) has frame operator `A • 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.FiniteFrame

open scoped _root_.InnerProductSpace
open _root_.InnerProductSpace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Fintype ι]

/-- A finite family `f` in a Hilbert space is a frame with frame bounds `A`
and `B` if the squared norms of the inner products `⟪f i, x⟫_𝕜` are comparable
to `‖x‖²`, uniformly in `x`. -/
def IsFrame (f : ι → E) (A B : ℝ) : Prop :=
  0 < A ∧ 0 < B ∧ ∀ x : E,
    A * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 ∧ ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 ≤ B * ‖x‖ ^ 2

/-- The lower frame bound is positive. -/
theorem IsFrame.pos_left {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) : 0 < A :=
  hf.1

/-- The upper frame bound is positive. -/
theorem IsFrame.pos_right {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) : 0 < B :=
  hf.2.1

/-- The lower frame inequality. -/
theorem IsFrame.lower {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) (x : E) :
    A * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 :=
  (hf.2.2 x).1

/-- The upper frame inequality. -/
theorem IsFrame.upper {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) (x : E) :
    ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 ≤ B * ‖x‖ ^ 2 :=
  (hf.2.2 x).2

/-- The frame operator of a finite family: `S x = ∑ i, ⟪f i, x⟫_𝕜 • f i`. -/
noncomputable def frameOperator (f : ι → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (f i) (f i)

/-- The frame operator applied to a vector. -/
theorem frameOperator_apply (f : ι → E) (x : E) :
    frameOperator (𝕜 := 𝕜) f x = ∑ i, ⟪f i, x⟫_𝕜 • f i := by
  simp [frameOperator]

/-- The inner product of the frame operator with a second vector, expanded in
the frame coefficients. -/
theorem inner_frameOperator_apply (f : ι → E) (x y : E) :
    ⟪frameOperator (𝕜 := 𝕜) f x, y⟫_𝕜
      = ∑ i, (starRingEnd 𝕜) ⟪f i, x⟫_𝕜 * ⟪f i, y⟫_𝕜 := by
  rw [frameOperator_apply, sum_inner]
  exact Finset.sum_congr rfl fun i _ => inner_smul_left _ _ _

/-- The frame operator is determined by the frame coefficients:
`⟪S x, x⟫_𝕜` is the sum of the squared coefficient norms. -/
theorem inner_frameOperator_apply_self (f : ι → E) (x : E) :
    ⟪frameOperator (𝕜 := 𝕜) f x, x⟫_𝕜
      = ((∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_frameOperator_apply, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul, RCLike.ofReal_pow]

/-- The real part of `⟪S x, x⟫_𝕜` is the sum of the squared coefficient norms. -/
theorem re_inner_frameOperator_apply_self (f : ι → E) (x : E) :
    RCLike.re ⟪frameOperator (𝕜 := 𝕜) f x, x⟫_𝕜 = ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 := by
  rw [inner_frameOperator_apply_self]
  simp

/-- Cauchy-Schwarz for the frame coefficients: the squared norm of the
sum of coefficient products is bounded by the product of the sums of
squared coefficient norms. -/
theorem sq_norm_inner_frameOperator_apply_le (f : ι → E) (x y : E) :
    ‖⟪frameOperator (𝕜 := 𝕜) f x, y⟫_𝕜‖ ^ 2
      ≤ (∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2) * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := by
  rw [inner_frameOperator_apply]
  calc ‖∑ i, (starRingEnd 𝕜) ⟪f i, x⟫_𝕜 * ⟪f i, y⟫_𝕜‖ ^ 2
      ≤ (∑ i, ‖⟪f i, x⟫_𝕜‖ * ‖⟪f i, y⟫_𝕜‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans_eq ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ (∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2) * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _

variable [CompleteSpace E]

/-- The frame operator is self-adjoint. -/
theorem isSelfAdjoint_frameOperator (f : ι → E) :
    IsSelfAdjoint (frameOperator (𝕜 := 𝕜) f) := by
  rw [IsSelfAdjoint, star_eq_adjoint]
  simp [frameOperator, map_sum]

omit [CompleteSpace E] in
/-- The frame operator is bounded below by the lower frame bound. -/
theorem le_norm_frameOperator_apply {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B)
    (x : E) : A * ‖x‖ ≤ ‖frameOperator (𝕜 := 𝕜) f x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : A * ‖x‖ ^ 2 ≤ ‖frameOperator (𝕜 := 𝕜) f x‖ * ‖x‖ := by
    calc A * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 := hf.lower x
      _ = RCLike.re ⟪frameOperator (𝕜 := 𝕜) f x, x⟫_𝕜 :=
        (re_inner_frameOperator_apply_self f x).symm
      _ ≤ ‖⟪frameOperator (𝕜 := 𝕜) f x, x⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖frameOperator (𝕜 := 𝕜) f x‖ * ‖x‖ := norm_inner_le_norm _ _
  have h2 : A * ‖x‖ * ‖x‖ ≤ ‖frameOperator (𝕜 := 𝕜) f x‖ * ‖x‖ := by
    rw [mul_assoc, ← pow_two]
    exact h1
  exact le_of_mul_le_mul_right h2 hxpos

/-- The frame operator of a frame is a unit: it is bounded below and
self-adjoint, so it is injective with closed range whose orthogonal complement
is trivial. -/
theorem isUnit_frameOperator {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) :
    IsUnit (frameOperator (𝕜 := 𝕜) f) := by
  set S := frameOperator (𝕜 := 𝕜) f with hS
  have hbelow : ∀ x : E, A * ‖x‖ ≤ ‖S x‖ :=
    fun x => le_norm_frameOperator_apply hf x
  have hinj : Function.Injective S := by
    intro x y hxy
    have h0 : S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hle := hbelow (x - y)
    rw [h0, norm_zero] at hle
    have hnorm : ‖x - y‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hpos' : 0 < A * ‖x - y‖ := mul_pos hf.pos_left hpos
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hanti : AntilipschitzWith ⟨A⁻¹, inv_nonneg.mpr hf.pos_left.le⟩ S :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      show dist x y ≤ A⁻¹ * dist (S x) (S y)
      rw [dist_eq_norm, dist_eq_norm, ← map_sub S x y]
      have hle := hbelow (x - y)
      calc ‖x - y‖ = A⁻¹ * (A * ‖x - y‖) := by
            rw [← mul_assoc, inv_mul_cancel₀ hf.pos_left.ne', one_mul]
        _ ≤ A⁻¹ * ‖S (x - y)‖ :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hf.pos_left.le)
  have hclosed : IsClosed (S.range : Set E) :=
    hanti.isClosed_range S.uniformContinuous
  have hself : ContinuousLinearMap.adjoint S = S := by
    rw [← star_eq_adjoint]
    exact (isSelfAdjoint_frameOperator (𝕜 := 𝕜) f).star_eq
  have hinjAdj : Function.Injective (ContinuousLinearMap.adjoint S) := by
    rw [hself]
    exact hinj
  have horth : S.rangeᗮ = ⊥ := by
    rw [S.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hinjAdj
  have hcl : S.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth]
    exact Submodule.bot_orthogonal_eq_top
  have hrange : S.range = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact hcl
  have hsurj : Function.Surjective S := by
    show Function.Surjective ⇑(S : E →ₗ[𝕜] E)
    rw [← LinearMap.range_eq_top]
    exact hrange
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

omit [CompleteSpace E] in
/-- The operator norm of the frame operator is at most the upper frame
bound. -/
theorem norm_frameOperator_le {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) :
    ‖frameOperator (𝕜 := 𝕜) f‖ ≤ B := by
  refine opNorm_le_bound (frameOperator (𝕜 := 𝕜) f) hf.pos_right.le fun x => ?_
  by_cases hx : frameOperator (𝕜 := 𝕜) f x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg hf.pos_right.le (norm_nonneg _)
  -- Cauchy-Schwarz in coefficient form: `‖Sx‖⁴ ≤ (∑ ‖⟪f i, x⟫_𝕜‖²) (∑ ‖⟪f i, Sx⟫_𝕜‖²)`.
  have hkey : (‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2) ^ 2
      ≤ (∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2) * (∑ i, ‖⟪f i, frameOperator (𝕜 := 𝕜) f x⟫_𝕜‖ ^ 2) := by
    have h1 := sq_norm_inner_frameOperator_apply_le (𝕜 := 𝕜) f x (frameOperator (𝕜 := 𝕜) f x)
    have h2 : ‖⟪frameOperator (𝕜 := 𝕜) f x, frameOperator (𝕜 := 𝕜) f x⟫_𝕜‖
        = ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rwa [h2] at h1
  have hub1 : ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 ≤ B * ‖x‖ ^ 2 := hf.upper x
  have hub2 : ∑ i, ‖⟪f i, frameOperator (𝕜 := 𝕜) f x⟫_𝕜‖ ^ 2
      ≤ B * ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 := hf.upper _
  have hle : (‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2) ^ 2
      ≤ (B * ‖x‖ ^ 2) * (B * ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2) :=
    hkey.trans (mul_le_mul hub1 hub2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (mul_nonneg hf.pos_right.le (sq_nonneg _)))
  have hsqpos : (0 : ℝ) < ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  -- Cancel one factor `‖Sx‖²` and take square roots.
  have hle2 : ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 ≤ (B * ‖x‖) ^ 2 := by
    apply le_of_mul_le_mul_right _ hsqpos
    calc ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 * ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2
        = (‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2) ^ 2 := by ring
      _ ≤ (B * ‖x‖ ^ 2) * (B * ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2) := hle
      _ = (B * ‖x‖) ^ 2 * ‖frameOperator (𝕜 := 𝕜) f x‖ ^ 2 := by ring
  exact le_of_sq_le_sq hle2 (mul_nonneg hf.pos_right.le (norm_nonneg _))

/-- The inverse of the frame operator, as a bounded operator. -/
noncomputable def frameOperatorInv {f : ι → E} {A B : ℝ}
    (hf : IsFrame (𝕜 := 𝕜) f A B) : E →L[𝕜] E :=
  ↑(IsUnit.unit (isUnit_frameOperator hf))⁻¹

/-- The frame operator composed with its inverse is the identity. -/
theorem frameOperator_comp_frameOperatorInv {f : ι → E} {A B : ℝ}
    (hf : IsFrame (𝕜 := 𝕜) f A B) :
    frameOperator (𝕜 := 𝕜) f ∘L frameOperatorInv hf = 1 := by
  set u := IsUnit.unit (isUnit_frameOperator hf) with hu_def
  have hu : (u : E →L[𝕜] E) = frameOperator (𝕜 := 𝕜) f := by
    rw [hu_def]
    exact IsUnit.unit_spec _
  show frameOperator (𝕜 := 𝕜) f ∘L (↑(u⁻¹) : E →L[𝕜] E) = 1
  rw [← hu, ← ContinuousLinearMap.mul_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The inverse of the frame operator composed with it is the identity. -/
theorem frameOperatorInv_comp_frameOperator {f : ι → E} {A B : ℝ}
    (hf : IsFrame (𝕜 := 𝕜) f A B) :
    frameOperatorInv hf ∘L frameOperator (𝕜 := 𝕜) f = 1 := by
  set u := IsUnit.unit (isUnit_frameOperator hf) with hu_def
  have hu : (u : E →L[𝕜] E) = frameOperator (𝕜 := 𝕜) f := by
    rw [hu_def]
    exact IsUnit.unit_spec _
  show (↑(u⁻¹) : E →L[𝕜] E) ∘L frameOperator (𝕜 := 𝕜) f = 1
  rw [← hu, ← ContinuousLinearMap.mul_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- The inverse of the frame operator is self-adjoint. -/
theorem isSelfAdjoint_frameOperatorInv {f : ι → E} {A B : ℝ}
    (hf : IsFrame (𝕜 := 𝕜) f A B) : IsSelfAdjoint (frameOperatorInv hf) := by
  rw [IsSelfAdjoint, star_eq_adjoint]
  have hS : ContinuousLinearMap.adjoint (frameOperator (𝕜 := 𝕜) f)
      = frameOperator (𝕜 := 𝕜) f := by
    rw [← star_eq_adjoint]
    exact (isSelfAdjoint_frameOperator (𝕜 := 𝕜) f).star_eq
  have h1 : ContinuousLinearMap.adjoint (frameOperatorInv hf)
      ∘L frameOperator (𝕜 := 𝕜) f = 1 := by
    rw [← hS, ← ContinuousLinearMap.adjoint_comp, frameOperator_comp_frameOperatorInv,
      ContinuousLinearMap.adjoint_one]
  calc ContinuousLinearMap.adjoint (frameOperatorInv hf)
      = ContinuousLinearMap.adjoint (frameOperatorInv hf) ∘L 1 := by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    _ = ContinuousLinearMap.adjoint (frameOperatorInv hf)
          ∘L (frameOperator (𝕜 := 𝕜) f ∘L frameOperatorInv hf) := by
        rw [frameOperator_comp_frameOperatorInv]
    _ = (ContinuousLinearMap.adjoint (frameOperatorInv hf)
          ∘L frameOperator (𝕜 := 𝕜) f) ∘L frameOperatorInv hf := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = 1 ∘L frameOperatorInv hf := by rw [h1]
    _ = frameOperatorInv hf := by rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- The frame reconstruction formula: every vector is the sum of its frame
coefficients against the dual frame. -/
theorem frame_reconstruction {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B)
    (x : E) :
    ∑ i, ⟪f i, frameOperatorInv hf x⟫_𝕜 • f i = x := by
  have h : frameOperator (𝕜 := 𝕜) f (frameOperatorInv hf x) = x := by
    rw [← ContinuousLinearMap.comp_apply, frameOperator_comp_frameOperatorInv]
    rfl
  rw [← frameOperator_apply (𝕜 := 𝕜) f (frameOperatorInv hf x)]
  exact h

/-- The canonical dual frame: the image of the frame under the inverse
frame operator. -/
noncomputable def dualFrame {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B)
    (i : ι) : E :=
  frameOperatorInv hf (f i)

/-- The frame operator of the dual frame is the inverse frame operator. -/
theorem frameOperator_dualFrame {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) :
    frameOperator (𝕜 := 𝕜) (dualFrame hf) = frameOperatorInv hf := by
  ext y
  rw [frameOperator_apply (𝕜 := 𝕜) (dualFrame hf) y]
  have hadj : ContinuousLinearMap.adjoint (frameOperatorInv hf) = frameOperatorInv hf := by
    rw [← star_eq_adjoint]
    exact (isSelfAdjoint_frameOperatorInv (𝕜 := 𝕜) hf).star_eq
  have hterm : ∀ i : ι, ⟪dualFrame hf i, y⟫_𝕜 • dualFrame hf i
      = frameOperatorInv hf (⟪f i, frameOperatorInv hf y⟫_𝕜 • f i) := by
    intro i
    rw [dualFrame, map_smul]
    congr 1
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← map_sum,
    ← frameOperator_apply (𝕜 := 𝕜) f (frameOperatorInv hf y)]
  congr 1
  rw [← ContinuousLinearMap.comp_apply, frameOperator_comp_frameOperatorInv]
  rfl

/-- The canonical dual frame is a frame, with reciprocal bounds `1 / B` and
`1 / A`. -/
theorem isFrame_dualFrame {f : ι → E} {A B : ℝ} (hf : IsFrame (𝕜 := 𝕜) f A B) :
    IsFrame (𝕜 := 𝕜) (dualFrame hf) (1 / B) (1 / A) := by
  refine ⟨one_div_pos.mpr hf.pos_right, one_div_pos.mpr hf.pos_left, fun x => ?_⟩
  have hsum : ∑ i, ‖⟪dualFrame hf i, x⟫_𝕜‖ ^ 2
      = RCLike.re ⟪frameOperatorInv hf x, x⟫_𝕜 := by
    rw [← re_inner_frameOperator_apply_self (𝕜 := 𝕜) (dualFrame hf) x,
      frameOperator_dualFrame hf]
  set y := frameOperatorInv hf x with hy
  have hxy : frameOperator (𝕜 := 𝕜) f y = x := by
    rw [hy, ← ContinuousLinearMap.comp_apply, frameOperator_comp_frameOperatorInv]
    rfl
  have hQ : RCLike.re ⟪frameOperatorInv hf x, x⟫_𝕜
      = ∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2 := by
    have h2 : frameOperatorInv hf (frameOperator (𝕜 := 𝕜) f y) = y := by
      rw [← ContinuousLinearMap.comp_apply, frameOperatorInv_comp_frameOperator]
      rfl
    rw [← hxy, h2, ← inner_conj_symm, RCLike.conj_re,
      re_inner_frameOperator_apply_self (𝕜 := 𝕜) f y]
  have hQnn : 0 ≤ ∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hlower : ‖x‖ ^ 2 ≤ B * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := by
    by_cases hSy : frameOperator (𝕜 := 𝕜) f y = 0
    · have hx0 : x = 0 := by rw [← hxy, hSy]
      rw [hx0]
      have h0 : ‖(0 : E)‖ ^ 2 = 0 := by simp
      rw [h0]
      exact mul_nonneg hf.pos_right.le hQnn
    · have hCS := sq_norm_inner_frameOperator_apply_le (𝕜 := 𝕜) f y
        (frameOperator (𝕜 := 𝕜) f y)
      have hnorm : ‖⟪frameOperator (𝕜 := 𝕜) f y, frameOperator (𝕜 := 𝕜) f y⟫_𝕜‖
          = ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        simp
      rw [hnorm] at hCS
      have hub : ∑ i, ‖⟪f i, frameOperator (𝕜 := 𝕜) f y⟫_𝕜‖ ^ 2
          ≤ B * ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 := hf.upper _
      have hle : (‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2) ^ 2
          ≤ (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) * (B * ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2) :=
        hCS.trans (mul_le_mul_of_nonneg_left hub
          (Finset.sum_nonneg fun i _ => sq_nonneg _))
      have hpos : 0 < ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 :=
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hSy)
      have hle2 : ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2
          ≤ B * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := by
        apply le_of_mul_le_mul_right _ hpos
        calc ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 * ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2
            = (‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2) ^ 2 := by ring
          _ ≤ (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) * (B * ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2) := hle
          _ = (B * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2))
              * ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 := by ring
      rw [← hxy]
      exact hle2
  have hupper : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ≤ (1 / A) * ‖x‖ ^ 2 := by
    by_cases hQ0 : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) = 0
    · rw [hQ0]
      exact mul_nonneg (one_div_nonneg.mpr hf.pos_left.le) (sq_nonneg _)
    · have hCS : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ≤ ‖frameOperator (𝕜 := 𝕜) f y‖ * ‖y‖ := by
        have h1 : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2)
            = RCLike.re ⟪frameOperator (𝕜 := 𝕜) f y, y⟫_𝕜 :=
          (re_inner_frameOperator_apply_self (𝕜 := 𝕜) f y).symm
        rw [h1]
        exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      have hlow : A * ‖y‖ ^ 2 ≤ ∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2 := hf.lower y
      have h3 : ‖y‖ ^ 2 ≤ (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) / A := by
        rw [le_div_iff₀ hf.pos_left, mul_comm]
        exact hlow
      have hQ2 : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ^ 2
          ≤ ‖x‖ ^ 2 * ((∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) / A) := by
        calc (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ^ 2
            ≤ (‖frameOperator (𝕜 := 𝕜) f y‖ * ‖y‖) ^ 2 :=
              pow_le_pow_left₀ hQnn hCS 2
          _ = ‖frameOperator (𝕜 := 𝕜) f y‖ ^ 2 * ‖y‖ ^ 2 := by ring
          _ ≤ ‖x‖ ^ 2 * ((∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) / A) := by
              rw [hxy]
              exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      have hQpos : 0 < ∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2 := lt_of_le_of_ne hQnn (Ne.symm hQ0)
      have hle : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2)
          ≤ (‖x‖ ^ 2 / A) * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := by
        rw [← pow_two]
        calc (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ^ 2 ≤ ‖x‖ ^ 2 * ((∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) / A) := hQ2
          _ = (‖x‖ ^ 2 / A) * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := by ring
      have hle2 : (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) ≤ ‖x‖ ^ 2 / A :=
        le_of_mul_le_mul_right hle hQpos
      rw [div_eq_mul_one_div, mul_comm (‖x‖ ^ 2) (1 / A)] at hle2
      exact hle2
  constructor
  · rw [hsum, hQ, div_mul_eq_mul_div, div_le_iff₀ hf.pos_right]
    calc 1 * ‖x‖ ^ 2 = ‖x‖ ^ 2 := one_mul _
      _ ≤ B * (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) := hlower
      _ = (∑ i, ‖⟪f i, y⟫_𝕜‖ ^ 2) * B := mul_comm _ _
  · rw [hsum, hQ]
    exact hupper

/-- A tight frame, one whose bounds agree, has frame operator `A • 1`. -/
theorem frameOperator_eq_smul_one_of_isTightFrame {f : ι → E} {A : ℝ}
    (hf : IsFrame (𝕜 := 𝕜) f A A) :
    frameOperator (𝕜 := 𝕜) f = (A : 𝕜) • (1 : E →L[𝕜] E) := by
  have hsym : ((frameOperator (𝕜 := 𝕜) f - (A : 𝕜) • (1 : E →L[𝕜] E)).toLinearMap).IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe, sub_apply,
      smul_apply, one_apply_eq_self, inner_sub_left,
      inner_sub_right, inner_smul_left, inner_smul_right]
    have h1 : ⟪frameOperator (𝕜 := 𝕜) f x, y⟫_𝕜
        = ⟪x, frameOperator (𝕜 := 𝕜) f y⟫_𝕜 := by
      rw [← ContinuousLinearMap.adjoint_inner_left]
      have hS : ContinuousLinearMap.adjoint (frameOperator (𝕜 := 𝕜) f)
          = frameOperator (𝕜 := 𝕜) f := by
        rw [← star_eq_adjoint]
        exact (isSelfAdjoint_frameOperator (𝕜 := 𝕜) f).star_eq
      rw [hS]
    rw [h1, RCLike.conj_ofReal]
  have hzero : ∀ x : E, ⟪((frameOperator (𝕜 := 𝕜) f
      - (A : 𝕜) • (1 : E →L[𝕜] E)).toLinearMap) x, x⟫_𝕜 = 0 := by
    intro x
    simp only [ContinuousLinearMap.coe_coe, sub_apply,
      smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, inner_self_eq_norm_sq_to_K]
    rw [inner_frameOperator_apply_self (𝕜 := 𝕜) f x, RCLike.conj_ofReal]
    have htight : ∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 = A * ‖x‖ ^ 2 :=
      le_antisymm (hf.upper x) (hf.lower x)
    have hcast : ((∑ i, ‖⟪f i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) = ((A * ‖x‖ ^ 2 : ℝ) : 𝕜) := by
      rw [htight]
    rw [hcast, RCLike.ofReal_mul, ← RCLike.ofReal_pow, sub_self]
  have hT0 := (LinearMap.IsSymmetric.inner_map_self_eq_zero hsym).mp hzero
  have hCLM : frameOperator (𝕜 := 𝕜) f - (A : 𝕜) • (1 : E →L[𝕜] E) = 0 := by
    ext x
    have h := LinearMap.congr_fun hT0 x
    simpa using h
  exact sub_eq_zero.mp hCLM

end MathlibExt.Analysis.InnerProductSpace.FiniteFrame
