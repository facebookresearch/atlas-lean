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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.FullTimePullback
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInftyOpen
public import MathlibExt.KTheory.CStar.Cone.EndpointLift

import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The initial-evaluation kernel of the full-time pullback

The kernel of evaluation at time one is a closed ideal of the actual full-time
pullback. Its coefficient projection is onto: subtracting the translated cone
endpoint lift corrects the existing set section at time one. This is only a
set-theoretic section, with no finite-time linearity assumption.

The kernel of the restricted coefficient projection is the suspension algebra.
The reciprocal coordinate sends time infinity to the puncture zero and time
one to endpoint one. The norm and C-star dictionaries are inherited from the
existing closed ideals; no global instance or parallel middle algebra is added.

Reference: Blackadar, K-Theory for Operator Algebras (1998), §25.1.2(b),
§25.1.4(b), and the full-time pullback in §25.6. The parent's full C0 kernel is
unchanged. Mapping-cone comparison, Busby converses and E-theory inverses are
not asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped NNReal ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism.FullTimePullback

/-! ## Actual time coordinates -/

/-- Translate the closed time ray to the nonnegative reals by `t ↦ t - 1`. -/
def timeHomeomorphNNReal : AsymptoticTime ≃ₜ ℝ≥0 := by
  let e : ℝ ≃o ℝ := OrderIso.addRight (-1)
  have h₁ : e 1 = 0 := by
    change (1 : ℝ) + (-1) = 0
    exact add_neg_cancel 1
  exact ((e.Ici 1).trans
    (Set.orderIsoOfEq (Ici (e 1)) (Ici 0) (congrArg Ici h₁))).toHomeomorph

/-- The translated time has its literal real coordinate. -/
theorem timeHomeomorphNNReal_apply (t : AsymptoticTime) :
    (timeHomeomorphNNReal t : ℝ) = (t : ℝ) - 1 := by
  change (t : ℝ) + (-1) = (t : ℝ) - 1
  exact (sub_eq_add_neg _ _).symm

/-- The inverse translation has real coordinate `u + 1`. -/
theorem timeHomeomorphNNReal_symm_apply (u : ℝ≥0) :
    (timeHomeomorphNNReal.symm u : ℝ) = (u : ℝ) + 1 := by
  have h := timeHomeomorphNNReal_apply (timeHomeomorphNNReal.symm u)
  rw [timeHomeomorphNNReal.apply_symm_apply] at h
  linarith

/-- Time one is sent to zero, using the proved endpoint transport. -/
@[simp]
theorem timeHomeomorphNNReal_one :
    timeHomeomorphNNReal ⟨1, le_rfl⟩ = 0 := by
  apply NNReal.eq
  rw [timeHomeomorphNNReal_apply]
  exact sub_self 1

/-- Zero is sent back to time one. -/
@[simp]
theorem timeHomeomorphNNReal_symm_zero :
    timeHomeomorphNNReal.symm 0 = ⟨1, le_rfl⟩ := by
  apply timeHomeomorphNNReal.injective
  rw [timeHomeomorphNNReal.apply_symm_apply, timeHomeomorphNNReal_one]

/-- Interior times have strictly positive translated coordinates. -/
theorem timeHomeomorphNNReal_pos {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    0 < timeHomeomorphNNReal t := by
  have h : 0 < (timeHomeomorphNNReal t : ℝ) := by
    rw [timeHomeomorphNNReal_apply]
    exact sub_pos.mpr ht
  exact_mod_cast h

/-- The decreasing reciprocal coordinate from the positive half-line to `(0,1)`. -/
def positiveNNRealReciprocalHomeomorph :
    Ioi (0 : ℝ≥0) ≃ₜ Ioo (0 : ℝ) 1 where
  toFun u := ⟨1 / (1 + ((u : ℝ≥0) : ℝ)), by
    have hu : 0 < ((u : ℝ≥0) : ℝ) := by exact_mod_cast u.property
    have hd : 0 < 1 + ((u : ℝ≥0) : ℝ) := by linarith
    exact ⟨div_pos zero_lt_one hd, (div_lt_one hd).2 (by linarith)⟩⟩
  invFun s := ⟨NNReal.mk (1 / (s : ℝ) - 1) (by
    exact le_of_lt (sub_pos.mpr ((one_lt_div s.property.1).2 s.property.2))), by
    have h : 0 < 1 / (s : ℝ) - 1 :=
      sub_pos.mpr ((one_lt_div s.property.1).2 s.property.2)
    exact_mod_cast h⟩
  left_inv u := by
    apply Subtype.ext
    apply NNReal.eq
    change 1 / (1 / (1 + ((u : ℝ≥0) : ℝ))) - 1 = ((u : ℝ≥0) : ℝ)
    simp only [one_div, inv_inv]
    ring
  right_inv s := by
    apply Subtype.ext
    change 1 / (1 + (1 / (s : ℝ) - 1)) = (s : ℝ)
    have h : 1 + (1 / (s : ℝ) - 1) = 1 / (s : ℝ) := by ring
    rw [h]
    simp only [one_div, inv_inv]
  continuous_toFun := by
    have hu : Continuous (fun u : Ioi (0 : ℝ≥0) ↦ ((u : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp continuous_subtype_val
    exact (continuous_const.div (continuous_const.add hu) (fun u ↦ by
      have hp : 0 < ((u : ℝ≥0) : ℝ) := by exact_mod_cast u.property
      exact ne_of_gt (by linarith : 0 < 1 + ((u : ℝ≥0) : ℝ)))).subtype_mk _
  continuous_invFun := by
    have hs : Continuous (fun s : Ioo (0 : ℝ) 1 ↦ 1 / (s : ℝ) - 1) :=
      (continuous_const.div continuous_subtype_val
        (fun s ↦ ne_of_gt s.property.1)).sub continuous_const
    exact (hs.subtype_mk _).subtype_mk _

/-- The reciprocal coordinate has the stated scalar value. -/
theorem positiveNNRealReciprocalHomeomorph_apply (u : Ioi (0 : ℝ≥0)) :
    (positiveNNRealReciprocalHomeomorph u : ℝ) =
      1 / (1 + ((u : ℝ≥0) : ℝ)) :=
  rfl

/-- The inverse coordinate is the actual positive number `1/s - 1`. -/
theorem positiveNNRealReciprocalHomeomorph_symm_apply (s : Ioo (0 : ℝ) 1) :
    ((positiveNNRealReciprocalHomeomorph.symm s : ℝ≥0) : ℝ) = 1 / (s : ℝ) - 1 :=
  rfl

/-- Translation followed by the reciprocal coordinate has value `1/t`. -/
theorem positiveNNRealReciprocalHomeomorph_time
    {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    (positiveNNRealReciprocalHomeomorph
      ⟨timeHomeomorphNNReal t, timeHomeomorphNNReal_pos ht⟩ : ℝ) = 1 / (t : ℝ) := by
  rw [positiveNNRealReciprocalHomeomorph_apply, timeHomeomorphNNReal_apply]
  congr 1
  ring

universe uA uB

/-! ## Cone and suspension transport -/

section ConeTransport

variable (B : Type uB) [NonUnitalCStarAlgebra B]

/-- Transport the existing cone to the closed time ray by translation. -/
def coneTimeEquiv : CStarKTheory.Cone B ≃⋆ₐ[ℂ] C₀(AsymptoticTime, B) :=
  ZeroAtInftyContinuousMap.starAlgEquivPrecomp timeHomeomorphNNReal

/-- Cone transport has the literal translated value. -/
theorem coneTimeEquiv_apply (f : CStarKTheory.Cone B) (t : AsymptoticTime) :
    coneTimeEquiv B f t = f (timeHomeomorphNNReal t) :=
  rfl

/-- The inverse uses the computed inverse time translation. -/
theorem coneTimeEquiv_symm_apply (f : C₀(AsymptoticTime, B)) (u : ℝ≥0) :
    (coneTimeEquiv B).symm f u = f (timeHomeomorphNNReal.symm u) :=
  rfl

/-- Transport preserves the endpoint value, with zero corresponding to time one. -/
@[simp]
theorem coneTimeEquiv_one (f : CStarKTheory.Cone B) :
    coneTimeEquiv B f ⟨1, le_rfl⟩ = f 0 := by
  rw [coneTimeEquiv_apply, timeHomeomorphNNReal_one]

/-- Restrict cone transport to the two actual point-evaluation kernels. -/
def conePointKernelEquiv :
    letI : NonUnitalCStarAlgebra
        (ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)).carrier :=
      ClosedStarIdeal.carrierCStarAlgebra _
    letI : NonUnitalCStarAlgebra
        (ZeroAtInftyContinuousMap.vanishingAt (A := B)
          (⟨1, le_rfl⟩ : AsymptoticTime)).carrier :=
      ClosedStarIdeal.carrierCStarAlgebra _
    (ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)).carrier ≃⋆ₐ[ℂ]
      (ZeroAtInftyContinuousMap.vanishingAt (A := B)
        (⟨1, le_rfl⟩ : AsymptoticTime)).carrier := by
  let W := ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)
  let V := ZeroAtInftyContinuousMap.vanishingAt (A := B)
    (⟨1, le_rfl⟩ : AsymptoticTime)
  letI : NonUnitalCStarAlgebra W.carrier := ClosedStarIdeal.carrierCStarAlgebra W
  letI : NonUnitalCStarAlgebra V.carrier := ClosedStarIdeal.carrierCStarAlgebra V
  let forward : W.carrier →⋆ₙₐ[ℂ] V.carrier :=
    NonUnitalStarAlgHom.codRestrict
      ((coneTimeEquiv B).toNonUnitalStarAlgHom.comp
        (NonUnitalStarSubalgebraClass.subtype W.carrier)) V.carrier (fun g ↦ by
          apply (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).2
          change coneTimeEquiv B g.val ⟨1, le_rfl⟩ = 0
          rw [coneTimeEquiv_one]
          exact (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).1 g.property)
  let backward : V.carrier →⋆ₙₐ[ℂ] W.carrier :=
    NonUnitalStarAlgHom.codRestrict
      ((coneTimeEquiv B).symm.toNonUnitalStarAlgHom.comp
        (NonUnitalStarSubalgebraClass.subtype V.carrier)) W.carrier (fun f ↦ by
          apply (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).2
          change (coneTimeEquiv B).symm f.val 0 = 0
          rw [coneTimeEquiv_symm_apply, timeHomeomorphNNReal_symm_zero]
          exact (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).1 f.property)
  exact StarAlgEquiv.ofNonUnitalStarAlgHom forward backward
    (by
      apply NonUnitalStarAlgHom.ext
      intro g
      apply Subtype.ext
      exact (coneTimeEquiv B).symm_apply_apply g.val)
    (by
      apply NonUnitalStarAlgHom.ext
      intro f
      apply Subtype.ext
      exact (coneTimeEquiv B).apply_symm_apply f.val)

/-- The restricted equivalence retains the original translated function. -/
theorem conePointKernelEquiv_apply
    (g : (ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)).carrier)
    (t : AsymptoticTime) :
    (conePointKernelEquiv B g : C₀(AsymptoticTime, B)) t =
      (g : C₀(ℝ≥0, B)) (timeHomeomorphNNReal t) :=
  rfl

/-- Its inverse retains the original inverse-translation coordinate. -/
theorem conePointKernelEquiv_symm_apply
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) (u : ℝ≥0) :
    ((conePointKernelEquiv B).symm f : C₀(ℝ≥0, B)) u =
      (f : C₀(AsymptoticTime, B)) (timeHomeomorphNNReal.symm u) :=
  rfl

/-- The suspension is the actual time-one-zero subideal of full closed-ray C0. -/
def openIntervalKernelEquiv :
    letI : NonUnitalCStarAlgebra
        (ZeroAtInftyContinuousMap.vanishingAt (A := B)
          (⟨1, le_rfl⟩ : AsymptoticTime)).carrier :=
      ClosedStarIdeal.carrierCStarAlgebra _
    C₀(Ioo (0 : ℝ) 1, B) ≃⋆ₐ[ℂ]
      (ZeroAtInftyContinuousMap.vanishingAt (A := B)
        (⟨1, le_rfl⟩ : AsymptoticTime)).carrier := by
  letI : NonUnitalCStarAlgebra
      (ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)).carrier :=
    ClosedStarIdeal.carrierCStarAlgebra _
  letI : NonUnitalCStarAlgebra
      (ZeroAtInftyContinuousMap.vanishingAt (A := B)
        (⟨1, le_rfl⟩ : AsymptoticTime)).carrier :=
    ClosedStarIdeal.carrierCStarAlgebra _
  exact ((ZeroAtInftyContinuousMap.starAlgEquivPrecomp
    (A := B) positiveNNRealReciprocalHomeomorph).trans
      ZeroAtInftyContinuousMap.positiveNNRealStarAlgEquivVanishingAtZero).trans
    (conePointKernelEquiv B)

/-- The suspension transport is zero at time one. -/
theorem openIntervalKernelEquiv_one (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (openIntervalKernelEquiv B f : C₀(AsymptoticTime, B)) ⟨1, le_rfl⟩ = 0 :=
  (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).1
    (openIntervalKernelEquiv B f).property

/-- At an interior time the literal suspension coordinate is `1/t`. -/
theorem openIntervalKernelEquiv_apply_of_one_lt
    (f : C₀(Ioo (0 : ℝ) 1, B)) {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    (openIntervalKernelEquiv B f : C₀(AsymptoticTime, B)) t =
      f ⟨1 / (t : ℝ),
        div_pos zero_lt_one (lt_trans zero_lt_one ht),
        (div_lt_one (lt_trans zero_lt_one ht)).2 ht⟩ := by
  change ZeroAtInftyContinuousMap.extendZeroFromPositiveNNReal
    (ZeroAtInftyContinuousMap.starAlgEquivPrecomp
      positiveNNRealReciprocalHomeomorph f) (timeHomeomorphNNReal t) = _
  rw [ZeroAtInftyContinuousMap.extendZeroFromPositiveNNReal_apply_of_pos _
    (timeHomeomorphNNReal_pos ht),
    ZeroAtInftyContinuousMap.starAlgEquivPrecomp_apply]
  congr 1
  apply Subtype.ext
  exact positiveNNRealReciprocalHomeomorph_time ht

/-- The computed inverse recovers the interior reciprocal time coordinate. -/
theorem openIntervalKernelEquiv_symm_apply
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) (s : Ioo (0 : ℝ) 1) :
    (openIntervalKernelEquiv B).symm f s =
      (f : C₀(AsymptoticTime, B))
        (timeHomeomorphNNReal.symm
          (positiveNNRealReciprocalHomeomorph.symm s : ℝ≥0)) :=
  rfl

end ConeTransport

/-! ## The actual anchored closed ideal -/

section AnchoredPullback

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (φ : AsymptoticMorphism A B)

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

/-- The actual kernel of ordinary evaluation at time one in the full pullback. -/
def initialEvaluationIdeal :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    ClosedStarIdeal (FullTimePullback φ) :=
  ClosedStarIdeal.ker (evaluation φ ⟨1, le_rfl⟩)

/-- Membership in the anchored ideal is exactly zero initial evaluation. -/
@[simp]
theorem mem_initialEvaluationIdeal (d : FullTimePullback φ) :
    d ∈ initialEvaluationIdeal φ ↔ evaluation φ ⟨1, le_rfl⟩ d = 0 :=
  ClosedStarIdeal.mem_ker (evaluation φ ⟨1, le_rfl⟩) d

/-- The anchored middle carrier, with the unchanged inherited subobject norm. -/
abbrev InitialEvaluationKernel : Type (max uA uB) :=
  (initialEvaluationIdeal φ).carrier

/-- Restrict the existing coefficient projection to its anchored closed ideal. -/
def initialProjection :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
      ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
    InitialEvaluationKernel φ →⋆ₙₐ[ℂ] A := by
  letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
    _root_.AsymptoticAlgebra.cStarAlgebra B
  letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact (projection φ).comp
    (NonUnitalStarSubalgebraClass.subtype (initialEvaluationIdeal φ).carrier)

/-- The restricted projection retains the actual first-coordinate value. -/
theorem initialProjection_apply (d : InitialEvaluationKernel φ) :
    initialProjection φ d = projection φ d.val :=
  rfl

/-- Correct the existing orbit section by its translated cone endpoint lift.
This is a plain set section, not a star-algebra homomorphism. -/
def initialSetSection (a : A) : InitialEvaluationKernel φ :=
  ⟨setSection φ a - kernelInclusion φ
      (coneTimeEquiv B (CStarKTheory.Cone.endpointLift (φ ⟨1, le_rfl⟩ a))), by
    apply (mem_initialEvaluationIdeal φ _).2
    rw [map_sub, evaluation_setSection, evaluation_kernelInclusion,
      coneTimeEquiv_one, CStarKTheory.Cone.endpointLift_zero, sub_self]⟩

/-- The corrected set section has the stated ambient subtraction value. -/
theorem initialSetSection_val (a : A) :
    (initialSetSection φ a).val = setSection φ a - kernelInclusion φ
      (coneTimeEquiv B (CStarKTheory.Cone.endpointLift (φ ⟨1, le_rfl⟩ a))) :=
  rfl

/-- Initial evaluation of the actual corrected section is zero. -/
theorem evaluation_initialSetSection (a : A) :
    evaluation φ ⟨1, le_rfl⟩ (initialSetSection φ a).val = 0 :=
  (mem_initialEvaluationIdeal φ _).1 (initialSetSection φ a).property

/-- Subtracting a full-kernel element leaves the coefficient unchanged. -/
@[simp]
theorem initialProjection_initialSetSection (a : A) :
    initialProjection φ (initialSetSection φ a) = a := by
  rw [initialProjection_apply, initialSetSection_val, map_sub,
    projection_setSection, projection_kernelInclusion, sub_zero]

/-- The explicit set section proves actual surjectivity for arbitrary raw orbits. -/
theorem initialProjection_surjective : Function.Surjective (initialProjection φ) :=
  fun a ↦ ⟨initialSetSection φ a, initialProjection_initialSetSection φ a⟩

/-- Restrict the old full C0 inclusion to functions vanishing at time one. -/
def actualKernelInclusion :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    letI : NonUnitalCStarAlgebra
        (ZeroAtInftyContinuousMap.vanishingAt (A := B)
          (⟨1, le_rfl⟩ : AsymptoticTime)).carrier :=
      ClosedStarIdeal.carrierCStarAlgebra _
    letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
      ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
    (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier →⋆ₙₐ[ℂ] InitialEvaluationKernel φ := by
  let V := ZeroAtInftyContinuousMap.vanishingAt (A := B)
    (⟨1, le_rfl⟩ : AsymptoticTime)
  letI : NonUnitalCStarAlgebra V.carrier := ClosedStarIdeal.carrierCStarAlgebra V
  letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact NonUnitalStarAlgHom.codRestrict
    ((kernelInclusion φ).comp (NonUnitalStarSubalgebraClass.subtype V.carrier))
    (initialEvaluationIdeal φ).carrier (fun f ↦ by
      apply (mem_initialEvaluationIdeal φ _).2
      change evaluation φ ⟨1, le_rfl⟩ (kernelInclusion φ f.val) = 0
      rw [evaluation_kernelInclusion]
      exact (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).1 f.property)

/-- The intermediate inclusion uses the parent's unchanged full C0 inclusion. -/
theorem actualKernelInclusion_val
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) :
    (actualKernelInclusion φ f).val = kernelInclusion φ f.val :=
  rfl

/-- This inclusion has zero coefficient projection. -/
@[simp]
theorem initialProjection_actualKernelInclusion
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) :
    initialProjection φ (actualKernelInclusion φ f) = 0 := by
  rw [initialProjection_apply, actualKernelInclusion_val, projection_kernelInclusion]

/-- The restricted full-kernel inclusion is injective. -/
theorem actualKernelInclusion_injective : Function.Injective (actualKernelInclusion φ) := by
  intro f g h
  apply Subtype.ext
  apply kernelInclusion_injective φ
  exact congrArg Subtype.val h

/-- Exactness uses the parent's full C0 witness and proves its initial value zero. -/
theorem actualKernelInclusion_exact :
    Function.Exact (actualKernelInclusion φ) (initialProjection φ) := by
  intro d
  constructor
  · intro hd
    have hd₀ : projection φ d.val = 0 := (initialProjection_apply φ d).symm.trans hd
    obtain ⟨f, hf⟩ := (_root_.AsymptoticMorphism.FullTimePullback.exact φ d.val).1 hd₀
    have hf₀ : f (⟨1, le_rfl⟩ : AsymptoticTime) = 0 := by
      calc
        f ⟨1, le_rfl⟩ = evaluation φ ⟨1, le_rfl⟩ (kernelInclusion φ f) :=
          (evaluation_kernelInclusion φ ⟨1, le_rfl⟩ f).symm
        _ = evaluation φ ⟨1, le_rfl⟩ d.val := congrArg (evaluation φ ⟨1, le_rfl⟩) hf
        _ = 0 := (mem_initialEvaluationIdeal φ d.val).1 d.property
    refine ⟨⟨f, (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).2 hf₀⟩, ?_⟩
    apply Subtype.ext
    exact hf
  · rintro ⟨f, rfl⟩
    exact initialProjection_actualKernelInclusion φ f

/-- Include the literal reciprocal suspension kernel in the anchored middle. -/
def initialSuspensionInclusion :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
      ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
    C₀(Ioo (0 : ℝ) 1, B) →⋆ₙₐ[ℂ] InitialEvaluationKernel φ := by
  letI : NonUnitalCStarAlgebra
      (ZeroAtInftyContinuousMap.vanishingAt (A := B)
        (⟨1, le_rfl⟩ : AsymptoticTime)).carrier :=
    ClosedStarIdeal.carrierCStarAlgebra _
  letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact (actualKernelInclusion φ).comp (openIntervalKernelEquiv B).toNonUnitalStarAlgHom

/-- The ambient value is the original inclusion of the computed C0 suspension. -/
theorem initialSuspensionInclusion_val (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (initialSuspensionInclusion φ f).val =
      kernelInclusion φ (openIntervalKernelEquiv B f).val :=
  rfl

/-- The suspension inclusion has zero initial-time evaluation. -/
theorem initialSuspensionInclusion_one (f : C₀(Ioo (0 : ℝ) 1, B)) :
    evaluation φ ⟨1, le_rfl⟩ (initialSuspensionInclusion φ f).val = 0 :=
  (mem_initialEvaluationIdeal φ _).1 (initialSuspensionInclusion φ f).property

/-- At every interior time its bounded coordinate is the literal value `f(1/t)`. -/
theorem initialSuspensionInclusion_apply_of_one_lt
    (f : C₀(Ioo (0 : ℝ) 1, B)) {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    evaluation φ t (initialSuspensionInclusion φ f).val =
      f ⟨1 / (t : ℝ),
        div_pos zero_lt_one (lt_trans zero_lt_one ht),
        (div_lt_one (lt_trans zero_lt_one ht)).2 ht⟩ := by
  rw [initialSuspensionInclusion_val, evaluation_kernelInclusion]
  exact openIntervalKernelEquiv_apply_of_one_lt B f ht

/-- The suspension inclusion is injective for zero and nonfaithful coefficient maps too. -/
theorem initialSuspensionInclusion_injective :
    Function.Injective (initialSuspensionInclusion φ) :=
  (actualKernelInclusion_injective φ).comp (openIntervalKernelEquiv B).injective

/-- The coefficient projection kills the suspension inclusion. -/
@[simp]
theorem initialProjection_initialSuspensionInclusion (f : C₀(Ioo (0 : ℝ) 1, B)) :
    initialProjection φ (initialSuspensionInclusion φ f) = 0 :=
  initialProjection_actualKernelInclusion φ (openIntervalKernelEquiv B f)

/-- Exactness of the anchored sequence, using the actual suspension inverse. -/
theorem initialSuspensionInclusion_exact :
    Function.Exact (initialSuspensionInclusion φ) (initialProjection φ) := by
  intro d
  constructor
  · intro hd
    obtain ⟨f, hf⟩ := (actualKernelInclusion_exact φ d).1 hd
    refine ⟨(openIntervalKernelEquiv B).symm f, ?_⟩
    change actualKernelInclusion φ
      (openIntervalKernelEquiv B ((openIntervalKernelEquiv B).symm f)) = d
    rw [(openIntervalKernelEquiv B).apply_symm_apply]
    exact hf
  · rintro ⟨f, rfl⟩
    exact initialProjection_initialSuspensionInclusion φ f

/-- Normalize the proved exact pair, retaining the actual anchored middle and norm. -/
def initialEvaluationExtension :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    CStarExtension.{uA, uB, max uA uB} A C₀(Ioo (0 : ℝ) 1, B) := by
  letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact (initialSuspensionInclusion φ) (initialProjection φ)
    (initialSuspensionInclusion_injective φ) (initialProjection_surjective φ)
    (initialSuspensionInclusion_exact φ)

/-- Exact-pair normalization does not replace the anchored middle carrier. -/
theorem initialEvaluationExtension_middle :
    (initialEvaluationExtension φ).Middle = InitialEvaluationKernel φ :=
  rfl

/-- The normalized inclusion is the actual reciprocal suspension inclusion. -/
theorem initialEvaluationExtension_inclusion_apply (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (initialEvaluationExtension φ).inclusion f = initialSuspensionInclusion φ f := by
  let : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact_inclusion_apply (initialSuspensionInclusion φ)
    (initialProjection φ) (initialSuspensionInclusion_injective φ)
    (initialProjection_surjective φ) (initialSuspensionInclusion_exact φ) f

/-- The normalized quotient is the actual restricted coefficient projection. -/
theorem initialEvaluationExtension_quotient_apply (d : InitialEvaluationKernel φ) :
    (initialEvaluationExtension φ).quotient d = initialProjection φ d := by
  let : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact_quotient_apply (initialSuspensionInclusion φ)
    (initialProjection φ) (initialSuspensionInclusion_injective φ)
    (initialProjection_surjective φ) (initialSuspensionInclusion_exact φ) d

end AnchoredPullback

end AsymptoticMorphism.FullTimePullback
