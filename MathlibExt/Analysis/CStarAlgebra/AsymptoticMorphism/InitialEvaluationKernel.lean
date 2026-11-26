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
# Initial-evaluation kernel of a full-time pullback

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. The projection p0 is surjective, with set section s0(a)=(a,t↦φ_t(a)-exp(1-t)•φ_1(a)).
Its kernel is J0, identified with C₀((0,1),B) by F(t)=f(1/t) for t>1 and F(1)=0. Thus
0→C₀((0,1),B)→Eφ→A→0 is a C-star extension.

Reference: Blackadar, K-Theory for Operator Algebras (1998), §25.1.2(b), §25.1.4(b), and the
full-time pullback in §25.6.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped NNReal ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism.FullTimePullback

/-!
## Coordinates on the closed time ray

For T=[1,∞), translation t↦t-1 is a homeomorphism T→[0,∞). On interior points t>1, the
reciprocal coordinate s=1/t gives a homeomorphism (1,∞)→(0,1).
-/

/-- **Translation of asymptotic time to the nonnegative half-line.**

The homeomorphism timeHomeomorphNNReal:T=[1,∞)≃ₜℝ≥0 is t↦t-1, with inverse u↦u+1.
-/
def timeHomeomorphNNReal : AsymptoticTime ≃ₜ ℝ≥0 := by
  let e : ℝ ≃o ℝ := OrderIso.addRight (-1)
  have h₁ : e 1 = 0 := by
    change (1 : ℝ) + (-1) = 0
    exact add_neg_cancel 1
  exact ((e.Ici 1).trans
    (Set.orderIsoOfEq (Ici (e 1)) (Ici 0) (congrArg Ici h₁))).toHomeomorph

/-- **Real value of the translated time coordinate.**

For t∈T=[1,∞), (timeHomeomorphNNReal t:ℝ)=t-1.
-/
theorem timeHomeomorphNNReal_apply (t : AsymptoticTime) :
    (timeHomeomorphNNReal t : ℝ) = (t : ℝ) - 1 := by
  change (t : ℝ) + (-1) = (t : ℝ) - 1
  exact (sub_eq_add_neg _ _).symm

/-- **Real value of the inverse time translation.**

For u∈ℝ≥0, the time timeHomeomorphNNReal.symm u∈[1,∞) has real coordinate u+1.
-/
theorem timeHomeomorphNNReal_symm_apply (u : ℝ≥0) :
    (timeHomeomorphNNReal.symm u : ℝ) = (u : ℝ) + 1 := by
  have h := timeHomeomorphNNReal_apply (timeHomeomorphNNReal.symm u)
  rw [timeHomeomorphNNReal.apply_symm_apply] at h
  linarith

/-- **The initial time translates to zero.**

Under timeHomeomorphNNReal:[1,∞)≃ₜℝ≥0, the time t=1 maps to u=0.
-/
@[simp]
theorem timeHomeomorphNNReal_one :
    timeHomeomorphNNReal ⟨1, le_rfl⟩ = 0 := by
  apply NNReal.eq
  rw [timeHomeomorphNNReal_apply]
  exact sub_self 1

/-- **Zero translates back to the initial time.**

Under the inverse of timeHomeomorphNNReal:[1,∞)≃ₜℝ≥0, the coordinate u=0 maps to t=1.
-/
@[simp]
theorem timeHomeomorphNNReal_symm_zero :
    timeHomeomorphNNReal.symm 0 = ⟨1, le_rfl⟩ := by
  apply timeHomeomorphNNReal.injective
  rw [timeHomeomorphNNReal.apply_symm_apply, timeHomeomorphNNReal_one]

/-- **Positivity of the translated interior time.**

If t∈[1,∞) and t>1, then timeHomeomorphNNReal t=t-1 is strictly positive.
-/
theorem timeHomeomorphNNReal_pos {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    0 < timeHomeomorphNNReal t := by
  have h : 0 < (timeHomeomorphNNReal t : ℝ) := by
    rw [timeHomeomorphNNReal_apply]
    exact sub_pos.mpr ht
  exact_mod_cast h

/-- **Reciprocal homeomorphism of positive coordinates.**

The homeomorphism positiveNNRealReciprocalHomeomorph:(0,∞)≃ₜ(0,1) is u↦1/(1+u), with inverse
s↦1/s-1.
-/
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

/-- **Value of the positive reciprocal coordinate.**

For u>0, positiveNNRealReciprocalHomeomorph u=1/(1+u)∈(0,1).
-/
theorem positiveNNRealReciprocalHomeomorph_apply (u : Ioi (0 : ℝ≥0)) :
    (positiveNNRealReciprocalHomeomorph u : ℝ) =
      1 / (1 + ((u : ℝ≥0) : ℝ)) :=
  rfl

/-- **Value of the inverse reciprocal coordinate.**

For s∈(0,1), positiveNNRealReciprocalHomeomorph.symm s=1/s-1>0.
-/
theorem positiveNNRealReciprocalHomeomorph_symm_apply (s : Ioo (0 : ℝ) 1) :
    ((positiveNNRealReciprocalHomeomorph.symm s : ℝ≥0) : ℝ) = 1 / (s : ℝ) - 1 :=
  rfl

/-- **Reciprocal coordinate of an interior asymptotic time.**

For t>1, composing the translated coordinate u=t-1 with u↦1/(1+u) gives 1/t∈(0,1).
-/
theorem positiveNNRealReciprocalHomeomorph_time
    {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    (positiveNNRealReciprocalHomeomorph
      ⟨timeHomeomorphNNReal t, timeHomeomorphNNReal_pos ht⟩ : ℝ) = 1 / (t : ℝ) := by
  rw [positiveNNRealReciprocalHomeomorph_apply, timeHomeomorphNNReal_apply]
  congr 1
  ring

universe uA uB

/-!
## Cone and suspension coordinate equivalences

Let B be a nonunital complex C-star algebra and T=[1,∞). Translation identifies C₀([0,∞),B)
with C₀(T,B), and reciprocal coordinates identify C₀((0,1),B) with {F∈C₀(T,B):F(1)=0},
preserving the supremum norm.
-/

section ConeTransport

variable (B : Type uB) [NonUnitalCStarAlgebra B]

/-- **Cone transported to the asymptotic time ray.**

Let B be a nonunital complex C-star algebra. The star-algebra equivalence coneTimeEquiv
B:CStarKTheory.Cone B=C₀([0,∞),B)≃⋆ₐ[ℂ]C₀([1,∞),B) sends f to t↦f(t-1).
-/
def coneTimeEquiv : CStarKTheory.Cone B ≃⋆ₐ[ℂ] C₀(AsymptoticTime, B) :=
  ZeroAtInftyContinuousMap.starAlgEquivPrecomp timeHomeomorphNNReal

/-- **Value of the translated cone function.**

Let B be a nonunital complex C-star algebra, f∈CStarKTheory.Cone B=C₀([0,∞),B) and t≥1. Then
coneTimeEquiv B f t=f(t-1).
-/
theorem coneTimeEquiv_apply (f : CStarKTheory.Cone B) (t : AsymptoticTime) :
    coneTimeEquiv B f t = f (timeHomeomorphNNReal t) :=
  rfl

/-- **Inverse cone transport value.**

Let B be a nonunital complex C-star algebra, F∈C₀([1,∞),B) and u≥0. Then (coneTimeEquiv
B).symm F u=F(u+1).
-/
theorem coneTimeEquiv_symm_apply (f : C₀(AsymptoticTime, B)) (u : ℝ≥0) :
    (coneTimeEquiv B).symm f u = f (timeHomeomorphNNReal.symm u) :=
  rfl

/-- **Endpoint preserved by cone translation.**

Let B be a nonunital complex C-star algebra and f∈C₀([0,∞),B). Then coneTimeEquiv B f 1=f(0).
-/
@[simp]
theorem coneTimeEquiv_one (f : CStarKTheory.Cone B) :
    coneTimeEquiv B f ⟨1, le_rfl⟩ = f 0 := by
  rw [coneTimeEquiv_apply, timeHomeomorphNNReal_one]

/-- **Equivalence of the cone endpoint and initial-time kernels.**

Let B be a nonunital complex C-star algebra. The star-algebra equivalence conePointKernelEquiv
B identifies {g∈C₀([0,∞),B):g(0)=0} with {F∈C₀([1,∞),B):F(1)=0} by F(t)=g(t-1), preserving the
inherited supremum norms.
-/
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

/-- **Value of a translated cone-kernel function.**

Let B be a nonunital complex C-star algebra and g∈C₀([0,∞),B) satisfy g(0)=0. For t≥1,
conePointKernelEquiv B g t=g(t-1).
-/
theorem conePointKernelEquiv_apply
    (g : (ZeroAtInftyContinuousMap.vanishingAt (A := B) (0 : ℝ≥0)).carrier)
    (t : AsymptoticTime) :
    (conePointKernelEquiv B g : C₀(AsymptoticTime, B)) t =
      (g : C₀(ℝ≥0, B)) (timeHomeomorphNNReal t) :=
  rfl

/-- **Inverse value of a translated cone-kernel function.**

Let B be a nonunital complex C-star algebra and F∈C₀([1,∞),B) satisfy F(1)=0. For u≥0,
(conePointKernelEquiv B).symm F u=F(u+1).
-/
theorem conePointKernelEquiv_symm_apply
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) (u : ℝ≥0) :
    ((conePointKernelEquiv B).symm f : C₀(ℝ≥0, B)) u =
      (f : C₀(AsymptoticTime, B)) (timeHomeomorphNNReal.symm u) :=
  rfl

/-- **Open-interval suspension as the initial-time vanishing ideal.**

Let B be a nonunital complex C-star algebra and T=[1,∞). Write J0={F∈C₀(T,B):F(1)=0}, with the
inherited supremum norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for
t>1; its inverse is R⁻¹(F)(s)=F(1/s). The map openIntervalKernelEquiv B:C₀((0,1),B)≃⋆ₐ[ℂ]J0 is
this reciprocal-coordinate equivalence, preserving the supremum norm.
-/
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

/-- **Reciprocal suspension function vanishes at the initial time.**

Let B be a nonunital complex C-star algebra and f∈C₀((0,1),B). The function
openIntervalKernelEquiv B f∈C₀([1,∞),B) has value zero at t=1.
-/
theorem openIntervalKernelEquiv_one (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (openIntervalKernelEquiv B f : C₀(AsymptoticTime, B)) ⟨1, le_rfl⟩ = 0 :=
  (ZeroAtInftyContinuousMap.mem_vanishingAt _ _).1
    (openIntervalKernelEquiv B f).property

/-- **Interior value of the reciprocal suspension function.**

Let B be a nonunital complex C-star algebra, f∈C₀((0,1),B) and t>1. Then
openIntervalKernelEquiv B f t=f(1/t).
-/
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

/-- **Inverse value of the reciprocal suspension function.**

Let B be a nonunital complex C-star algebra and F∈C₀([1,∞),B) satisfy F(1)=0. For s∈(0,1),
(openIntervalKernelEquiv B).symm F s=F(1/s).
-/
theorem openIntervalKernelEquiv_symm_apply
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) (s : Ioo (0 : ℝ) 1) :
    (openIntervalKernelEquiv B).symm f s =
      (f : C₀(AsymptoticTime, B))
        (timeHomeomorphNNReal.symm
          (positiveNNRealReciprocalHomeomorph.symm s : ℝ≥0)) :=
  rfl

end ConeTransport

/-!
## Closed ideal of zero initial evaluation

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Evaluation at time one is ev_1(a,F)=F(1); its kernel is
the closed ideal Eφ.
-/

section AnchoredPullback

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (φ : AsymptoticMorphism A B)

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

/-- **Closed initial-evaluation ideal.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The ideal initialEvaluationIdeal φ is
ker(ev_1)={d=(a,F)∈Dφ:F(1)=0}.
-/
def initialEvaluationIdeal :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    ClosedStarIdeal (FullTimePullback φ) :=
  ClosedStarIdeal.ker (evaluation φ ⟨1, le_rfl⟩)

/-- **Membership in the initial-evaluation ideal.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For d=(a,F)∈Dφ, d∈initialEvaluationIdeal φ if and only if
evaluation φ 1 d=F(1)=0.
-/
@[simp]
theorem mem_initialEvaluationIdeal (d : FullTimePullback φ) :
    d ∈ initialEvaluationIdeal φ ↔ evaluation φ ⟨1, le_rfl⟩ d = 0 :=
  ClosedStarIdeal.mem_ker (evaluation φ ⟨1, le_rfl⟩) d

/-- **Carrier of the initial-evaluation kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. InitialEvaluationKernel φ is Eφ with the nonunital C-star
structure of this closed ideal.
-/
abbrev InitialEvaluationKernel : Type (max uA uB) :=
  (initialEvaluationIdeal φ).carrier

/-- **Coefficient projection restricted to the initial kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The nonunital complex star homomorphism initialProjection
φ:Eφ→A is p0(a,F)=a.
-/
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

/-- **Value of the restricted coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For d=(a,F)∈Eφ, initialProjection φ d=projection φ
d.val=a.
-/
theorem initialProjection_apply (d : InitialEvaluationKernel φ) :
    initialProjection φ d = projection φ d.val :=
  rfl

/-- **Initial-time-zero set section of the coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The set section s0(a)=(a,t↦φ_t(a)-exp(1-t)•φ_1(a)) belongs
to Eφ and satisfies p0(s0(a))=a. This is initialSetSection φ; the exponential correction
belongs to C₀(T,B), so it leaves the quotient class Φφ(a) unchanged.
-/
def initialSetSection (a : A) : InitialEvaluationKernel φ :=
  ⟨setSection φ a - kernelInclusion φ
      (coneTimeEquiv B (CStarKTheory.Cone.endpointLift (φ ⟨1, le_rfl⟩ a))), by
    apply (mem_initialEvaluationIdeal φ _).2
    rw [map_sub, evaluation_setSection, evaluation_kernelInclusion,
      coneTimeEquiv_one, CStarKTheory.Cone.endpointLift_zero, sub_self]⟩

/-- **Ambient value of the initial-time-zero section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Let s(a)=(a,t↦φ_t(a))∈Dφ and k(F)=(0,F) for F∈C₀(T,B).
Then (initialSetSection φ a).val=s(a)-k(t↦exp(1-t)•φ_1(a)); the correction is coneTimeEquiv B
(Cone.endpointLift(φ_1(a))).
-/
theorem initialSetSection_val (a : A) :
    (initialSetSection φ a).val = setSection φ a - kernelInclusion φ
      (coneTimeEquiv B (CStarKTheory.Cone.endpointLift (φ ⟨1, le_rfl⟩ a))) :=
  rfl

/-- **Initial evaluation of the corrected section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The set section s0(a)=(a,t↦φ_t(a)-exp(1-t)•φ_1(a)) belongs
to Eφ and satisfies p0(s0(a))=a. For a∈A, evaluation φ 1 (initialSetSection φ a).val=0.
-/
theorem evaluation_initialSetSection (a : A) :
    evaluation φ ⟨1, le_rfl⟩ (initialSetSection φ a).val = 0 :=
  (mem_initialEvaluationIdeal φ _).1 (initialSetSection φ a).property

/-- **Coefficient of the corrected initial section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The set section s0(a)=(a,t↦φ_t(a)-exp(1-t)•φ_1(a)) belongs
to Eφ and satisfies p0(s0(a))=a. For a∈A, initialProjection φ (initialSetSection φ a)=a.
-/
@[simp]
theorem initialProjection_initialSetSection (a : A) :
    initialProjection φ (initialSetSection φ a) = a := by
  rw [initialProjection_apply, initialSetSection_val, map_sub,
    projection_setSection, projection_kernelInclusion, sub_zero]

/-- **Surjectivity of the initial-kernel coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The map initialProjection φ:Eφ→A is surjective, with
section a↦(a,t↦φ_t(a)-exp(1-t)•φ_1(a)).
-/
theorem initialProjection_surjective : Function.Surjective (initialProjection φ) :=
  fun a ↦ ⟨initialSetSection φ a, initialProjection_initialSetSection φ a⟩

/-- **Inclusion of initial-time-zero vanishing functions.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. The nonunital complex star homomorphism actualKernelInclusion φ:J0→Eφ is F↦(0,F).
-/
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

/-- **Ambient value of the initial-time-zero kernel inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For F∈J0, (actualKernelInclusion φ F).val=kernelInclusion φ F=(0,F) in Dφ.
-/
theorem actualKernelInclusion_val
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) :
    (actualKernelInclusion φ f).val = kernelInclusion φ f.val :=
  rfl

/-- **Coefficient projection kills the initial-time-zero kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For F∈J0, initialProjection φ (actualKernelInclusion φ F)=0.
-/
@[simp]
theorem initialProjection_actualKernelInclusion
    (f : (ZeroAtInftyContinuousMap.vanishingAt (A := B)
      (⟨1, le_rfl⟩ : AsymptoticTime)).carrier) :
    initialProjection φ (actualKernelInclusion φ f) = 0 := by
  rw [initialProjection_apply, actualKernelInclusion_val, projection_kernelInclusion]

/-- **Injectivity of the initial-time-zero kernel inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. The homomorphism actualKernelInclusion φ:J0→Eφ, F↦(0,F), is injective.
-/
theorem actualKernelInclusion_injective : Function.Injective (actualKernelInclusion φ) := by
  intro f g h
  apply Subtype.ext
  apply kernelInclusion_injective φ
  exact congrArg Subtype.val h

/-- **Exact initial-kernel sequence with the vanishing ideal.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For k0(F)=(0,F), range(k0)=ker(p0), so J0→Eφ→A is exact.
-/
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

/-- **Suspension inclusion into the initial-evaluation kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). The nonunital complex star homomorphism initialSuspensionInclusion
φ:C₀((0,1),B)→Eφ sends f to (0,R(f)).
-/
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

/-- **Ambient value of the reciprocal suspension inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). For f∈C₀((0,1),B), (initialSuspensionInclusion φ f).val=kernelInclusion φ
R(f)=(0,R(f)) in Dφ.
-/
theorem initialSuspensionInclusion_val (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (initialSuspensionInclusion φ f).val =
      kernelInclusion φ (openIntervalKernelEquiv B f).val :=
  rfl

/-- **Initial evaluation of the suspension inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For f∈C₀((0,1),B), the element initialSuspensionInclusion
φ f∈Eφ has evaluation zero at t=1.
-/
theorem initialSuspensionInclusion_one (f : C₀(Ioo (0 : ℝ) 1, B)) :
    evaluation φ ⟨1, le_rfl⟩ (initialSuspensionInclusion φ f).val = 0 :=
  (mem_initialEvaluationIdeal φ _).1 (initialSuspensionInclusion φ f).property

/-- **Interior evaluation of the suspension inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For f∈C₀((0,1),B) and t>1, evaluation φ t
(initialSuspensionInclusion φ f).val=f(1/t).
-/
theorem initialSuspensionInclusion_apply_of_one_lt
    (f : C₀(Ioo (0 : ℝ) 1, B)) {t : AsymptoticTime} (ht : 1 < (t : ℝ)) :
    evaluation φ t (initialSuspensionInclusion φ f).val =
      f ⟨1 / (t : ℝ),
        div_pos zero_lt_one (lt_trans zero_lt_one ht),
        (div_lt_one (lt_trans zero_lt_one ht)).2 ht⟩ := by
  rw [initialSuspensionInclusion_val, evaluation_kernelInclusion]
  exact openIntervalKernelEquiv_apply_of_one_lt B f ht

/-- **Injectivity of the reciprocal suspension inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). The map initialSuspensionInclusion φ:f↦(0,R(f)) is injective for every
asymptotic family φ, including zero or nonfaithful families.
-/
theorem initialSuspensionInclusion_injective :
    Function.Injective (initialSuspensionInclusion φ) :=
  (actualKernelInclusion_injective φ).comp (openIntervalKernelEquiv B).injective

/-- **Coefficient projection kills the suspension inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For f∈C₀((0,1),B), initialProjection φ
(initialSuspensionInclusion φ f)=0.
-/
@[simp]
theorem initialProjection_initialSuspensionInclusion (f : C₀(Ioo (0 : ℝ) 1, B)) :
    initialProjection φ (initialSuspensionInclusion φ f) = 0 :=
  initialProjection_actualKernelInclusion φ (openIntervalKernelEquiv B f)

/-- **Exact sequence with the reciprocal suspension kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). For i(f)=(0,R(f)), range(i)=ker(p0); thus C₀((0,1),B)→Eφ→A is exact.
-/
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

/-- **C-star extension defined by initial evaluation.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). The extension initialEvaluationExtension φ is 0→C₀((0,1),B)→Eφ→A→0, with
inclusion f↦(0,R(f)) and quotient p0.
-/
def initialEvaluationExtension :
    letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
      _root_.AsymptoticAlgebra.cStarAlgebra B
    CStarExtension.{uA, uB, max uA uB} A C₀(Ioo (0 : ℝ) 1, B) := by
  letI : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact (initialSuspensionInclusion φ) (initialProjection φ)
    (initialSuspensionInclusion_injective φ) (initialProjection_surjective φ)
    (initialSuspensionInclusion_exact φ)

/-- **Middle algebra of the initial-evaluation extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. The middle algebra of initialEvaluationExtension φ is
InitialEvaluationKernel φ=Eφ.
-/
theorem initialEvaluationExtension_middle :
    (initialEvaluationExtension φ).Middle = InitialEvaluationKernel φ :=
  rfl

/-- **Inclusion map of the initial-evaluation extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. Write J0={F∈C₀(T,B):F(1)=0}, with the inherited supremum
norm. For f∈C₀((0,1),B), define R(f)∈J0 by R(f)(1)=0 and R(f)(t)=f(1/t) for t>1; its inverse
is R⁻¹(F)(s)=F(1/s). For f∈C₀((0,1),B), (initialEvaluationExtension φ).inclusion
f=initialSuspensionInclusion φ f=(0,R(f)).
-/
theorem initialEvaluationExtension_inclusion_apply (f : C₀(Ioo (0 : ℝ) 1, B)) :
    (initialEvaluationExtension φ).inclusion f = initialSuspensionInclusion φ f := by
  let : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact_inclusion_apply (initialSuspensionInclusion φ)
    (initialProjection φ) (initialSuspensionInclusion_injective φ)
    (initialProjection_surjective φ) (initialSuspensionInclusion_exact φ) f

/-- **Quotient map of the initial-evaluation extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). Let
Eφ=InitialEvaluationKernel φ={(a,F)∈Dφ:F(1)=0}, a closed ideal with the inherited norm, and
p0:Eφ→A its coefficient projection. For d=(a,F)∈Eφ, (initialEvaluationExtension φ).quotient
d=initialProjection φ d=a.
-/
theorem initialEvaluationExtension_quotient_apply (d : InitialEvaluationKernel φ) :
    (initialEvaluationExtension φ).quotient d = initialProjection φ d := by
  let : NonUnitalCStarAlgebra (InitialEvaluationKernel φ) :=
    ClosedStarIdeal.carrierCStarAlgebra (initialEvaluationIdeal φ)
  exact CStarExtension.ofExact_quotient_apply (initialSuspensionInclusion φ)
    (initialProjection φ) (initialSuspensionInclusion_injective φ)
    (initialProjection_surjective φ) (initialSuspensionInclusion_exact φ) d

end AnchoredPullback

end AsymptoticMorphism.FullTimePullback
