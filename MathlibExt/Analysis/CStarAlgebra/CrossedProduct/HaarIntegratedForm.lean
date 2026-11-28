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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.IntegratedOperator
public import MathlibExt.MeasureTheory.Group.HaarWeightedInversion

/-!
# Haar-integrated covariant representations

Let G be a locally compact topological group with its Borel measurable structure and a regular
left Haar measure μ. Let α act point-norm continuously on a nonunital complex C-star algebra
A, and let ρ=(π,U) be a covariant representation on a complex Hilbert space H. For compactly
supported continuous f:G→A, the bounded operator Iρ(f) is defined by Iρ(f)ξ=∫ s, π(f(s))(Us ξ)
∂μ. Twisted convolution and modular involution satisfy Iρ(f*g)=Iρ(f)Iρ(g) and Iρ(f*)=Iρ(f)*,
and ‖Iρ(f)‖≤∫ s, ‖f(s)‖ ∂μ.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped CompactlySupported CStarAlgebra InnerProductSpace Pointwise

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Multiplicativity of the integrated representation.**

For a left Haar measure μ and a covariant Hilbert-space representation ρ=(π,U) of α, compactly
supported twisted-convolution coefficients satisfy Iρ(f*g)=Iρ(f)Iρ(g), where Iρ(f)ξ=∫ s,
π(f(s))(Us ξ) ∂μ.
-/
theorem haarIntegratedOperator_mul (f g : HaarTwistedCore.Carrier μ α) :
    StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α (f * g)) =
      StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α f) *
        StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α g) := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let fc : C_c(G, A) := HaarTwistedCore.toCc μ α f
  let gc : C_c(G, A) := HaarTwistedCore.toCc μ α g
  let P : A →L[ℂ] (H →L[ℂ] H) :=
    ⟨{ toFun := ρ.algebra
       map_add' := map_add ρ.algebra
       map_smul' := fun c a => map_smul ρ.algebra c a }, map_continuous ρ.algebra⟩
  apply ContinuousLinearMap.ext
  intro ξ
  let K : G → G → H := fun s t =>
    ρ.algebra (HaarTwistedCore.kernel α fc gc s t) ((ρ.group s : H →L[ℂ] H) ξ)
  have hKcont : Continuous K.uncurry :=
    ((map_continuous ρ.algebra).comp
      (HaarTwistedCore.continuous_kernel α fc gc)).clm_apply
        ((ρ.group.continuous_orbit ξ).comp continuous_fst)
  let Sfg : Set G := tsupport fc * tsupport gc
  have hSfgcompact : IsCompact Sfg := fc.hasCompactSupport.mul gc.hasCompactSupport
  have hSfgclosed : IsClosed Sfg :=
    (isClosed_tsupport gc).mul_left_of_isCompact fc.hasCompactSupport
  have hKzero (p : G × G) (hp : p ∉ Sfg ×ˢ tsupport fc) : K p.1 p.2 = 0 := by
    by_cases ht : p.2 ∈ tsupport fc
    · have hs : p.1 ∉ Sfg := fun hs => hp ⟨hs, ht⟩
      have hg : p.2⁻¹ * p.1 ∉ tsupport gc := by
        intro hg
        apply hs
        simpa only [mul_inv_cancel_left] using Set.mul_mem_mul ht hg
      change ρ.algebra (fc p.2 * α p.2 (gc (p.2⁻¹ * p.1)))
        ((ρ.group p.1 : H →L[ℂ] H) ξ) = 0
      rw [image_eq_zero_of_notMem_tsupport hg, α.apply_zero, mul_zero, map_zero]
      rfl
    · change ρ.algebra (HaarTwistedCore.kernel α fc gc p.1 p.2)
        ((ρ.group p.1 : H →L[ℂ] H) ξ) = 0
      rw [HaarTwistedCore.kernel_zero_of_notMem_tsupport_left α fc gc p.1 p.2 ht, map_zero]
      rfl
  have hKcompact : HasCompactSupport K.uncurry :=
    HasCompactSupport.intro' (hSfgcompact.prod fc.hasCompactSupport)
      (hSfgclosed.prod (isClosed_tsupport fc)) hKzero
  have hLeft :
      StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α (f * g)) ξ =
        ∫ s : G, (∫ t : G, K s t ∂μ) ∂μ := by
    rw [StronglyContinuousUnitaryRepresentation.integratedOperator_apply]
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      let L : A →L[ℂ] H :=
        (ContinuousLinearMap.apply ℂ H ((ρ.group s : H →L[ℂ] H) ξ)).comp P
      have hL := L.integral_comp_comm (HaarTwistedCore.integrable_kernel μ α fc gc s)
      change ρ.algebra (HaarTwistedCore.convolution μ α f g s)
        ((ρ.group s : H →L[ℂ] H) ξ) = ∫ t : G, K s t ∂μ
      rw [HaarTwistedCore.convolution_apply]
      change L (∫ t : G, HaarTwistedCore.kernel α fc gc s t ∂μ) =
        ∫ t : G, L (HaarTwistedCore.kernel α fc gc s t) ∂μ
      exact hL.symm
  have hSwap : (∫ s : G, (∫ t : G, K s t ∂μ) ∂μ) =
      ∫ t : G, (∫ s : G, K s t ∂μ) ∂μ :=
    integral_integral_swap_of_hasCompactSupport hKcont hKcompact
  have hRight : (∫ t : G, (∫ s : G, K s t ∂μ) ∂μ) =
      StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra fc
        (StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra gc ξ) := by
    change (∫ t : G, (∫ s : G, K s t ∂μ) ∂μ) =
      ∫ t : G, ρ.algebra (fc t) ((ρ.group t : H →L[ℂ] H)
        (StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra gc ξ)) ∂μ
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      let T : H →L[ℂ] H := ρ.algebra (fc t) * (ρ.group t : H →L[ℂ] H)
      have hPoint (r : G) : K (t * r) t =
          T (ρ.algebra (gc r) ((ρ.group r : H →L[ℂ] H) ξ)) := by
        have hU : (ρ.group (t * r) : H →L[ℂ] H) =
            (ρ.group t : H →L[ℂ] H) * (ρ.group r : H →L[ℂ] H) :=
          congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
            (ρ.group.toMonoidHom.map_mul t r)
        have hu : star (ρ.group t : H →L[ℂ] H) * (ρ.group t : H →L[ℂ] H) = 1 :=
          (ρ.group t).prop.1
        have hCov : ρ.algebra (α t (gc r)) * (ρ.group t : H →L[ℂ] H) =
            (ρ.group t : H →L[ℂ] H) * ρ.algebra (gc r) := by
          rw [← ρ.covariance t (gc r)]
          simp only [mul_assoc, hu, mul_one]
        have hOp :
            ρ.algebra (fc t * α t (gc r)) * (ρ.group (t * r) : H →L[ℂ] H) =
              (ρ.algebra (fc t) * (ρ.group t : H →L[ℂ] H)) * ρ.algebra (gc r) *
                (ρ.group r : H →L[ℂ] H) := by
          rw [map_mul ρ.algebra, hU]
          calc
            (ρ.algebra (fc t) * ρ.algebra (α t (gc r))) *
                ((ρ.group t : H →L[ℂ] H) * (ρ.group r : H →L[ℂ] H)) =
              ρ.algebra (fc t) * (ρ.algebra (α t (gc r)) * (ρ.group t : H →L[ℂ] H)) *
                (ρ.group r : H →L[ℂ] H) := by simp only [mul_assoc]
            _ = ρ.algebra (fc t) *
                ((ρ.group t : H →L[ℂ] H) * ρ.algebra (gc r)) *
                  (ρ.group r : H →L[ℂ] H) := by rw [hCov]
            _ = (ρ.algebra (fc t) * (ρ.group t : H →L[ℂ] H)) * ρ.algebra (gc r) *
                (ρ.group r : H →L[ℂ] H) := by simp only [mul_assoc]
        change ρ.algebra (fc t * α t (gc (t⁻¹ * (t * r))))
          ((ρ.group (t * r) : H →L[ℂ] H) ξ) = _
        rw [inv_mul_cancel_left]
        exact congrArg (fun B : H →L[ℂ] H => B ξ) hOp
      calc
        (∫ s : G, K s t ∂μ) = ∫ r : G, K (t * r) t ∂μ :=
          (integral_mul_left_eq_self (μ := μ) (fun s : G => K s t) t).symm
        _ = ∫ r : G, T (ρ.algebra (gc r) ((ρ.group r : H →L[ℂ] H) ξ)) ∂μ :=
          integral_congr_ae (Eventually.of_forall hPoint)
        _ = T (∫ r : G, ρ.algebra (gc r) ((ρ.group r : H →L[ℂ] H) ξ) ∂μ) :=
          T.integral_comp_comm
            (StronglyContinuousUnitaryRepresentation.integratedVector_integrable
              μ ρ.group ρ.algebra gc ξ)
        _ = ρ.algebra (fc t) ((ρ.group t : H →L[ℂ] H)
            (StronglyContinuousUnitaryRepresentation.integratedOperator
              μ ρ.group ρ.algebra gc ξ)) :=
          rfl
  exact hLeft.trans (hSwap.trans hRight)

/-- **Involution becomes the Hilbert adjoint.**

For the Haar-integrated covariant operator Iρ and a compactly supported coefficient f,
Iρ(f*)=Iρ(f)*. The involution f* is the modularly weighted Haar involution of the
twisted-convolution algebra.
-/
theorem haarIntegratedOperator_star (f : HaarTwistedCore.Carrier μ α) :
    StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α (star f)) =
      star (StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α f)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  let fc : C_c(G, A) := HaarTwistedCore.toCc μ α f
  let F : G → ℂ := fun s =>
    ⟪ξ, ρ.algebra (fc s) ((ρ.group s : H →L[ℂ] H) η)⟫_ℂ
  have hFcont : Continuous F :=
    continuous_const.inner
      (((map_continuous ρ.algebra).comp fc.continuous).clm_apply
        (ρ.group.continuous_orbit η))
  have hFcompact : HasCompactSupport F := by
    refine HasCompactSupport.intro' fc.hasCompactSupport (isClosed_tsupport fc) ?_
    intro s hs
    change ⟪ξ, ρ.algebra (fc s) ((ρ.group s : H →L[ℂ] H) η)⟫_ℂ = 0
    rw [image_eq_zero_of_notMem_tsupport hs, map_zero]
    change ⟪ξ, (0 : H)⟫_ℂ = 0
    simp only [inner_zero_right]
  have hPoint (s : G) :
      ⟪ρ.algebra ((star f) s) ((ρ.group s : H →L[ℂ] H) ξ), η⟫_ℂ =
        (Measure.modularCharacter s : ℝ) • F s⁻¹ := by
    have hu : star (ρ.group s : H →L[ℂ] H) * (ρ.group s : H →L[ℂ] H) = 1 :=
      (ρ.group s).prop.1
    have hCov : ρ.algebra (α s (star (fc s⁻¹))) * (ρ.group s : H →L[ℂ] H) =
        (ρ.group s : H →L[ℂ] H) * star (ρ.algebra (fc s⁻¹)) := by
      rw [← ρ.covariance s (star (fc s⁻¹)), StarHomClass.map_star ρ.algebra (fc s⁻¹)]
      simp only [mul_assoc, hu, mul_one]
    have hInv : star (ρ.group s : H →L[ℂ] H) = (ρ.group s⁻¹ : H →L[ℂ] H) :=
      congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
        (ρ.group.toMonoidHom.map_inv s).symm
    change ⟪ρ.algebra (HaarTwistedCore.crossedStar μ α f s)
      ((ρ.group s : H →L[ℂ] H) ξ), η⟫_ℂ = _
    rw [HaarTwistedCore.crossedStar_apply, map_smul]
    simp only [_root_.smul_apply]
    change ⟪((Measure.modularCharacter s : ℝ) : ℂ) •
      (ρ.algebra (α s (star (fc s⁻¹))) ((ρ.group s : H →L[ℂ] H) ξ) : H), η⟫_ℂ = _
    refine (inner_smul_real_left (𝕜 := ℂ)
      (ρ.algebra (α s (star (fc s⁻¹))) ((ρ.group s : H →L[ℂ] H) ξ))
      η (Measure.modularCharacter s : ℝ)).trans ?_
    change (Measure.modularCharacter s : ℝ) •
      ⟪(ρ.algebra (α s (star (fc s⁻¹))) * (ρ.group s : H →L[ℂ] H)) ξ, η⟫_ℂ = _
    rw [hCov]
    apply congrArg (fun z : ℂ => (Measure.modularCharacter s : ℝ) • z)
    change ⟪(ρ.group s : H →L[ℂ] H) (star (ρ.algebra (fc s⁻¹)) ξ), η⟫_ℂ =
      ⟪ξ, ρ.algebra (fc s⁻¹) ((ρ.group s⁻¹ : H →L[ℂ] H) η)⟫_ℂ
    calc
      _ = ⟪star (ρ.algebra (fc s⁻¹)) ξ, star (ρ.group s : H →L[ℂ] H) η⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right (ρ.group s : H →L[ℂ] H)
          (star (ρ.algebra (fc s⁻¹)) ξ) η).symm
      _ = ⟪ξ, ρ.algebra (fc s⁻¹) (star (ρ.group s : H →L[ℂ] H) η)⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left (ρ.algebra (fc s⁻¹))
          (star (ρ.group s : H →L[ℂ] H) η) ξ
      _ = _ := by rw [hInv]
  have hLeft :
      (∫ s : G, ⟪ρ.algebra ((star f) s) ((ρ.group s : H →L[ℂ] H) ξ), η⟫_ℂ ∂μ) =
        ⟪StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α (star f)) ξ, η⟫_ℂ :=
    ContinuousLinearMap.integral_comp_commSL (by intro r z; simp) (innerSLFlip ℂ η)
      (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α (star f)) ξ)
  have hRight : (∫ s : G, F s ∂μ) =
      ⟪ξ, StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra fc η⟫_ℂ :=
    (innerSL ℂ ξ).integral_comp_comm
      (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra fc η)
  calc
    _ = ∫ s : G, ⟪ρ.algebra ((star f) s) ((ρ.group s : H →L[ℂ] H) ξ), η⟫_ℂ ∂μ := hLeft.symm
    _ = ∫ s : G, (Measure.modularCharacter s : ℝ) • F s⁻¹ ∂μ :=
      integral_congr_ae (Eventually.of_forall hPoint)
    _ = ∫ s : G, F s ∂μ :=
      integral_modularCharacter_smul_inv_of_hasCompactSupport μ hFcont hFcompact
    _ = _ := hRight

/-- **Integrated star-algebra homomorphism.**

For an action α on A and a covariant representation ρ=(π,U) on a complex Hilbert space H, the
compactly supported Haar twisted-convolution algebra maps to bounded operators by f↦Iρ(f),
with Iρ(f)ξ=∫ s, π(f(s))(Us ξ) ∂μ. This map preserves addition, complex scalar multiplication,
multiplication and involution.
-/
def haarIntegratedHom : HaarTwistedCore.Carrier μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
    (HaarTwistedCore.toCc μ α f)
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    rw [StronglyContinuousUnitaryRepresentation.integratedOperator_apply,
      HaarTwistedCore.toCc_zero]
    simp only [CompactlySupportedContinuousMap.zero_apply, map_zero]
    change (∫ _ : G, (0 : H) ∂μ) = (0 : H)
    exact integral_zero G H
  map_add' := by
    intro f g
    rw [HaarTwistedCore.toCc_add]
    exact StronglyContinuousUnitaryRepresentation.integratedOperator_add μ ρ.group ρ.algebra _ _
  map_mul' := haarIntegratedOperator_mul μ ρ
  map_smul' := by
    intro c f
    change StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α (c • f)) =
      c • StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α f)
    rw [HaarTwistedCore.toCc_smul]
    exact StronglyContinuousUnitaryRepresentation.integratedOperator_smul μ ρ.group ρ.algebra _ _
  map_star' := haarIntegratedOperator_star μ ρ

/-- **Operator value of the integrated homomorphism.**

For a compactly supported coefficient f, `haarIntegratedHom μ ρ f` is the bounded operator
whose vector action is ξ↦∫ s, ρ.algebra(f(s))(ρ.group(s)ξ) ∂μ.
-/
@[simp]
theorem haarIntegratedHom_apply (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ f =
      StronglyContinuousUnitaryRepresentation.integratedOperator μ ρ.group ρ.algebra
        (HaarTwistedCore.toCc μ α f) :=
  rfl

/-- **Vector action of the integrated representation.**

Let ρ=(π,U) be a covariant representation of α on the complex Hilbert space H, μ the regular
left Haar measure and f a compactly supported twisted-convolution coefficient. For ξ∈H,
`haarIntegratedHom μ ρ f ξ = ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ`.
-/
theorem haarIntegratedHom_apply_vector (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    haarIntegratedHom μ ρ f ξ =
      ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ :=
  rfl

/-- **L¹ bound for the integrated representation.**

For a compactly supported coefficient f and a covariant Hilbert-space representation ρ, the
operator norm satisfies `‖haarIntegratedHom μ ρ f‖ ≤ ∫ s : G, ‖f s‖ ∂μ`.
-/
theorem norm_haarIntegratedHom_le (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ f‖ ≤ ∫ s : G, ‖f s‖ ∂μ :=
  StronglyContinuousUnitaryRepresentation.norm_integratedOperator_le μ ρ.group ρ.algebra
    (HaarTwistedCore.toCc μ α f)

end

end CovariantRepresentation
