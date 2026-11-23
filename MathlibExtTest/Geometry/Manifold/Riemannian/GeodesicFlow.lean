/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow.VectorSpace
import Mathlib.Dynamics.Flow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the geodesic-flow API on Euclidean space

Checks on a finite-dimensional real inner product space `F` and on the plane
realized as `ℂ`: the straight-line maps satisfy the geodesic-flow predicates,
including time-zero identity, the flow law and geodesic orbits, a Mathlib
`Flow` on the unit tangent bundle of `ℂ` does, value pins, composition pins
for the flow law, and three mutations of the unit flow that fail to be
geodesic flows. On Euclidean space a family with time-zero identity and
geodesic orbits is the straight-line flow, so no example there can fail the
flow law alone.
-/

open Bundle Manifold
open scoped Manifold ContDiff

namespace GeodesicFlowTests

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Straight-line flow on the tangent bundle of `F`, satisfying the flow law. -/
def straightLineFlow (t : ℝ) (p : TangentBundle 𝓘(ℝ, F) F) :
    TangentBundle 𝓘(ℝ, F) F :=
  ⟨p.proj + t • NormedSpace.fromTangentSpace p.proj p.snd,
    (NormedSpace.fromTangentSpace
      (p.proj + t • NormedSpace.fromTangentSpace p.proj p.snd)).symm
      (NormedSpace.fromTangentSpace p.proj p.snd)⟩

/-- Straight-line flow on the unit bundle of `F`, satisfying the flow law. -/
def straightLineUnitFlow (t : ℝ)
    (p : Manifold.unitTangentBundle 𝓘(ℝ, F) F) :
    Manifold.unitTangentBundle 𝓘(ℝ, F) F :=
  ⟨straightLineFlow t (p : TangentBundle 𝓘(ℝ, F) F), by
    show ‖(straightLineFlow t (p : TangentBundle 𝓘(ℝ, F) F)).snd‖ = 1
    have hp : ‖(p : TangentBundle 𝓘(ℝ, F) F).snd‖ = 1 := p.2
    have hv : NormedSpace.fromTangentSpace
        (straightLineFlow t (p : TangentBundle 𝓘(ℝ, F) F)).proj
        (straightLineFlow t (p : TangentBundle 𝓘(ℝ, F) F)).snd =
        NormedSpace.fromTangentSpace (p : TangentBundle 𝓘(ℝ, F) F).proj
          (p : TangentBundle 𝓘(ℝ, F) F).snd := rfl
    rw [norm_tangentSpace_vectorSpace, hv, ← norm_tangentSpace_vectorSpace]
    exact hp⟩

/-- The straight-line map is the geodesic flow of `F`, including the flow law. -/
theorem straightLineFlow_isGeodesicFlow :
    Manifold.IsGeodesicFlow 𝓘(ℝ, F) straightLineFlow := by
  rw [Manifold.isGeodesicFlow_vectorSpace_iff]
  intro t p
  exact ⟨rfl, ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-- The unit straight-line map is the unit geodesic flow of `F`, with the flow law. -/
theorem straightLineUnitFlow_isUnitGeodesicFlow :
    Manifold.IsUnitGeodesicFlow 𝓘(ℝ, F) straightLineUnitFlow := by
  rw [Manifold.isUnitGeodesicFlow_vectorSpace_iff]
  intro t p
  exact ⟨rfl, ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-- Total straight-line map of the plane via the model homeomorph, with the flow law. -/
def planeTotalFlow (t : ℝ) (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm
    (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).1 +
      t • (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2),
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2)

/-- Unit straight-line map of the plane, satisfying the flow law. -/
def planeUnitFlow (t : ℝ)
    (p : Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨planeTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ), by
    show ‖(planeTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd‖ = 1
    have hp : ‖(p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd‖ = 1 := p.2
    have hEq : NormedSpace.fromTangentSpace
        (planeTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj
        (planeTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd =
        NormedSpace.fromTangentSpace (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
          (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd := rfl
    rw [norm_tangentSpace_vectorSpace, hEq, ← norm_tangentSpace_vectorSpace]
    exact hp⟩

/-- Flow law for the total straight-line map of the plane. -/
theorem planeTotal_add (t₁ t₂ : ℝ)
    (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    planeTotalFlow (t₁ + t₂) p =
      planeTotalFlow t₁ (planeTotalFlow t₂ p) := by
  have hH : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
      (planeTotalFlow (t₁ + t₂) p) =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
        (planeTotalFlow t₁ (planeTotalFlow t₂ p)) := by
    simp only [planeTotalFlow, Homeomorph.apply_symm_apply]
    apply Prod.ext
    · simp only [add_smul]
      abel
    · rfl
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).injective hH

/-- Time zero is the identity for the total straight-line map. -/
theorem planeTotal_zero (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    planeTotalFlow 0 p = p := by
  have hH : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
      (planeTotalFlow 0 p) =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) p := by
    simp only [planeTotalFlow, Homeomorph.apply_symm_apply]
    simp
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).injective hH

/-- The unit straight-line flow of the plane as a Mathlib `Flow` with its flow law. -/
def planeFlow : Flow ℝ (Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) where
  toFun := planeUnitFlow
  cont' := by
    have hFst : Continuous (fun tp : ℝ × TangentBundle 𝓘(ℝ, ℂ) ℂ ↦
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).1 +
          tp.1 • ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).2) := by
      fun_prop
    have hSnd : Continuous (fun tp : ℝ × TangentBundle 𝓘(ℝ, ℂ) ℂ ↦
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).2) := by
      fun_prop
    have hInner := hFst.prodMk hSnd
    have hSym :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm.continuous.comp
        hInner
    have hEqFun : Function.uncurry planeTotalFlow =
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm ∘
          (fun tp : ℝ × TangentBundle 𝓘(ℝ, ℂ) ℂ ↦
            (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).1 +
              tp.1 • ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).2,
            ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) tp.2).2)) := rfl
    have hTotal : Continuous (Function.uncurry planeTotalFlow) := by
      rw [hEqFun]
      exact hSym
    have hBase : Continuous (fun tp :
        ℝ × Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ ↦
        planeTotalFlow tp.1 (tp.2 : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
      hTotal.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))
    exact Continuous.subtype_mk hBase
      (fun tp ↦ (planeUnitFlow tp.1 tp.2).2)
  map_add' := by
    intro t₁ t₂ x
    apply Subtype.ext
    show planeTotalFlow (t₁ + t₂) (x : TangentBundle 𝓘(ℝ, ℂ) ℂ) =
      planeTotalFlow t₁ (planeTotalFlow t₂ (x : TangentBundle 𝓘(ℝ, ℂ) ℂ))
    exact planeTotal_add t₁ t₂ _
  map_zero' := by
    intro x
    apply Subtype.ext
    show planeTotalFlow 0 (x : TangentBundle 𝓘(ℝ, ℂ) ℂ) =
      (x : TangentBundle 𝓘(ℝ, ℂ) ℂ)
    exact planeTotal_zero _

/-- The coercion of the plane flow is the unit geodesic flow, including the flow law. -/
theorem planeFlow_isUnitGeodesicFlow :
    Manifold.IsUnitGeodesicFlow 𝓘(ℝ, ℂ) ⇑planeFlow := by
  have hEq : ⇑planeFlow = planeUnitFlow := rfl
  rw [hEq, Manifold.isUnitGeodesicFlow_vectorSpace_iff]
  intro t p
  exact ⟨rfl, rfl⟩

/-- The tangent vector `⟨0, 1⟩` of the plane. -/
def planeUnitVec : TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨0, (NormedSpace.fromTangentSpace (0 : ℂ)).symm 1⟩

/-- The vector `⟨0, 1⟩` is a unit tangent vector of the plane. -/
theorem planeUnitVec_mem :
    planeUnitVec ∈ Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ := by
  show ‖planeUnitVec.snd‖ = 1
  have h : NormedSpace.fromTangentSpace
      planeUnitVec.proj planeUnitVec.snd = 1 :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have h1 : ‖NormedSpace.fromTangentSpace
      planeUnitVec.proj planeUnitVec.snd‖ = 1 := by
    rw [h]
    exact norm_one
  rw [← h1, norm_tangentSpace_vectorSpace]

/-- The unit vector `⟨0, 1⟩` as a point of the unit bundle. -/
def planeUnitVecSub : Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨planeUnitVec, planeUnitVec_mem⟩

/-- The plane flow at time `3` from `⟨0, 1⟩` has basepoint `3`. -/
theorem planeFlow_time3_base :
    ((planeFlow 3 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 3 := by
  have hEq : (((planeFlow 3 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)) = planeTotalFlow 3 planeUnitVec := rfl
  have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
  have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).1 = 0 := rfl
  have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).2 = 1 := rfl
  rw [hEq, hFst]
  simp only [planeTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
  norm_num [smul_eq_mul]

/-- The plane flow at time `3` from `⟨0, 1⟩` has fiber `1`. -/
theorem planeFlow_time3_fiber :
    NormedSpace.fromTangentSpace
      ((planeFlow 3 planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
      ((planeFlow 3 planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).snd = 1 := rfl

/-- Composition pin for the flow law on the plane flow: `2` then `3` give base `5`. -/
theorem planeFlow_comp_base :
    ((planeFlow 2 (planeFlow 3 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 5 ∧
    ((planeFlow 2 (planeFlow 3 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj =
      ((planeFlow 5 planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj := by
  have hComp : (((planeFlow 2 (planeFlow 3 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)) =
      planeTotalFlow 2 (planeTotalFlow 3 planeUnitVec) := rfl
  have hFive : (((planeFlow 5 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)) = planeTotalFlow 5 planeUnitVec := rfl
  have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
  have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).1 = 0 := rfl
  have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).2 = 1 := rfl
  have hComp5 : ((planeFlow 2 (planeFlow 3 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 5 := by
    rw [hComp, hFst]
    simp only [planeTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
    norm_num [smul_eq_mul]
  have hFive5 : ((planeFlow 5 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 5 := by
    rw [hFive, hFst]
    simp only [planeTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
    norm_num [smul_eq_mul]
  exact ⟨hComp5, hComp5.trans hFive5.symm⟩

/-- Instance of the flow law for the plane flow at times `2` and `3`. -/
theorem planeFlow_mapAdd_2_3 :
    (⇑planeFlow) (2 + 3) planeUnitVecSub =
      (⇑planeFlow) 2 ((⇑planeFlow) 3 planeUnitVecSub) :=
  planeFlow_isUnitGeodesicFlow.map_add 2 3 planeUnitVecSub

/-- The tangent vector `⟨1, 2⟩` of the plane. -/
def tmVec : TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨1, (NormedSpace.fromTangentSpace (1 : ℂ)).symm 2⟩

/-- The straight-line flow at time `1/2` from `⟨1, 2⟩` has base `2`. -/
theorem tmFlow_half_base :
    (straightLineFlow (1 / 2 : ℝ) tmVec).proj = 2 := by
  have eF : NormedSpace.fromTangentSpace tmVec.proj tmVec.snd = 2 :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have eP : (straightLineFlow (1 / 2 : ℝ) tmVec).proj =
      tmVec.proj + (1 / 2 : ℝ) •
        NormedSpace.fromTangentSpace tmVec.proj tmVec.snd := rfl
  have eB : tmVec.proj = 1 := rfl
  rw [eP, eF, eB]
  norm_num [smul_eq_mul]

/-- The straight-line flow at time `1/2` from `⟨1, 2⟩` has fiber `2`. -/
theorem tmFlow_half_fiber :
    NormedSpace.fromTangentSpace
      (straightLineFlow (1 / 2 : ℝ) tmVec).proj
      (straightLineFlow (1 / 2 : ℝ) tmVec).snd = 2 :=
  ContinuousLinearEquiv.apply_symm_apply _ _

/-- The position vector field `z ↦ z` of the plane. -/
def posField : Π x : ℂ, TangentSpace 𝓘(ℝ, ℂ) x :=
  fun x ↦ (NormedSpace.fromTangentSpace x).symm x

/-- The position field is differentiable at every point as a section. -/
theorem posFieldMDiff (x : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent (T% posField) x := by
  refine (mdifferentiableAt_section 𝓘(ℝ, ℂ) posField).mpr ?_
  have hEq : (fun b : ℂ ↦ ((trivializationAt ℂ
      (TangentSpace 𝓘(ℝ, ℂ)) x) ⟨b, posField b⟩).2) = id := by
    funext b
    show ((trivializationAt ℂ
      (TangentSpace 𝓘(ℝ, ℂ)) x) ⟨b, posField b⟩).2 = b
    rw [trivializationAt_model_space_apply]
    rfl
  rw [hEq]
  exact differentiableAt_id.mdifferentiableAt

/-- The Levi-Civita derivative of the position field is the direction. -/
theorem posField_levi (x : ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, ℂ) ℂ posField x v =
      v := by
  have hConn := CovariantDerivative.leviCivitaConnection_vectorSpace_apply
    (posFieldMDiff x) v
  have hEqFun : (fun y : ℂ ↦ (posField y : ℂ)) = id := by
    funext y
    rfl
  have hHas : HasFDerivAt (fun y : ℂ ↦ (posField y : ℂ))
      (ContinuousLinearMap.id ℝ ℂ) x := by
    rw [hEqFun]
    exact ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ ℂ)
  have hF : fderiv ℝ (fun y : ℂ ↦ (posField y : ℂ)) x =
      ContinuousLinearMap.id ℝ ℂ := hHas.fderiv
  rw [hConn, hF]
  rfl

/-- Total speed-doubled flow of the plane, with its flow law. -/
def doubleTotalFlow (t : ℝ) (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm
    (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).1 +
      (2 * t) • (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2),
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2)

/-- Unit speed-doubled flow of the plane, with its flow law. -/
def doubleUnitFlow (t : ℝ)
    (p : Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨doubleTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ), by
    show ‖(doubleTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd‖ = 1
    have hp : ‖(p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd‖ = 1 := p.2
    have hEq : NormedSpace.fromTangentSpace
        (doubleTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj
        (doubleTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd =
        NormedSpace.fromTangentSpace (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
          (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd := rfl
    rw [norm_tangentSpace_vectorSpace, hEq, ← norm_tangentSpace_vectorSpace]
    exact hp⟩

/-- The speed-doubled flow is the identity at time `0`. -/
theorem doubleUnitFlow_zero (p :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    doubleUnitFlow 0 p = p := by
  apply Subtype.ext
  show doubleTotalFlow 0 (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) =
    (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)
  have hH : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
      (doubleTotalFlow 0 (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)) =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) := by
    simp only [doubleTotalFlow, Homeomorph.apply_symm_apply]
    simp
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).injective hH

/-- The speed-doubled flow is not the unit geodesic flow with its flow law. -/
theorem doubleUnitFlow_notGeodesic :
    ¬ Manifold.IsUnitGeodesicFlow 𝓘(ℝ, ℂ) doubleUnitFlow := by
  intro h
  have hAff :=
    (Manifold.isUnitGeodesicFlow_vectorSpace_iff doubleUnitFlow).mp h
  have h1 := (hAff 1 planeUnitVecSub).1
  have hL : (((doubleUnitFlow 1 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj = 2 := by
    have hEq : (((doubleUnitFlow 1 planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ)) = doubleTotalFlow 1 planeUnitVec := rfl
    have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
    have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        planeUnitVec).1 = 0 := rfl
    have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        planeUnitVec).2 = 1 := rfl
    rw [hEq, hFst]
    simp only [doubleTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
    norm_num [smul_eq_mul]
  have eRhs : ((planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj +
      (1 : ℝ) • NormedSpace.fromTangentSpace
        ((planeUnitVecSub :
          Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
          TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
        ((planeUnitVecSub :
          Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
          TangentBundle 𝓘(ℝ, ℂ) ℂ).snd = 1 := by
    have b0 : ((planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 0 := rfl
    have f0 : NormedSpace.fromTangentSpace
        ((planeUnitVecSub :
          Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
          TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
        ((planeUnitVecSub :
          Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
          TangentBundle 𝓘(ℝ, ℂ) ℂ).snd = 1 :=
      ContinuousLinearEquiv.apply_symm_apply _ _
    rw [f0, b0]
    simp
  have hEq21 : (2 : ℂ) = 1 := hL.symm.trans (h1.trans eRhs)
  have hNe : (2 : ℂ) ≠ 1 := by norm_num
  exact hNe hEq21

/-- Total circular unit-speed flow of the plane, with its flow law. -/
def circTotalFlow (t : ℝ) (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm
    (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).1 -
      Complex.I * (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2 *
        (Complex.exp (t * Complex.I) - 1)),
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2 *
      Complex.exp (t * Complex.I)))

/-- Unit circular flow of the plane, with its flow law. -/
def circUnitFlow (t : ℝ)
    (p : Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨circTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ), by
    show ‖(circTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd‖ = 1
    have hp : ‖(p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd‖ = 1 := p.2
    have hV : ‖(tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2‖ = 1 := by
      have hEq2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
          (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2 =
          NormedSpace.fromTangentSpace (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
            (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd := rfl
      rw [hEq2, ← norm_tangentSpace_vectorSpace]
      exact hp
    have hExp : ‖Complex.exp (↑t * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I t
    have hFib : NormedSpace.fromTangentSpace
        (circTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj
        (circTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd =
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
          (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2 *
          Complex.exp (↑t * Complex.I) := rfl
    rw [norm_tangentSpace_vectorSpace, hFib, norm_mul, hV, hExp, mul_one]⟩

/-- Derivative of the circular base curve with fixed data. -/
theorem circBase_hasDerivAt (X V : ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ X - Complex.I * V * (Complex.exp (↑s * Complex.I) - 1))
      (V * Complex.exp (↑t * Complex.I)) t := by
  have hMulC : HasDerivAt (fun z : ℂ ↦ z * Complex.I) Complex.I (↑t) :=
    hasDerivAt_mul_const _
  have hExpC : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * Complex.I))
      (Complex.exp (↑t * Complex.I) * Complex.I) (↑t) := hMulC.cexp
  have hSubC : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * Complex.I) - 1)
      (Complex.exp (↑t * Complex.I) * Complex.I) (↑t) :=
    hExpC.sub_const 1
  have hMul : HasDerivAt
      (fun z : ℂ ↦ Complex.I * V * (Complex.exp (z * Complex.I) - 1))
      (Complex.I * V * (Complex.exp (↑t * Complex.I) * Complex.I)) (↑t) :=
    HasDerivAt.const_mul _ hSubC
  have hBase : HasDerivAt
      (fun z : ℂ ↦ X - Complex.I * V * (Complex.exp (z * Complex.I) - 1))
      (0 - Complex.I * V * (Complex.exp (↑t * Complex.I) * Complex.I))
      (↑t) := HasDerivAt.fun_sub (hasDerivAt_const _ _) hMul
  have hVal : 0 - Complex.I * V *
      (Complex.exp (↑t * Complex.I) * Complex.I) =
      V * Complex.exp (↑t * Complex.I) := by
    linear_combination (-(V * Complex.exp (↑t * Complex.I)) * Complex.I_mul_I)
  rw [hVal] at hBase
  exact hBase.comp_ofReal

/-- The circular flow is the identity at time `0`. -/
theorem circUnitFlow_zero (p :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    circUnitFlow 0 p = p := by
  apply Subtype.ext
  show circTotalFlow 0 (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) =
    (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)
  have hH : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
      (circTotalFlow 0 (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)) =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ))
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) := by
    simp only [circTotalFlow, Homeomorph.apply_symm_apply]
    simp [Complex.exp_zero]
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).injective hH

/-- Every circular orbit satisfies the velocity link at every time. -/
theorem circUnitFlow_velocityLink (p :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun s ↦ (↑(circUnitFlow s p) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj) t
      (ContinuousLinearMap.toSpanSingleton ℝ
        (↑(circUnitFlow t p) :
          TangentBundle 𝓘(ℝ, ℂ) ℂ).snd) := by
  have hBase : HasDerivAt
      (fun s : ℝ ↦ (↑(circUnitFlow s p) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj)
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2 *
        Complex.exp (↑t * Complex.I)) t :=
    circBase_hasDerivAt _ _ _
  have hFib : ((↑(circUnitFlow t p) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).snd : ℂ) =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2 *
        Complex.exp (↑t * Complex.I) := rfl
  rw [← hFib] at hBase
  exact hasMFDerivAt_iff_hasFDerivAt.mpr hBase.hasFDerivAt

/-- The circular flow is not the unit geodesic flow with its flow law. -/
theorem circUnitFlow_notGeodesic :
    ¬ Manifold.IsUnitGeodesicFlow 𝓘(ℝ, ℂ) circUnitFlow := by
  intro h
  have hAff :=
    (Manifold.isUnitGeodesicFlow_vectorSpace_iff circUnitFlow).mp h
  have h2 := (hAff Real.pi planeUnitVecSub).2
  have hFib : NormedSpace.fromTangentSpace
      ((circUnitFlow Real.pi planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
      ((circUnitFlow Real.pi planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).snd =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) planeUnitVec).2 *
        Complex.exp (↑Real.pi * Complex.I) := rfl
  have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).2 = 1 := rfl
  have e2 : Complex.exp (↑Real.pi * Complex.I) = -1 :=
    Complex.exp_pi_mul_I
  have hL : NormedSpace.fromTangentSpace
      ((circUnitFlow Real.pi planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
      ((circUnitFlow Real.pi planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).snd = -1 := by
    rw [hFib, c2, e2, one_mul]
  have hR : NormedSpace.fromTangentSpace
      ((planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
      ((planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ).snd = 1 :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have hNe : (-1 : ℂ) ≠ 1 := by norm_num
  exact hNe (hL.symm.trans (h2.trans hR))

/-- Total shifted-start flow of the plane, breaking time-zero identity and the flow law. -/
def shiftTotalFlow (t : ℝ) (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) :
    TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm
    (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).1 +
      (t + 1) • (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2),
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ) p).2)

/-- Unit shifted-start flow of the plane, breaking time-zero identity and the flow law. -/
def shiftUnitFlow (t : ℝ)
    (p : Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ :=
  ⟨shiftTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ), by
    show ‖(shiftTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd‖ = 1
    have hp : ‖(p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd‖ = 1 := p.2
    have hEq : NormedSpace.fromTangentSpace
        (shiftTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj
        (shiftTotalFlow t (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd =
        NormedSpace.fromTangentSpace (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).proj
          (p : TangentBundle 𝓘(ℝ, ℂ) ℂ).snd := rfl
    rw [norm_tangentSpace_vectorSpace, hEq, ← norm_tangentSpace_vectorSpace]
    exact hp⟩

/-- Every shifted-start orbit is a geodesic velocity curve, though the flow law fails. -/
theorem shiftUnitFlow_orbitGeodesic (p :
    Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
    Manifold.IsGeodesicVelocityCurve 𝓘(ℝ, ℂ)
      (fun t ↦ (↑(shiftUnitFlow t p) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ)) := by
  rw [Manifold.isGeodesicVelocityCurve_vectorSpace_iff]
  intro t
  refine ⟨?_, rfl⟩
  have hEq : ∀ s, (↑(shiftUnitFlow s p) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ) =
      shiftTotalFlow s (p : TangentBundle 𝓘(ℝ, ℂ) ℂ) := fun s => rfl
  have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
  have hFib : ∀ s, NormedSpace.fromTangentSpace
      (shiftTotalFlow s (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj
      (shiftTotalFlow s (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).snd =
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        (p : TangentBundle 𝓘(ℝ, ℂ) ℂ)).2 := fun s => rfl
  rw [hEq t, hEq 0, hFib 0, hFst, hFst]
  simp only [shiftTotalFlow, Homeomorph.apply_symm_apply]
  simp only [add_smul, one_smul, zero_add]
  abel

/-- The shifted-start flow is not the unit geodesic flow; time-zero and flow law fail. -/
theorem shiftUnitFlow_notGeodesic :
    ¬ Manifold.IsUnitGeodesicFlow 𝓘(ℝ, ℂ) shiftUnitFlow := by
  intro h
  have h0 := h.map_zero planeUnitVecSub
  have hProj := congrArg (fun q :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ ↦
      ((q : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj) h0
  have hL : (((shiftUnitFlow 0 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj = 1 := by
    have hEq : (((shiftUnitFlow 0 planeUnitVecSub :
        Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
        TangentBundle 𝓘(ℝ, ℂ) ℂ)) = shiftTotalFlow 0 planeUnitVec := rfl
    have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
    have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        planeUnitVec).1 = 0 := rfl
    have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
        planeUnitVec).2 = 1 := rfl
    rw [hEq, hFst]
    simp only [shiftTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
    simp
  have hR : ((planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 0 := rfl
  rw [hL, hR] at hProj
  norm_num at hProj

/-- Counterexample pin for the flow law: shifted-start `1` then `1` give base `4`. -/
theorem shiftUnitFlow_comp_base :
    ((shiftUnitFlow 1 (shiftUnitFlow 1 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 4 := by
  have hEq : (((shiftUnitFlow 1 (shiftUnitFlow 1 planeUnitVecSub) :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)) =
      shiftTotalFlow 1 (shiftTotalFlow 1 planeUnitVec) := rfl
  have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
  have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).1 = 0 := rfl
  have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).2 = 1 := rfl
  rw [hEq, hFst]
  simp only [shiftTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
  norm_num [smul_eq_mul]

/-- Counterexample pin for the flow law: shifted-start time `2` gives base `3`. -/
theorem shiftUnitFlow_two_base :
    ((shiftUnitFlow 2 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ).proj = 3 := by
  have hEq : (((shiftUnitFlow 2 planeUnitVecSub :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ) :
      TangentBundle 𝓘(ℝ, ℂ) ℂ)) = shiftTotalFlow 2 planeUnitVec := rfl
  have hFst : ∀ q : TangentBundle 𝓘(ℝ, ℂ) ℂ, q.proj =
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)) q).1 := fun q => rfl
  have c1 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).1 = 0 := rfl
  have c2 : (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)
      planeUnitVec).2 = 1 := rfl
  rw [hEq, hFst]
  simp only [shiftTotalFlow, Homeomorph.apply_symm_apply, c1, c2]
  norm_num [smul_eq_mul]

/-- The shifted-start family fails the flow law at times `1` and `1`. -/
theorem shiftUnitFlow_noFlowLaw :
    ¬ ∀ t s v, shiftUnitFlow (t + s) v =
      shiftUnitFlow t (shiftUnitFlow s v) := by
  intro h
  have h11 := h 1 1 planeUnitVecSub
  have hEq : (1 : ℝ) + 1 = 2 := by norm_num
  rw [hEq] at h11
  have hP := congrArg (fun q :
      Manifold.unitTangentBundle 𝓘(ℝ, ℂ) ℂ ↦
      ((q : TangentBundle 𝓘(ℝ, ℂ) ℂ)).proj) h11
  rw [shiftUnitFlow_two_base, shiftUnitFlow_comp_base] at hP
  have hNe : (3 : ℂ) ≠ 4 := by norm_num
  exact hNe hP

end

end GeodesicFlowTests
