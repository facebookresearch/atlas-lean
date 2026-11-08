/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow
public import MathlibExt.Geometry.Manifold.Riemannian.LeviCivitaVectorSpace
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Geodesic flow of Euclidean space

Let `F` be a finite-dimensional real inner product space with its standard metric.
This file characterizes the geodesic-flow predicates on `F`: a velocity curve is
geodesic iff its base point moves affinely with constant velocity, so the flow is
the straight-line flow. Hence the predicates are satisfiable on Euclidean space and
pin down the straight-line flow there. Chapter reference: do Carmo, Riemannian
Geometry, Ch. 3. No flow object is defined here.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem const_of_hasDerivAt_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : ℝ → G} (h : ∀ t, HasDerivAt f 0 t) (x y : ℝ) :
    f x = f y := by
  have hDiff : Differentiable ℝ f := fun t => (h t).differentiableAt
  have hDeriv : ∀ t, deriv f t = 0 := fun t => (h t).deriv
  exact is_const_of_deriv_eq_zero hDiff hDeriv x y

private theorem affine_of_hasDerivAt_const {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : ℝ → G} {v0 : G} (h : ∀ t, HasDerivAt f v0 t)
    (t : ℝ) : f t = f 0 + t • v0 := by
  have hSmul : ∀ s, HasDerivAt (fun r : ℝ => r • v0) v0 s := by
    intro s
    simpa using HasDerivAt.smul_const (hasDerivAt_id s) v0
  have hSub : ∀ s, HasDerivAt (fun r => f r - r • v0) 0 s := by
    intro s
    simpa using HasDerivAt.fun_sub (h s) (hSmul s)
  have hC := const_of_hasDerivAt_zero hSub t 0
  have hC0 : f t - t • v0 = f 0 := by simpa using hC
  exact (sub_eq_iff_eq_add).mp hC0

private theorem fiber_const_of_geodesic (u : ℝ → TangentBundle 𝓘(ℝ, F) F)
    (hGeo : Manifold.IsGeodesicVelocityCurve 𝓘(ℝ, F) u) (s : ℝ) :
    NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) =
      NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) := by
  have hInnerConst : ∀ (a0 : F) (x y : ℝ),
      inner ℝ (NormedSpace.fromTangentSpace ((u x).proj) ((u x).snd)) a0 =
      inner ℝ (NormedSpace.fromTangentSpace ((u y).proj) ((u y).snd)) a0 := by
    intro a0 x y
    set w : TangentSpace 𝓘(ℝ, F) ((u 0).proj) :=
      (NormedSpace.fromTangentSpace ((u 0).proj)).symm a0
    have hWdiff : ∀ z, MDiffAt (T% (FiberBundle.extend F w)) z :=
      fun z => FiberBundle.mdifferentiableAt_extend_model_space _ z
    have hLeviZero : ∀ tt, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F
        (FiberBundle.extend F w) ((u tt).proj) ((u tt).snd) = 0 := by
      intro tt
      have h0CLM : CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F
          (FiberBundle.extend F w) ((u tt).proj) = 0 :=
        CovariantDerivative.leviCivitaConnection_extend_vectorSpace _ _
      simp [h0CLM]
    have hGeoAll : ∀ (tt : ℝ), HasDerivAt (fun s => inner ℝ (u s).snd
        (FiberBundle.extend F w ((u s).proj))) 0 tt := by
      intro tt
      have hH := hGeo.hasDerivAt_inner tt _ (hWdiff ((u tt).proj))
      have hVal : inner ℝ (u tt).snd
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F
            (FiberBundle.extend F w) ((u tt).proj) ((u tt).snd)) = 0 := by
        rw [hLeviZero tt]
        simp
      rwa [hVal] at hH
    have eExt : ∀ s, (NormedSpace.fromTangentSpace ((u s).proj))
        (FiberBundle.extend F w ((u s).proj)) = a0 := by
      intro s
      rw [FiberBundle.extend_model_space]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hBridge : ∀ s, inner ℝ (u s).snd
        (FiberBundle.extend F w ((u s).proj)) =
        inner ℝ (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd)) a0 := by
      intro s
      have hRfl : inner ℝ (u s).snd (FiberBundle.extend F w ((u s).proj)) =
          inner ℝ (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd))
            ((NormedSpace.fromTangentSpace ((u s).proj))
              (FiberBundle.extend F w ((u s).proj))) := rfl
      rw [hRfl, eExt s]
    have hDeriv : ∀ tt, HasDerivAt (fun s => inner ℝ
        (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd)) a0) 0 tt := by
      intro tt
      have hTt := hGeoAll tt
      rw [funext hBridge] at hTt
      exact hTt
    exact const_of_hasDerivAt_zero hDeriv x y
  have hKey := hInnerConst
    (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) -
      NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) s 0
  have hSub : inner ℝ
      (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) -
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd))
      (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) -
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) = 0 := by
    have hEq : inner ℝ (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd))
        (_ - _) - inner ℝ (NormedSpace.fromTangentSpace ((u 0).proj)
        ((u 0).snd)) (_ - _) = 0 := sub_eq_zero.mpr hKey
    rwa [← inner_sub_left] at hEq
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hSub)

namespace Manifold

/-- A velocity curve on Euclidean space is geodesic iff the base point is affine
with constant velocity and the fiber is constant as an element of `F`. -/
theorem isGeodesicVelocityCurve_vectorSpace_iff
    (u : ℝ → TangentBundle 𝓘(ℝ, F) F) :
    IsGeodesicVelocityCurve 𝓘(ℝ, F) u ↔ ∀ t,
      (u t).proj = (u 0).proj +
        t • NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) ∧
      NormedSpace.fromTangentSpace ((u t).proj) ((u t).snd) =
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) := by
  constructor
  · intro hGeo t
    have hFib : ∀ s, NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) =
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) :=
      fun s => fiber_const_of_geodesic u hGeo s
    have hDerivConst : ∀ t, HasDerivAt (fun s => (u s).proj)
        (NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) t := by
      intro t
      have hF : HasFDerivAt (fun s => (u s).proj)
          (ContinuousLinearMap.toSpanSingleton ℝ (u t).snd) t :=
        hasMFDerivAt_iff_hasFDerivAt.mp (hGeo.hasMFDerivAt_proj t)
      have hD : HasDerivAt (fun s => (u s).proj) (((u t).snd : F)) t :=
        hasDerivAt_iff_hasFDerivAt.mpr hF
      have hEqF : (((u t).snd : F)) =
          NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) := hFib t
      rwa [hEqF] at hD
    exact ⟨affine_of_hasDerivAt_const hDerivConst t, hFib t⟩
  · intro hAff
    have hFibEq : ∀ s, NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) =
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) :=
      fun s => (hAff s).2
    have hProjEqFun : (fun s => (u s).proj) = (fun s => (u 0).proj + s •
        NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) :=
      funext fun s => (hAff s).1
    have hBaseDeriv : ∀ t, HasDerivAt (fun s => (u s).proj)
        (NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) t := by
      intro t
      rw [hProjEqFun]
      have hSm : HasDerivAt (fun s : ℝ => s •
          NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd))
          (NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)) t := by
        simpa using HasDerivAt.smul_const (hasDerivAt_id t)
          (NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd))
      exact HasDerivAt.const_add _ hSm
    constructor
    · intro t
      have hEqF : (((u t).snd : F)) =
          NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) := hFibEq t
      have hD : HasDerivAt (fun s => (u s).proj) (((u t).snd : F)) t := by
        rw [hEqF]
        exact hBaseDeriv t
      exact hasMFDerivAt_iff_hasFDerivAt.mpr hD.hasFDerivAt
    · intro t W hWdiff
      have hConn : CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F W
          ((u t).proj) ((u t).snd) =
          fderiv ℝ W ((u t).proj) ((u t).snd) :=
        CovariantDerivative.leviCivitaConnection_vectorSpace_apply hWdiff _
      set v0 : F := NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd)
      set G : F → F := fun y => NormedSpace.fromTangentSpace y (W y) with hG
      have hTrivEq : (fun b : F => (((trivializationAt F
          (TangentSpace 𝓘(ℝ, F)) ((u t).proj)) ⟨b, W b⟩).2)) = G := by
        funext b
        rw [hG, trivializationAt_model_space_apply]
        rfl
      have hMDiffG : MDiffAt G ((u t).proj) := by
        have hSec : MDiffAt (fun b : F => (((trivializationAt F
            (TangentSpace 𝓘(ℝ, F)) ((u t).proj)) ⟨b, W b⟩).2)) ((u t).proj) :=
          (mdifferentiableAt_section 𝓘(ℝ, F) W).mp hWdiff
        rwa [hTrivEq] at hSec
      have hFDerivG : HasFDerivAt G (fderiv ℝ G ((u t).proj)) ((u t).proj) :=
        (mdifferentiableAt_iff_differentiableAt.mp hMDiffG).hasFDerivAt
      have hComp : HasDerivAt (fun s : ℝ => G ((u s).proj))
          ((fderiv ℝ G ((u t).proj)) v0) t :=
        HasFDerivAt.comp_hasDerivAt t hFDerivG (hBaseDeriv t)
      have hInnerF : HasDerivAt (fun s => inner ℝ v0 (G ((u s).proj)))
          (inner ℝ v0 ((fderiv ℝ G ((u t).proj)) v0)) t := by
        simpa using HasDerivAt.inner ℝ (hasDerivAt_const t v0) hComp
      have hFunEq : (fun s => inner ℝ (u s).snd (W ((u s).proj))) =
          (fun s => inner ℝ v0 (G ((u s).proj))) := by
        funext s
        have r3 : NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd) =
            v0 := hFibEq s
        have hRfl : inner ℝ (u s).snd (W ((u s).proj)) =
            inner ℝ (NormedSpace.fromTangentSpace ((u s).proj) ((u s).snd))
              (G ((u s).proj)) := by
          rw [hG]
          exact rfl
        rw [hRfl, r3]
      have hValEq : inner ℝ v0 ((fderiv ℝ G ((u t).proj)) v0) =
          inner ℝ (u t).snd
            (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F W
              ((u t).proj) ((u t).snd)) := by
        rw [hConn]
        have rV : v0 =
            NormedSpace.fromTangentSpace ((u t).proj) ((u t).snd) :=
          (hFibEq t).symm
        rw [rV]
        exact rfl
      rw [hFunEq, ← hValEq]
      exact hInnerF

/-- The geodesic flow on Euclidean space is the straight-line flow. -/
theorem isGeodesicFlow_vectorSpace_iff
    (φ : ℝ → TangentBundle 𝓘(ℝ, F) F → TangentBundle 𝓘(ℝ, F) F) :
    IsGeodesicFlow 𝓘(ℝ, F) φ ↔ ∀ t p,
      (φ t p).proj = p.proj +
        t • NormedSpace.fromTangentSpace (p.proj) (p.snd) ∧
      NormedSpace.fromTangentSpace ((φ t p).proj) ((φ t p).snd) =
        NormedSpace.fromTangentSpace (p.proj) (p.snd) := by
  constructor
  · intro hFlow t p
    have h6 := (isGeodesicVelocityCurve_vectorSpace_iff
      (fun s => φ s p)).mp (hFlow.isGeodesicVelocityCurve p) t
    rw [hFlow.map_zero p] at h6
    exact h6
  · intro hAff
    have hZero : ∀ v, φ 0 v = v := by
      intro v
      have hP : (φ 0 v).proj = v.proj := by
        have h := (hAff 0 v).1
        simpa using h
      have hF := (hAff 0 v).2
      exact Bundle.TotalSpace.ext hP (heq_of_eq hF)
    have hAdd : ∀ t s v, φ (t + s) v = φ t (φ s v) := by
      intro t s v
      have hL1 := (hAff (t + s) v).1
      have hS1 := (hAff s v).1
      have hS2 := (hAff s v).2
      have hT1 := (hAff t (φ s v)).1
      have hP : (φ (t + s) v).proj = (φ t (φ s v)).proj := by
        rw [hL1, hT1, hS2, hS1, add_smul, add_assoc]
        congr 1
        exact add_comm _ _
      have hF : NormedSpace.fromTangentSpace ((φ (t + s) v).proj)
          ((φ (t + s) v).snd) =
          NormedSpace.fromTangentSpace ((φ t (φ s v)).proj)
            ((φ t (φ s v)).snd) := by
        rw [(hAff (t + s) v).2, (hAff t (φ s v)).2, (hAff s v).2]
      exact Bundle.TotalSpace.ext hP (heq_of_eq hF)
    refine ⟨hZero, hAdd, fun v => ?_⟩
    have hOrb : ∀ t, (φ t v).proj = (φ 0 v).proj + t •
        NormedSpace.fromTangentSpace ((φ 0 v).proj) ((φ 0 v).snd) ∧
        NormedSpace.fromTangentSpace ((φ t v).proj) ((φ t v).snd) =
        NormedSpace.fromTangentSpace ((φ 0 v).proj) ((φ 0 v).snd) :=
      fun t => by rw [hZero v]; exact hAff t v
    exact (isGeodesicVelocityCurve_vectorSpace_iff _).mpr hOrb

/-- The unit geodesic flow on Euclidean space is the straight-line flow. -/
theorem isUnitGeodesicFlow_vectorSpace_iff
    (φ : ℝ → unitTangentBundle 𝓘(ℝ, F) F →
      unitTangentBundle 𝓘(ℝ, F) F) :
    IsUnitGeodesicFlow 𝓘(ℝ, F) φ ↔ ∀ t p,
      (↑(φ t p) : TangentBundle 𝓘(ℝ, F) F).proj =
        (↑p : TangentBundle 𝓘(ℝ, F) F).proj +
          t • NormedSpace.fromTangentSpace
            (↑p : TangentBundle 𝓘(ℝ, F) F).proj
            (↑p : TangentBundle 𝓘(ℝ, F) F).snd ∧
      NormedSpace.fromTangentSpace
          (↑(φ t p) : TangentBundle 𝓘(ℝ, F) F).proj
          (↑(φ t p) : TangentBundle 𝓘(ℝ, F) F).snd =
        NormedSpace.fromTangentSpace
          (↑p : TangentBundle 𝓘(ℝ, F) F).proj
          (↑p : TangentBundle 𝓘(ℝ, F) F).snd := by
  constructor
  · intro hFlow t p
    have h6 := (isGeodesicVelocityCurve_vectorSpace_iff
      (fun s => (↑(φ s p) : TangentBundle 𝓘(ℝ, F) F))).mp
      (hFlow.isGeodesicVelocityCurve p) t
    have hZ : (↑(φ 0 p) : TangentBundle 𝓘(ℝ, F) F) = (↑p : _):= by
      rw [hFlow.map_zero p]
    rw [hZ] at h6
    exact h6
  · intro hAff
    have hZero : ∀ v, φ 0 v = v := by
      intro v
      have hP : (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).proj =
          (↑v : TangentBundle 𝓘(ℝ, F) F).proj := by
        have h := (hAff 0 v).1
        simpa only [zero_smul, add_zero] using h
      have hF : NormedSpace.fromTangentSpace
          (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).proj
          (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).snd =
          NormedSpace.fromTangentSpace
            (↑v : TangentBundle 𝓘(ℝ, F) F).proj
            (↑v : TangentBundle 𝓘(ℝ, F) F).snd := (hAff 0 v).2
      have hV : (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F) =
          (↑v : TangentBundle 𝓘(ℝ, F) F) :=
        Bundle.TotalSpace.ext hP (heq_of_eq hF)
      exact Subtype.ext hV
    have hAdd : ∀ t s v, φ (t + s) v = φ t (φ s v) := by
      intro t s v
      have hL1 := (hAff (t + s) v).1
      have hS1 := (hAff s v).1
      have hS2 := (hAff s v).2
      have hT1 := (hAff t (φ s v)).1
      have hP : (↑(φ (t + s) v) : TangentBundle 𝓘(ℝ, F) F).proj =
          (↑(φ t (φ s v)) : TangentBundle 𝓘(ℝ, F) F).proj := by
        rw [hL1, hT1, hS2, hS1, add_smul, add_assoc]
        congr 1
        exact add_comm _ _
      have hF : NormedSpace.fromTangentSpace
          (↑(φ (t + s) v) : TangentBundle 𝓘(ℝ, F) F).proj
          (↑(φ (t + s) v) : TangentBundle 𝓘(ℝ, F) F).snd =
          NormedSpace.fromTangentSpace
            (↑(φ t (φ s v)) : TangentBundle 𝓘(ℝ, F) F).proj
            (↑(φ t (φ s v)) : TangentBundle 𝓘(ℝ, F) F).snd := by
        rw [(hAff (t + s) v).2, (hAff t (φ s v)).2, (hAff s v).2]
      have hV : (↑(φ (t + s) v) : TangentBundle 𝓘(ℝ, F) F) =
          (↑(φ t (φ s v)) : TangentBundle 𝓘(ℝ, F) F) :=
        Bundle.TotalSpace.ext hP (heq_of_eq hF)
      exact Subtype.ext hV
    refine ⟨hZero, hAdd, fun v => ?_⟩
    have hZ : (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F) = (↑v : _) := by
      rw [hZero v]
    have hOrb : ∀ t, (↑(φ t v) : TangentBundle 𝓘(ℝ, F) F).proj =
        (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).proj + t •
          NormedSpace.fromTangentSpace
            (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).proj
            (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).snd ∧
        NormedSpace.fromTangentSpace
          (↑(φ t v) : TangentBundle 𝓘(ℝ, F) F).proj
          (↑(φ t v) : TangentBundle 𝓘(ℝ, F) F).snd =
        NormedSpace.fromTangentSpace
          (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).proj
          (↑(φ 0 v) : TangentBundle 𝓘(ℝ, F) F).snd :=
      fun t => by rw [hZ]; exact hAff t v
    exact (isGeodesicVelocityCurve_vectorSpace_iff _).mpr hOrb

end Manifold
