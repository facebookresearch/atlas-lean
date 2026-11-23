/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow.FirstIntegral
import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow.VectorSpace
import MathlibExt.Geometry.Manifold.Riemannian.Killing.VectorSpace

/-!
# First integrals on the flat plane

Checks for `Manifold.IsFirstIntegralOfGeodesics` on
`EuclideanSpace ℝ (Fin 2)`: energy, the linear integral of a
constant Killing field, cubic integrals with value pins, a proved
non-example, periodicity and nonvanishing of the constant field,
and the general orbit and constant cases.

T1 is the degree-2 near-miss every metric has; T3 is the cubic
witness of degree 3 for the Burns-Matveev conjecture's hypothesis,
which is itself neither stated nor proved here.
-/

open Bundle

open scoped Manifold

noncomputable section

namespace GeodesicFirstIntegralTests

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- First basis vector. -/
def e0 : Plane := EuclideanSpace.single 0 1

/-- Second basis vector. -/
def e1 : Plane := EuclideanSpace.single 1 1

/-- Tangent vector with base `x` and velocity `v`. -/
def mkTangent (x v : Plane) : TangentBundle 𝓘(ℝ, Plane) Plane := ⟨x, v⟩

/-- Velocity read in the model space. -/
def vel (p : TangentBundle 𝓘(ℝ, Plane) Plane) : Plane :=
  NormedSpace.fromTangentSpace p.proj p.snd

/-- First coordinate of the velocity. -/
def xi0 (p : TangentBundle 𝓘(ℝ, Plane) Plane) : ℝ := (vel p).ofLp 0

/-- Second coordinate of the velocity. -/
def xi1 (p : TangentBundle 𝓘(ℝ, Plane) Plane) : ℝ := (vel p).ofLp 1

/-- Energy: squared norm of the velocity. -/
def energy (p : TangentBundle 𝓘(ℝ, Plane) Plane) : ℝ :=
  inner ℝ (vel p) (vel p)

/-- Linear function pairing `e0` with the velocity. -/
def lin (p : TangentBundle 𝓘(ℝ, Plane) Plane) : ℝ := inner ℝ e0 (vel p)

/-- First coordinate of the base point. -/
def base0 (p : TangentBundle 𝓘(ℝ, Plane) Plane) : ℝ := p.proj.ofLp 0

/-- Straight line with velocity `e0`. -/
def uLine : ℝ → TangentBundle 𝓘(ℝ, Plane) Plane :=
  fun t => mkTangent (t • e0) e0

/-- Constant field with value `e0`. -/
def X0 : Π y : Plane, TangentSpace 𝓘(ℝ, Plane) y :=
  fun y => show TangentSpace 𝓘(ℝ, Plane) y from e0

/-- A vector has integer coordinates. -/
def IntCoord (k : Plane) : Prop := ∀ i, ∃ n : ℤ, k.ofLp i = (n : ℝ)

/-- Check that the model unfolds to the plane model. -/
theorem plane_model : 𝓘(ℝ, Plane) = 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) := rfl

/-- T1: energy is a first integral; the degree-2 near-miss every metric has. -/
theorem energy_first_integral :
    Manifold.IsFirstIntegralOfGeodesics 𝓘(ℝ, Plane) energy := by
  intro u hu s t
  have hAff := (Manifold.isGeodesicVelocityCurve_vectorSpace_iff u).mp hu
  have ht : vel (u t) = vel (u 0) := (hAff t).2
  have hs : vel (u s) = vel (u 0) := (hAff s).2
  show inner ℝ (vel (u t)) (vel (u t)) = inner ℝ (vel (u s)) (vel (u s))
  rw [ht, hs]

/-- T2: pairing with the constant Killing field `e0` is a first integral. -/
theorem lin_first_integral :
    Manifold.IsFirstIntegralOfGeodesics 𝓘(ℝ, Plane) lin := by
  intro u hu s t
  have hAff := (Manifold.isGeodesicVelocityCurve_vectorSpace_iff u).mp hu
  have ht : vel (u t) = vel (u 0) := (hAff t).2
  have hs : vel (u s) = vel (u 0) := (hAff s).2
  show inner ℝ e0 (vel (u t)) = inner ℝ e0 (vel (u s))
  rw [ht, hs]

/-- T5a: the constant field with value `e0` is Killing. -/
theorem killing_const_e0 :
    Manifold.IsKillingVectorField 𝓘(ℝ, Plane) X0 :=
  Manifold.isKillingVectorField_const e0

/-- T3a: the cube of the linear integral is a first integral. -/
theorem lin_cube_first_integral :
    Manifold.IsFirstIntegralOfGeodesics 𝓘(ℝ, Plane)
      (fun p => (lin p) ^ 3) :=
  Manifold.IsFirstIntegralOfGeodesics.pow 𝓘(ℝ, Plane) lin_first_integral 3

/-- T3b: the cube of the first velocity coordinate is a first integral. -/
theorem xi_cube_first_integral :
    Manifold.IsFirstIntegralOfGeodesics 𝓘(ℝ, Plane)
      (fun p => (xi0 p) ^ 3) := by
  intro u hu s t
  have hAff := (Manifold.isGeodesicVelocityCurve_vectorSpace_iff u).mp hu
  have ht : vel (u t) = vel (u 0) := (hAff t).2
  have hs : vel (u s) = vel (u 0) := (hAff s).2
  have hV : vel (u t) = vel (u s) := ht.trans hs.symm
  have hE : xi0 (u t) = xi0 (u s) := by
    show (vel (u t)).ofLp 0 = (vel (u s)).ofLp 0
    rw [hV]
  show (xi0 (u t)) ^ 3 = (xi0 (u s)) ^ 3
  rw [hE]

/-- T3 pin: at velocity `e0` the cubic coordinate function is `1`. -/
theorem xi_cube_at_e0 :
    (fun p => (xi0 p) ^ 3) (mkTangent 0 e0) = 1 := by
  have hVel : vel (mkTangent 0 e0) = e0 := rfl
  have hC : e0.ofLp (0 : Fin 2) = 1 :=
    PiLp.single_eq_same (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)
  have hXi : xi0 (mkTangent 0 e0) = 1 := by
    show (vel (mkTangent 0 e0)).ofLp 0 = 1
    rw [hVel, hC]
  show (xi0 (mkTangent 0 e0)) ^ 3 = 1
  rw [hXi]
  norm_num

/-- T3 pin: at velocity `e1` the cubic coordinate function is `0`. -/
theorem xi_cube_at_e1 :
    (fun p => (xi0 p) ^ 3) (mkTangent 0 e1) = 0 := by
  have hVel : vel (mkTangent 0 e1) = e1 := rfl
  have hC : e1.ofLp (0 : Fin 2) = 0 :=
    PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin 2 => ℝ)
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℝ)
  have hXi : xi0 (mkTangent 0 e1) = 0 := by
    show (vel (mkTangent 0 e1)).ofLp 0 = 0
    rw [hVel, hC]
  show (xi0 (mkTangent 0 e1)) ^ 3 = 0
  rw [hXi]
  norm_num

/-- T3 pin: at velocity `e0 + e1` the cubic coordinate function is `1`. -/
theorem xi_cube_at_sum :
    (fun p => (xi0 p) ^ 3) (mkTangent 0 (e0 + e1)) = 1 := by
  have hVel : vel (mkTangent 0 (e0 + e1)) = e0 + e1 := rfl
  have h0 : e0.ofLp (0 : Fin 2) = 1 :=
    PiLp.single_eq_same (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)
  have h1 : e1.ofLp (0 : Fin 2) = 0 :=
    PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin 2 => ℝ)
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℝ)
  have hAdd : (e0 + e1).ofLp (0 : Fin 2) = 1 := by
    have hA : (e0 + e1).ofLp (0 : Fin 2) = e0.ofLp 0 + e1.ofLp 0 :=
      PiLp.add_apply _ e0 e1 0
    rw [hA, h0, h1, add_zero]
  have hXi : xi0 (mkTangent 0 (e0 + e1)) = 1 := by
    show (vel (mkTangent 0 (e0 + e1))).ofLp 0 = 1
    rw [hVel, hAdd]
  show (xi0 (mkTangent 0 (e0 + e1))) ^ 3 = 1
  rw [hXi]
  norm_num

/-- T3 pin: at velocity `2 • e0` the value is `8`, showing cubic scaling. -/
theorem xi_cube_at_smul :
    (fun p => (xi0 p) ^ 3) (mkTangent 0 ((2 : ℝ) • e0)) = 8 := by
  have h0 : e0.ofLp (0 : Fin 2) = 1 :=
    PiLp.single_eq_same (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)
  have hVel : vel (mkTangent 0 ((2 : ℝ) • e0)) = (2 : ℝ) • e0 := rfl
  have hS : ((2 : ℝ) • e0).ofLp (0 : Fin 2) = 2 := by
    have hA : ((2 : ℝ) • e0).ofLp (0 : Fin 2) = (2 : ℝ) • e0.ofLp 0 :=
      PiLp.smul_apply _ (2 : ℝ) e0 0
    rw [hA, h0, smul_eq_mul, mul_one]
  have hXi : xi0 (mkTangent 0 ((2 : ℝ) • e0)) = 2 := by
    show (vel (mkTangent 0 ((2 : ℝ) • e0))).ofLp 0 = 2
    rw [hVel]
    exact hS
  show (xi0 (mkTangent 0 ((2 : ℝ) • e0))) ^ 3 = 8
  rw [hXi]
  norm_num

/-- T4 helper: the line with velocity `e0` is a geodesic velocity curve. -/
theorem uLine_geodesic :
    Manifold.IsGeodesicVelocityCurve 𝓘(ℝ, Plane) uLine := by
  rw [Manifold.isGeodesicVelocityCurve_vectorSpace_iff]
  intro t
  have hVel0 : vel (uLine 0) = e0 := rfl
  have hVelt : vel (uLine t) = e0 := rfl
  have hProj0 : (uLine 0).proj = (0 : ℝ) • e0 := rfl
  have hProjt : (uLine t).proj = t • e0 := rfl
  constructor
  · show (uLine t).proj = (uLine 0).proj + t • vel (uLine 0)
    rw [hProjt, hProj0, hVel0]
    simp
  · show vel (uLine t) = vel (uLine 0)
    rw [hVelt, hVel0]

/-- T4: the base-point coordinate is not a first integral. -/
theorem base_not_first_integral :
    ¬ Manifold.IsFirstIntegralOfGeodesics 𝓘(ℝ, Plane) base0 := by
  intro h
  have hEq := h uLine uLine_geodesic 0 1
  have hProj0 : (uLine 0).proj = (0 : ℝ) • e0 := rfl
  have hProj1 : (uLine 1).proj = (1 : ℝ) • e0 := rfl
  have hC : e0.ofLp (0 : Fin 2) = 1 :=
    PiLp.single_eq_same (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)
  have hS0 : ((0 : ℝ) • e0).ofLp (0 : Fin 2) = 0 := by
    have hA : ((0 : ℝ) • e0).ofLp (0 : Fin 2) = (0 : ℝ) • e0.ofLp 0 :=
      PiLp.smul_apply _ (0 : ℝ) e0 0
    rw [hA, hC, zero_smul]
  have hS1 : ((1 : ℝ) • e0).ofLp (0 : Fin 2) = 1 := by
    have hA : ((1 : ℝ) • e0).ofLp (0 : Fin 2) = (1 : ℝ) • e0.ofLp 0 :=
      PiLp.smul_apply _ (1 : ℝ) e0 0
    rw [hA, hC, one_smul]
  have h0 : base0 (uLine 0) = 0 := by
    show ((uLine 0).proj).ofLp 0 = 0
    rw [hProj0]
    exact hS0
  have h1 : base0 (uLine 1) = 1 := by
    show ((uLine 1).proj).ofLp 0 = 1
    rw [hProj1]
    exact hS1
  rw [h1, h0] at hEq
  exact one_ne_zero hEq

/-- T5b: the constant field is `ℤ²`-periodic as a real statement. -/
theorem killing_periodic (y k : Plane) (_ : IntCoord k) :
    NormedSpace.fromTangentSpace (y + k) (X0 (y + k)) =
      NormedSpace.fromTangentSpace y (X0 y) := by
  rfl

/-- T5c: the constant field is nonzero somewhere. -/
theorem killing_nonzero : ∃ y : Plane, X0 y ≠ 0 := by
  refine ⟨0, ?_⟩
  intro hC
  have hC' : e0 = (0 : Plane) := hC
  have hCoord : e0.ofLp (0 : Fin 2) = 1 :=
    PiLp.single_eq_same (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)
  have hZ : (0 : Plane).ofLp (0 : Fin 2) = 0 := PiLp.zero_apply _ 0
  have hE : e0.ofLp 0 = (0 : Plane).ofLp 0 := by rw [hC']
  rw [hCoord, hZ] at hE
  norm_num at hE

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ G H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 2 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 G (fun x : N ↦ TangentSpace I x)]

/-- T6a: a first integral is constant along orbits of any geodesic flow. -/
theorem general_orbit_const {F : TangentBundle I N → ℝ}
    (hF : Manifold.IsFirstIntegralOfGeodesics I F)
    {φ : ℝ → TangentBundle I N → TangentBundle I N}
    (hφ : Manifold.IsGeodesicFlow I φ) (t : ℝ)
    (v : TangentBundle I N) :
    F (φ t v) = F v :=
  Manifold.IsFirstIntegralOfGeodesics.const_on_flow I hF hφ t v

/-- T6b: on a general manifold, constants are first integrals. -/
theorem general_const_first_integral (c : ℝ) :
    Manifold.IsFirstIntegralOfGeodesics I
      (fun _ : TangentBundle I N ↦ c) :=
  Manifold.IsFirstIntegralOfGeodesics.const I c

end GeodesicFirstIntegralTests
