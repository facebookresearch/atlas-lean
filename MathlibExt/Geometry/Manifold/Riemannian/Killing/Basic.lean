/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Killing vector fields on a Riemannian manifold

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric, given by `IsManifold`,
`RiemannianBundle` and `IsContMDiffRiemannianBundle` instances, and let `∇` be its
Levi-Civita connection. This file defines Killing fields via Killing's equation.

## Main definitions

* `Manifold.IsKillingVectorField I X`: `C^∞` plus `⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫ = 0`.
* `Manifold.killingVectorFields I M`: the submodule of Killing fields.

## Main results

* `inner_leviCivitaConnection_self` and the polarization iff.
* `mvfderiv_inner_sub_inner_mlieBracket`: the `(L_X g)(Y, Z)` identity.
* `isKillingVectorField_iff_mvfderiv_inner`: Killing iff `L_X g = 0`.
* Zero, addition, scaling, membership and extensionality for Killing fields.

## Implementation notes

Killing's equation is the definition because Mathlib has the Levi-Civita connection
but no Lie derivative of tensors; `isKillingVectorField_iff_mvfderiv_inner` identifies
it with `L_X g = 0`. Smoothness is required (the textbook hypothesis); it excludes
fields where the connection takes its junk value `0`.

## References

* B. O'Neill, Semi-Riemannian Geometry with Applications to Relativity (1983).
* P. Petersen, Riemannian Geometry (3rd ed., GTM 171, Springer, 2016).
* Burns and Matveev, Open problems and questions about geodesics, Ergodic Theory
  Dynam. Systems 41 (2021), §10.2.
-/

@[expose] public section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A field `X` is Killing when it is `C^∞` and satisfies Killing's equation
`∇_i X_j + ∇_j X_i = 0` for the Levi-Civita connection of the metric itself, i.e.
`⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫ = 0`. This is `L_X g = 0`
(see `isKillingVectorField_iff_mvfderiv_inner`). Smoothness is part of the definition
(the textbook definition, excluding junk-value fields). The flow-by-isometries fact is
NOT proved here. Motivation: Killing `V` gives the linear first integral `ξ ↦ g(V, ξ)`
of geodesic flow (Burns and Matveev (2021), §10.2), not formalized here. -/
structure IsKillingVectorField (X : (x : M) → TangentSpace I x) : Prop where
  contMDiff : CMDiff ∞ (T% X)
  inner_leviCivitaConnection_add : ∀ (x : M) (u v : TangentSpace I x),
    inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0

/-- A Killing field preserves lengths infinitesimally: `⟪∇_u X, u⟫ = 0`. -/
theorem IsKillingVectorField.inner_leviCivitaConnection_self
    {X : (x : M) → TangentSpace I x} (hX : IsKillingVectorField I X)
    (x : M) (u : TangentSpace I x) :
    inner ℝ (leviCivitaConnection I M X x u) u = 0 := by
  have hAdd : inner ℝ (leviCivitaConnection I M X x u) u +
      inner ℝ u (leviCivitaConnection I M X x u) = 0 :=
    hX.inner_leviCivitaConnection_add x u u
  have hSym : inner ℝ u (leviCivitaConnection I M X x u) =
      inner ℝ (leviCivitaConnection I M X x u) u := real_inner_comm _ _
  rw [hSym] at hAdd
  linarith

/-- Polarization: Killing is `C^∞` plus vanishing of `⟪∇_u X, u⟫` for all `u`. -/
theorem isKillingVectorField_iff_inner_leviCivitaConnection_self
    {X : (x : M) → TangentSpace I x} :
    IsKillingVectorField I X ↔ CMDiff ∞ (T% X) ∧
      ∀ (x : M) (u : TangentSpace I x),
        inner ℝ (leviCivitaConnection I M X x u) u = 0 := by
  constructor
  · intro hX
    exact ⟨hX.contMDiff,
      fun x u ↦ IsKillingVectorField.inner_leviCivitaConnection_self I hX x u⟩
  · intro h
    obtain ⟨hSmooth, hSelf⟩ := h
    refine ⟨hSmooth, fun x u v ↦ ?_⟩
    have hUV : inner ℝ (leviCivitaConnection I M X x (u + v)) (u + v) = 0 :=
      hSelf x (u + v)
    have hU : inner ℝ (leviCivitaConnection I M X x u) u = 0 := hSelf x u
    have hV : inner ℝ (leviCivitaConnection I M X x v) v = 0 := hSelf x v
    have hAdd : leviCivitaConnection I M X x (u + v) =
        (leviCivitaConnection I M X x u) + (leviCivitaConnection I M X x v) :=
      map_add _ _ _
    simp only [hAdd, inner_add_left, inner_add_right] at hUV
    have hSym : inner ℝ (leviCivitaConnection I M X x v) u =
        inner ℝ u (leviCivitaConnection I M X x v) := real_inner_comm _ _
    rw [hU, hV, hSym] at hUV
    linear_combination hUV

/-- `(L_X g)(Y, Z)` at `x` equals `⟪∇_{Y x} X, Z x⟫ + ⟪Y x, ∇_{Z x} X⟫`. -/
theorem mvfderiv_inner_sub_inner_mlieBracket
    {X Y Z : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) -
        inner ℝ (VectorField.mlieBracket I X Y x) (Z x) -
        inner ℝ (Y x) (VectorField.mlieBracket I X Z x) =
      inner ℝ (leviCivitaConnection I M X x (Y x)) (Z x) +
        inner ℝ (Y x) (leviCivitaConnection I M X x (Z x)) := by
  have hcov := isMetricCompatible_leviCivitaConnection I (M := M)
  have hMetric : ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) =
      inner ℝ (leviCivitaConnection I M Y x (X x)) (Z x) +
        inner ℝ (Y x) (leviCivitaConnection I M Z x (X x)) :=
    hcov.mvfderiv_inner_eq X hY hZ
  have hTXY : (leviCivitaConnection I M Y x (X x)) -
      (leviCivitaConnection I M X x (Y x)) = VectorField.mlieBracket I X Y x :=
    (torsion_eq_zero_iff (leviCivitaConnection I M)).mp
      (torsion_leviCivitaConnection_eq_zero I (M := M)) hX hY
  have hTXZ : (leviCivitaConnection I M Z x (X x)) -
      (leviCivitaConnection I M X x (Z x)) = VectorField.mlieBracket I X Z x :=
    (torsion_eq_zero_iff (leviCivitaConnection I M)).mp
      (torsion_leviCivitaConnection_eq_zero I (M := M)) hX hZ
  rw [hMetric, ← hTXY, ← hTXZ, inner_sub_left, inner_sub_right]
  ring

/-- Killing is `C^∞` plus vanishing of `(L_X g)(Y, Z)` for all differentiable `Y Z`. -/
theorem isKillingVectorField_iff_mvfderiv_inner
    {X : (x : M) → TangentSpace I x} :
    IsKillingVectorField I X ↔ CMDiff ∞ (T% X) ∧
      ∀ (x : M) (Y Z : (x : M) → TangentSpace I x), MDiffAt (T% Y) x →
        MDiffAt (T% Z) x → ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) -
          inner ℝ (VectorField.mlieBracket I X Y x) (Z x) -
          inner ℝ (Y x) (VectorField.mlieBracket I X Z x) = 0 := by
  constructor
  · intro hX
    refine ⟨hX.contMDiff, fun x Y Z hY hZ ↦ ?_⟩
    have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
    have hC1 := mvfderiv_inner_sub_inner_mlieBracket I hXx hY hZ
    have hKill := hX.inner_leviCivitaConnection_add x (Y x) (Z x)
    rw [hC1]
    exact hKill
  · intro h
    obtain ⟨hSmooth, hVanish⟩ := h
    refine ⟨hSmooth, fun x u v ↦ ?_⟩
    have hXx : MDiffAt (T% X) x := hSmooth.mdifferentiableAt (by simp)
    have hY : MDiffAt (T% (FiberBundle.extend E u)) x :=
      FiberBundle.mdifferentiableAt_extend I E u
    have hZ : MDiffAt (T% (FiberBundle.extend E v)) x :=
      FiberBundle.mdifferentiableAt_extend I E v
    have hV := hVanish x (FiberBundle.extend E u) (FiberBundle.extend E v) hY hZ
    have hC1 := mvfderiv_inner_sub_inner_mlieBracket I hXx hY hZ
    have hYu : FiberBundle.extend E u x = u := FiberBundle.extend_apply_self E u
    have hZv : FiberBundle.extend E v x = v := FiberBundle.extend_apply_self E v
    rw [hC1] at hV
    rw [hYu, hZv] at hV
    exact hV

/-- The zero vector field is Killing. -/
theorem isKillingVectorField_zero :
    IsKillingVectorField I (0 : (x : M) → TangentSpace I x) := by
  have hSmooth : CMDiff ∞ (T% (0 : (x : M) → TangentSpace I x)) :=
    contMDiff_zeroSection ℝ _
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hCov0 : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) = 0 :=
    CovariantDerivative.zero (leviCivitaConnection I M)
  have hU : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) x u = 0 := by
    simp [hCov0]
  have hV : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) x v = 0 := by
    simp [hCov0]
  rw [hU, hV]
  simp

/-- The sum of two Killing fields is Killing. -/
theorem IsKillingVectorField.add {X Y : (x : M) → TangentSpace I x}
    (hX : IsKillingVectorField I X) (hY : IsKillingVectorField I Y) :
    IsKillingVectorField I (X + Y) := by
  have hSmooth : CMDiff ∞ (T% (X + Y)) := hX.contMDiff.add_section hY.contMDiff
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := hY.contMDiff.mdifferentiableAt (by simp)
  have hAddCov : leviCivitaConnection I M (X + Y) x =
      (leviCivitaConnection I M X x) + (leviCivitaConnection I M Y x) :=
    (isCovariantDerivativeOn (leviCivitaConnection I M)).add hXx hYx
  have hU : leviCivitaConnection I M (X + Y) x u =
      (leviCivitaConnection I M X x u) + (leviCivitaConnection I M Y x u) := by
    simp [hAddCov]
  have hV : leviCivitaConnection I M (X + Y) x v =
      (leviCivitaConnection I M X x v) + (leviCivitaConnection I M Y x v) := by
    simp [hAddCov]
  have hXeq : inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0 :=
    hX.inner_leviCivitaConnection_add x u v
  have hYeq : inner ℝ (leviCivitaConnection I M Y x u) v +
      inner ℝ u (leviCivitaConnection I M Y x v) = 0 :=
    hY.inner_leviCivitaConnection_add x u v
  rw [hU, hV, inner_add_left, inner_add_right]
  linarith

/-- A constant real multiple of a Killing field is Killing. -/
theorem IsKillingVectorField.const_smul {X : (x : M) → TangentSpace I x}
    (hX : IsKillingVectorField I X) (c : ℝ) : IsKillingVectorField I (c • X) := by
  have hSmooth : CMDiff ∞ (T% (c • X)) := hX.contMDiff.const_smul_section
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
  have hSmulCov : leviCivitaConnection I M (c • X) x =
      c • (leviCivitaConnection I M X x) :=
    (isCovariantDerivativeOn (leviCivitaConnection I M)).smul_const c hXx
  have hU : leviCivitaConnection I M (c • X) x u =
      c • (leviCivitaConnection I M X x u) := by simp [hSmulCov]
  have hV : leviCivitaConnection I M (c • X) x v =
      c • (leviCivitaConnection I M X x v) := by simp [hSmulCov]
  have hXeq : inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0 :=
    hX.inner_leviCivitaConnection_add x u v
  rw [hU, hV, inner_smul_left, inner_smul_right]
  simp
  linear_combination c * hXeq

variable (M)

/-- The submodule of Killing vector fields on `M`. -/
def killingVectorFields : Submodule ℝ (Π x : M, TangentSpace I x) where
  carrier := {X | IsKillingVectorField I X}
  zero_mem' := isKillingVectorField_zero I
  add_mem' := fun hX hY ↦ IsKillingVectorField.add I hX hY
  smul_mem' := fun c _X hX ↦ IsKillingVectorField.const_smul I hX c

/-- Membership in `killingVectorFields` is being Killing. -/
@[simp]
theorem mem_killingVectorFields {X : (x : M) → TangentSpace I x} :
    X ∈ killingVectorFields I M ↔ IsKillingVectorField I X :=
  Iff.rfl

/-- Two Killing fields agreeing at every point are equal. -/
@[ext]
theorem killingVectorFields.ext {a b : killingVectorFields I M}
    (h : ∀ x : M, (a : Π x : M, TangentSpace I x) x = (b : Π x : M, TangentSpace I x) x) :
    a = b := by
  apply Subtype.ext
  funext x
  exact h x

end Manifold
