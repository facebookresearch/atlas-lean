/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.Killing.Basic
public import MathlibExt.Geometry.Manifold.Riemannian.LeviCivitaVectorSpace

/-!
# Killing vector fields on Euclidean space

Let `F` be a finite-dimensional real inner product space with its standard metric.
This file characterizes Killing fields by a skew-adjoint derivative condition, and
shows translations and skew-adjoint linear fields are Killing. The Euclidean
connection formula comes from `LeviCivitaVectorSpace`.

## Main results

* `Manifold.isKillingVectorField_vectorSpace_iff`: Killing iff smooth with
  skew-adjoint derivative everywhere.
* `Manifold.isKillingVectorField_const`: constant fields are Killing.
* `Manifold.isKillingVectorField_continuousLinearMap_iff`: linear fields are Killing
  iff the map is skew-adjoint.
-/

@[expose] public section

open Bundle CovariantDerivative FiberBundle VectorField
open scoped Manifold ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Killing fields on Euclidean space.** Let $F$ be a finite-dimensional real inner product
space, viewed as a Riemannian manifold with the metric given by its inner product. A vector field
$V$ on $F$ is Killing if and only if $V$ is $C^\infty$ and its derivative is skew-adjoint at every
point: for all $x, u, w \in F$, $\langle DV(x)\,u, w \rangle + \langle u, DV(x)\,w \rangle = 0$. -/
theorem Manifold.isKillingVectorField_vectorSpace_iff
    {V : Π y : F, TangentSpace 𝓘(ℝ, F) y} :
    Manifold.IsKillingVectorField 𝓘(ℝ, F) V ↔ ContDiff ℝ ∞ V ∧
      ∀ (x : F) (u w : TangentSpace 𝓘(ℝ, F) x),
        inner ℝ (fderiv ℝ V x u) w + inner ℝ u (fderiv ℝ V x w) = 0 := by
  constructor
  · intro hK
    obtain ⟨hSmooth, hKill⟩ := hK
    have hCont : ContDiff ℝ ∞ V :=
      contMDiff_vectorSpace_iff_contDiff.mp hSmooth
    refine ⟨hCont, fun x u w => ?_⟩
    have hX : MDiffAt (T% V) x := hSmooth.mdifferentiableAt (by simp)
    have eU : leviCivitaConnection 𝓘(ℝ, F) F V x u = fderiv ℝ V x u :=
      CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX u
    have eW : leviCivitaConnection 𝓘(ℝ, F) F V x w = fderiv ℝ V x w :=
      CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX w
    have hEq := hKill x u w
    rw [eU, eW] at hEq
    exact hEq
  · intro h
    obtain ⟨hCont, hSkew⟩ := h
    have hSmooth : CMDiff ∞ (T% V) :=
      contMDiff_vectorSpace_iff_contDiff.mpr hCont
    refine ⟨hSmooth, fun x u v => ?_⟩
    have hX : MDiffAt (T% V) x := hSmooth.mdifferentiableAt (by simp)
    have eU : leviCivitaConnection 𝓘(ℝ, F) F V x u = fderiv ℝ V x u :=
      CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX u
    have eV : leviCivitaConnection 𝓘(ℝ, F) F V x v = fderiv ℝ V x v :=
      CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX v
    rw [eU, eV]
    exact hSkew x u v

/-- **Translations are Killing.** Let $F$ be a finite-dimensional real inner product space,
viewed as a Riemannian manifold with the metric given by its inner product. For every $c \in F$,
the constant vector field $y \mapsto c$ on $F$ is Killing. -/
theorem Manifold.isKillingVectorField_const (c : F) :
    Manifold.IsKillingVectorField 𝓘(ℝ, F)
      (fun y : F => show TangentSpace 𝓘(ℝ, F) y from c) := by
  rw [Manifold.isKillingVectorField_vectorSpace_iff]
  refine ⟨?_, fun x u w => ?_⟩
  · exact contDiff_const
  · have hDer : ∀ y : F,
        fderiv ℝ (fun y : F => show TangentSpace 𝓘(ℝ, F) y from c) y = 0 :=
      fun y => fderiv_const_apply c
    have hPlain : ∀ a b : F, inner ℝ ((0 : F →L[ℝ] F) a) b +
        inner ℝ a ((0 : F →L[ℝ] F) b) = 0 := by simp
    rw [hDer x]
    exact hPlain u w

/-- **Linear Killing fields on Euclidean space.** Let $F$ be a finite-dimensional real inner
product space, viewed as a Riemannian manifold with the metric given by its inner product, and let
$A \colon F \to F$ be a continuous linear map. The linear vector field $y \mapsto A y$ is Killing
if and only if $A$ is skew-adjoint: $\langle A u, w \rangle + \langle u, A w \rangle = 0$ for all
$u, w \in F$. -/
theorem Manifold.isKillingVectorField_continuousLinearMap_iff (A : F →L[ℝ] F) :
    Manifold.IsKillingVectorField 𝓘(ℝ, F)
      (fun y : F => show TangentSpace 𝓘(ℝ, F) y from A y) ↔
      ∀ u w : F, inner ℝ (A u) w + inner ℝ u (A w) = 0 := by
  have hDer : ∀ x : F,
      fderiv ℝ (fun y : F => show TangentSpace 𝓘(ℝ, F) y from A y) x = A :=
    fun x => ContinuousLinearMap.fderiv A
  have hCont : ContDiff ℝ ∞
      (fun y : F => show TangentSpace 𝓘(ℝ, F) y from A y) := by
    exact A.contDiff
  rw [Manifold.isKillingVectorField_vectorSpace_iff]
  constructor
  · intro h u w
    obtain ⟨-, hSkew⟩ := h
    have hEq := hSkew w u w
    rw [hDer w] at hEq
    exact hEq
  · intro h
    refine ⟨hCont, fun x u w => ?_⟩
    rw [hDer x]
    exact h u w
