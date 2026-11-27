/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.LeviCivita
import MathlibExt.Geometry.Manifold.Riemannian.LeviCivitaVectorSpace

/-!
# Tests for the fundamental theorem of Riemannian geometry

The theorem makes any two smooth torsion-free metric-compatible connections agree on smooth
vector fields, and Mathlib's Levi-Civita connection is one of them. On the Euclidean plane, the
connection it provides acts on smooth vector fields as the Fréchet derivative.
-/

open Bundle MathlibExt.Geometry.MetricCompatibilityShared
open CovariantDerivative (ContMDiffCovariantDerivative leviCivitaConnection)
open MathlibExt.Geometry.LeviCivitaWanted.Geometry.LeviCivita
open scoped Manifold ContDiff

namespace LeviCivitaFundamentalTheoremTests

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- Mathlib's Levi-Civita connection is smooth, torsion-free and compatible with the metric. -/
private theorem leviCivitaConnection_spec :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) ∞ ∧
      (leviCivitaConnection I M).torsion = 0 ∧
      IsMetricCompatible (leviCivitaConnection I M) :=
  ⟨contMDiffCovariantDerivative_leviCivitaConnection,
    CovariantDerivative.torsion_leviCivitaConnection_eq_zero I,
    .of_isMetricCompatible (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)⟩

variable [T2Space M]

/-- Uniqueness: two smooth torsion-free metric-compatible connections agree on smooth vector
fields. -/
example (cov₁ cov₂ : CovariantDerivative I E (TangentSpace I (M := M)))
    (h₁ : ContMDiffCovariantDerivative cov₁ ∞ ∧ cov₁.torsion = 0 ∧
      IsMetricCompatible cov₁)
    (h₂ : ContMDiffCovariantDerivative cov₂ ∞ ∧ cov₂.torsion = 0 ∧
      IsMetricCompatible cov₂) :
    SameOnSmooth cov₁ cov₂ := by
  obtain ⟨cov, -, huniq⟩ := levi_civita_exists_unique (I := I) (M := M)
  intro Y hY x v
  rw [← huniq cov₁ h₁ Y hY x v, huniq cov₂ h₂ Y hY x v]

/-- Any smooth torsion-free metric-compatible connection agrees with Mathlib's Levi-Civita
connection on smooth vector fields. -/
example (cov' : CovariantDerivative I E (TangentSpace I (M := M)))
    (h : ContMDiffCovariantDerivative cov' ∞ ∧ cov'.torsion = 0 ∧
      IsMetricCompatible cov')
    (Y : Π x : M, TangentSpace I x) (hY : CMDiff ∞ (T% Y)) (x : M) (v : TangentSpace I x) :
    cov' Y x v = leviCivitaConnection I M Y x v := by
  obtain ⟨cov, -, huniq⟩ := levi_civita_exists_unique (I := I) (M := M)
  rw [← huniq cov' h Y hY x v, huniq _ leviCivitaConnection_spec Y hY x v]

end General

section Plane

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Mathlib's Levi-Civita connection of the Euclidean plane is smooth. -/
example : ContMDiffCovariantDerivative (leviCivitaConnection 𝓘(ℝ, ℝ²) ℝ²) ∞ :=
  contMDiffCovariantDerivative_leviCivitaConnection

/-- On the Euclidean plane, the connection given by the theorem differentiates smooth vector
fields as the Fréchet derivative does. -/
example : ∃ cov : CovariantDerivative 𝓘(ℝ, ℝ²) ℝ² (TangentSpace 𝓘(ℝ, ℝ²) (M := ℝ²)),
    cov.torsion = 0 ∧ IsMetricCompatible cov ∧
      ∀ (Y : Π x : ℝ², TangentSpace 𝓘(ℝ, ℝ²) x), CMDiff ∞ (T% Y) →
        ∀ (x : ℝ²) (v : TangentSpace 𝓘(ℝ, ℝ²) x), cov Y x v = fderiv ℝ Y x v := by
  obtain ⟨cov, ⟨-, htor, hmet⟩, huniq⟩ :=
    levi_civita_exists_unique (I := 𝓘(ℝ, ℝ²)) (M := ℝ²)
  refine ⟨cov, htor, hmet, fun Y hY x v ↦ ?_⟩
  rw [huniq _ leviCivitaConnection_spec Y hY x v,
    CovariantDerivative.leviCivitaConnection_vectorSpace_apply
      ((hY x).mdifferentiableAt (by simp))]

end Plane

end LeviCivitaFundamentalTheoremTests
