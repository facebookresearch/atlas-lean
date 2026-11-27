/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

universe u

variable {k : Type u} [Field k]

-- The deprecated `IsProjectiveVariety` is the projectivity predicate of `ProjectiveSpace`, not a
-- parallel definition, so existing statements keep elaborating while they migrate.
set_option linter.deprecated false in
example (X : Over (Spec (.of k))) : IsProjectiveVariety X ↔ ProjectiveSpace.IsProjective X :=
  Iff.rfl

-- Projective space is projective.
example (n : ℕ) : ProjectiveSpace.IsProjective (ProjectiveSpace.projectiveSpace k n) :=
  ⟨n + 1, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance, (Category.id_comp _).symm⟩

-- On a Noetherian scheme, ampleness is Serre's criterion over Mathlib's finitely presented
-- sheaves of modules.
example {X : Scheme.{u}} [IsNoetherian X] (L : LineBundle X) :
    IsAmpleLine L ↔ ∀ F : X.Modules, SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F →
      ∃ N : ℕ, ∀ m ≥ N, GloballyGenerated (moduleTensor X F (power L.val m)) :=
  Iff.rfl

-- The structure sheaf is a line bundle.
noncomputable example (X : Scheme.{u}) : LineBundle X :=
  ⟨structureModule X, isLineBundle_structureModule X⟩
