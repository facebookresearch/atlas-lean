/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.DGQuasiFunctorModels

/-!
# Tests for cofibrant right DG modules

Representable right DG modules are cofibrant, so they are objects of the DG category of cofibrant
modules, and the identity of a representable module is a cofibrant replacement of it. Degree-zero
cocycles lift along maps of cochain complexes of modules that are quasi-isomorphisms in degree zero
and surjective in degree `-1`.
-/

noncomputable section

namespace MathlibExtTest.DGQuasiFunctorModels

open CategoryTheory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts MathlibExt.CategoryTheory.DGQuasiFunctorModels

universe u

variable {k : Type u} [CommRing k] {C : Type u} [DGCategory k C]

/-- A representable module is an object of the DG category of cofibrant modules. -/
example (X : C) : DGDerivedModules k C :=
  ⟨⟨dgRepresentable k X⟩, isCofibrantModule_dgRepresentable X⟩

/-- The identity is a trivial fibration: its components are identities. -/
theorem isModuleTrivialFibration_id (M : RightModule k C) :
    IsModuleTrivialFibration (𝟙 M) := fun x ↦ by
  have h : moduleComponent (𝟙 M) x = 𝟙 _ := (moduleEvaluationFunctor x).map_id M
  rw [h]
  exact ⟨inferInstance, fun _ ↦ Function.surjective_id⟩

/-- So a representable module is its own cofibrant replacement. -/
example (X : C) : ModuleReplacement (⟨dgRepresentable k X⟩ : RightModule k C) :=
  ⟨_, 𝟙 _, isCofibrantModule_dgRepresentable X, isModuleTrivialFibration_id _⟩

/-- A cocycle of degree zero lifts along a map that is a quasi-isomorphism in degree zero and
surjective in degree `-1`; no other degree is involved. -/
example {N P : Cochains k} (φ : N ⟶ P) [QuasiIsoAt φ 0] (hφ : Function.Surjective (φ.f (-1)))
    (c : P.X 0) (hc : P.d 0 1 c = 0) : ∃ c' : N.X 0, N.d 0 1 c' = 0 ∧ φ.f 0 c' = c :=
  exists_cocycle_lift_of_quasiIsoAt_zero φ hφ c hc

end MathlibExtTest.DGQuasiFunctorModels

end
