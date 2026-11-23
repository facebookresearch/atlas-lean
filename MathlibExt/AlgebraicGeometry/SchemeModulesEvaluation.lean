/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global sections of sheaves of modules on a scheme are additive and left exact

On a scheme `X`, evaluation of sheaves of modules at `⊤` followed by restriction
of scalars along a ring homomorphism `S →+* Γ(X, ⊤)` is an additive, left exact
functor `X.Modules ⥤ ModuleCat S`. Additivity is needed to take right-derived
functors of global sections, for instance with scalars restricted along the
structure morphism `X ⟶ Spec k`; left exactness identifies the zeroth derived
functor with global sections.

Lean does not find the additivity instance through the instance for composites:
the codomain of evaluation is `ModuleCat` of the ring of sections of
`X.ringCatSheaf` over `⊤`, which is not reducibly the ring `Γ(X, ⊤)` on which
restriction of scalars acts. The instances are stated on `X.Modules`, whose
`Preadditive` instance is not reducibly that of `SheafOfModules X.ringCatSheaf`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections of sheaves of modules on a scheme, followed by restriction of
scalars along `φ : S →+* Γ(X, ⊤)`, form an additive functor. -/
instance evaluation_top_comp_restrictScalars_additive (X : Scheme.{u}) {S : Type*} [Ring S]
    (φ : S →+* Γ(X, ⊤)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars φ :
      X.Modules ⥤ ModuleCat S).Additive :=
  ⟨rfl⟩

/-- Global sections of sheaves of modules on a scheme, followed by restriction of
scalars along `φ : S →+* Γ(X, ⊤)`, form a left exact functor. -/
instance evaluation_top_comp_restrictScalars_preservesFiniteLimits (X : Scheme.{u})
    {S : Type*} [Ring S] (φ : S →+* Γ(X, ⊤)) :
    PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars φ : X.Modules ⥤ ModuleCat S) := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let E : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} S := ModuleCat.restrictScalars φ
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := X.ringCatSheaf) (op ⊤)
  exact comp_preservesFiniteLimits F E

end AlgebraicGeometry.Scheme.Modules
