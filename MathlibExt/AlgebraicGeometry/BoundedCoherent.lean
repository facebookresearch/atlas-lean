/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherent module sheaves and bounded coherent derived objects

A module sheaf on a scheme is coherent (Stacks, Tag 01BV) when it is
quasi-coherent and its sections on every affine open form a coherent module:
finitely generated, with every finitely generated submodule finitely presented
(Stacks, Tag 05CU). On a locally noetherian scheme this is quasi-coherence with
finitely generated sections (Stacks, Tag 01XZ); in general finite generation
alone is weaker. An object of the derived category of module sheaves is bounded
coherent when its cohomology sheaves are coherent and finitely many are nonzero.
The derived category is `HasDerivedCategory.standard`, as in the Fourier--Mukai
and spherical-twist modules.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedCoherent

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

/-- A coherent module sheaf: quasi-coherent, with coherent sections on every affine open. -/
def coherentModule {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F ∧
    ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U) ∧
      ∀ N : Submodule Γ(X, U) Γ(F, U), N.FG → Module.FinitePresentation Γ(X, U) N

/-- The bounded coherent objects of the derived category of module sheaves: every
cohomology sheaf is coherent and only finitely many are nonzero. -/
def boundedCoherent (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) := fun M ↦
  (∀ n : ℤ, coherentModule ((DerivedCategory.homologyFunctor X.Modules n).obj M)) ∧
    {n : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj M)}.Finite

end MathlibExt.AlgebraicGeometry.BoundedCoherent
