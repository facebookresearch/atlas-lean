/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Actual finite points and their determinant norm lines

A finite point is the actual scheme morphism `Spec E -> X` over `K`.
A closed finite point additionally has its literal closed immersion;
the field is therefore the residue field of that point, up to the native
field isomorphism. A closed-image record fixes the factorization of an
arbitrary finite-extension point through that same closed point.

The fibre is the native global-section module of the actual line pullback.
Its norm line is `Hom_K(det_K E, det_K V)`, using the actual exterior
annihilator determinant modules. An `E`-frame gives its ordered determinant
generator. Every vector contributes the determinant field norm of its
actual frame coordinate. Nothing supplies an unrelated height function.

Source: Yuan--Zhang, arXiv:2105.13587v9, Section 5.3.1 (printed p152):
the vector height is the norm-line class divided by the actual residue
degree. Exterior determinant primitives are reused from the quoted
Apache-2.0 Axiom source through ProjectiveDeterminantModules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FinitePointNormLines

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open GenericSectionMaps ProjectiveDeterminantModules

variable {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]

/-- The actual finite field-point scheme over the original scalar base. -/
def fieldPoint : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E)))

abbrev ExtensionPoint (X : Over (Spec (.of K))) := fieldPoint (K := K) (E := E) ⟶ X

/-- The geometric point is an actual closed immersion from its finite residue field. -/
structure ClosedPoint (X : Over (Spec (.of K))) where
  [finiteDegree : FiniteDimensional K E]
  map : ExtensionPoint (K := K) (E := E) X
  [closed : IsClosedImmersion map.left]

attribute [instance] ClosedPoint.closed

/-- An extension-field presentation factors through the same genuine closed point. -/
structure ClosedImage {X : Over (Spec (.of K))} (x : ExtensionPoint (K := K) (E := E) X) where
  residue : Type
  [field : Field residue]
  [algebra : Algebra K residue]
  [finite : FiniteDimensional K residue]
  point : ClosedPoint (K := K) (E := residue) X
  embedding : residue →ₐ[K] E
  factorization : Spec.map (CommRingCat.ofHom embedding.toRingHom) ≫ point.map.left = x.left

attribute [instance] ClosedImage.field ClosedImage.algebra ClosedImage.finite

/-- The native section module of this exact finite-point line pullback. -/
def pointFibre {X : Over (Spec (.of K))} (L : X.left.Modules)
    (x : ExtensionPoint (K := K) (E := E) X) : ModuleCat E :=
  (sections (Over.mk (𝟙 (Spec (.of E))))).obj ((Scheme.Modules.pullback x.left).obj L)

variable (V : ModuleCat E)

local instance restrictedModule : Module K V :=
  inferInstanceAs (Module K ((ModuleCat.restrictScalars (algebraMap K E)).obj V))

local instance restrictedTower : IsScalarTower K E V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The source frame is the actual rank-one `E`-module equivalence. -/
def frameEquiv (b : Basis Unit E V) : E ≃ₗ[E] V :=
  ((b.repr.trans (Finsupp.linearEquivFunOnFinite E E Unit)).trans
    (LinearEquiv.funUnique Unit E E)).symm

/-- Restriction of scalars retains that same actual frame map. -/
def frameEquivOverBase (b : Basis Unit E V) : E ≃ₗ[K] V :=
  (frameEquiv V b).restrictScalars K

/-- The norm is the actual Hom of the two exterior determinant lines. -/
def normModule : ModuleCat K :=
  ModuleCat.of K (determinantModule K E →ₗ[K] determinantModule K V)

/-- The actual algebraic norm line sheaf over the field point. -/
def normLine : (Spec (.of K)).Modules :=
  (tilde.functor (.of K)).obj (normModule (K := K) V)

/-- The determinant generator is computed from the original `E` frame. -/
def normFrame (b : Basis Unit E V) : normModule (K := K) V :=
  (determinantEquiv (frameEquivOverBase (K := K) V b)).toLinearMap

/-- A fibre vector contributes its actual field norm, not a selected real number. -/
def normElement (b : Basis Unit E V) (v : V) : normModule (K := K) V :=
  Algebra.norm K (b.repr v ()) • normFrame (K := K) V b

omit [FiniteDimensional K E] in
@[simp] theorem normElement_frame (b : Basis Unit E V) :
    normElement (K := K) V b (b ()) = normFrame (K := K) V b := by
  simp [normElement]

@[simp] theorem normElement_zero (b : Basis Unit E V) : normElement (K := K) V b 0 = 0 := by
  simp [normElement]

omit [FiniteDimensional K E] in
/-- Scalar change is the native determinant field norm on this same line. -/
theorem normElement_smul (b : Basis Unit E V) (a : E) (v : V) :
    normElement (K := K) V b (a • v) =
      Algebra.norm K a • normElement (K := K) V b v := by
  simp [normElement, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]

end MathlibExt.AlgebraicGeometry.FinitePointNormLines
