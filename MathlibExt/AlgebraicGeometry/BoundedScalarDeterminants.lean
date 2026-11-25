/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeterminantZeroUnits
public import MathlibExt.AlgebraicGeometry.BoundedDeterminantTransportModels
public import MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Actual scalar determinant maps for arbitrary bounded perfect complexes

The target presentation is identified with the native cochain scalar
extension in every degree. The module map is the actual adjunction unit
followed by that cochain identification. Even determinant factors use
the source semilinear exterior map; odd factors use the normalized dual
evaluation on those same determinant vectors.

The whole map is computed by ordered semilinear tensor maps. Zero terms
removed by scalar extension use the actual exterior-augmentation units.
The final scalar isomorphism is fixed by its native adjunction-unit
equation, without a freely selected line comparison.

Sources: Knudsen--Mumford, Sections 1--2; Stacks Project, Tags 0FJW/0FJX;
the completed projective scalar determinant source is retained in
ProjectiveDeterminantModules.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open BoundedProjectiveDeterminants ProjectiveDeterminantModules DeterminantZeroUnits
open AffineDerivedCoefficientModules
open scoped TensorProduct

variable {R S : CommRingCat.{0}} (g : R ⟶ S) (C : BoundedProjectiveDeterminants.Complex R)

/-- The actual bounded target, with all native degreewise scalar maps retained. -/
structure ScalarPresentation where
  target : BoundedProjectiveDeterminants.Complex S
  cochain : target.cochain ≅ scalarComplex g C.cochain
  support : nonzeroDegrees S target (degrees R C) = degrees S target

variable (D : ScalarPresentation g C)

/-- The original semilinear source map in every cochain degree. -/
def component (i : ℤ) : C.cochain.X i →ₛₗ[g.hom] D.target.cochain.X i where
  toFun x := (D.cochain.inv.f i)
    ((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app (C.cochain.X i) x)
  map_add' x y := by
    change (D.cochain.inv.f i).hom
      (((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app (C.cochain.X i)).hom (x+y)) = _
    rw [LinearMap.map_add, LinearMap.map_add]
  map_smul' r x := by
    change (D.cochain.inv.f i).hom
      (((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app (C.cochain.X i)).hom (r • x)) = _
    rw [LinearMap.map_smul]
    exact (D.cochain.inv.f i).hom.map_smul (g.hom r) _

/-- Source determinant maps are fixed by exterior images and actual dual evaluation. -/
structure TermSources where
  scalar : ∀ i : ℤ, IsScalarExtension g.hom (component g C D i)
  determinant : ∀ i : ℤ, BaseChangeDeterminant g.hom (component g C D i) (scalar i)
  dual : ∀ i : ℤ,
    Module.Dual R (determinantModule R (C.cochain.X i)) →ₛₗ[g.hom]
      Module.Dual S (determinantModule S (D.target.cochain.X i))
  dual_normalized : ∀ (i : ℤ)
    (a : Module.Dual R (determinantModule R (C.cochain.X i)))
    (v : determinantModule R (C.cochain.X i)),
    dual i a ((determinant i).map v) = g.hom (a v)
  dual_scalar : ∀ i : ℤ, IsScalarExtension g.hom (dual i)

variable (T : TermSources g C D)

/-- The actual signed factor map, retaining the source exterior and dual normalizations. -/
def termMap (i : ℤ) : term R C i →ₛₗ[g.hom] term S D.target i := by
  classical
  by_cases h : Even i
  · have hr : term R C i = ModuleCat.of R (determinantModule R (C.cochain.X i)) := by
      simp [term, h]
    have hs : term S D.target i = ModuleCat.of S (determinantModule S (D.target.cochain.X i)) := by
      simp [term, h]
    rw [hr, hs]
    exact (T.determinant i).map
  · have hr : term R C i =
        ModuleCat.of R (Module.Dual R (determinantModule R (C.cochain.X i))) := by
      simp [term, h]
    have hs : term S D.target i =
        ModuleCat.of S (Module.Dual S (determinantModule S (D.target.cochain.X i))) := by
      simp [term, h]
    rw [hr, hs]
    exact T.dual i

/-- The actual empty-tensor scalar map. -/
def unitMap : (𝟙_ (ModuleCat.{0} R)) →ₛₗ[g.hom] (𝟙_ (ModuleCat.{0} S)) where
  toFun := g.hom
  map_add' := map_add g.hom
  map_smul' r a := map_mul g.hom r a

/-- Every ordered tensor comparison is computed from its actual term maps. -/
def tensorMap : (is : List ℤ) → tensorTerms R C is →ₛₗ[g.hom] tensorTerms S D.target is
  | [] => unitMap g
  | i :: is => TensorProduct.map (termMap g C D T i) (tensorMap is)

/-- The scalar determinant map trims exactly the zero terms of the true target. -/
def determinantMap : determinantObject R C →ₛₗ[g.hom] determinantObject S D.target :=
  ((eqToIso (congrArg (tensorTerms S D.target) D.support)).hom.hom.comp
    (removeZeroTerms S D.target (degrees R C)).hom.hom).comp
      (tensorMap g C D T (degrees R C))

/-- The complete scalar isomorphism is normalized by the native unit
on every actual determinant vector. -/
structure ScalarComparison where
  comparison : (ModuleCat.extendScalars g.hom).obj (determinantObject R C) ≅
    determinantObject S D.target
  normalized : ∀ x : determinantObject R C,
    comparison.hom
      ((ModuleCat.extendRestrictScalarsAdj g.hom).unit.app (determinantObject R C) x) =
        determinantMap g C D T x

end MathlibExt.AlgebraicGeometry.BoundedScalarDeterminants
