/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.UniverseKunneth.Coalgebra
public import MathlibExt.CategoryTheory.Monoidal.PointedComonFunctor

/-!
# Homology of coaugmented comonoids over a field

The Künneth monoidal structure over a field makes homology a functor on pointed comonoids,
from chain comonoids under the trivial tensor-unit comonoid to graded comonoids under its
homology counterpart.

The transported point is the scalar unit map followed by homology of the chain point. The
output agrees by an identity-component isomorphism with the direct homology coaugmentation
construction, retaining the field and module universe heights.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj ModuleCat.UniverseTensor

universe u v

namespace HomologicalComplex.UniverseKunneth

variable {k : Type u} [Field k]

attribute [local instance] ComonObj.instTensorUnit

local instance : HasFiniteBiproducts (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) :=
  CategoryTheory.Abelian.hasFiniteBiproducts
    (C := ModuleCat.UniverseScalarRestriction.Modules.{u, v} k)
/-- The closed tensor structure of the field module category.

Use the monoidal closed structure at the specified field and module heights. -/
local instance instMonoidalClosedModules :
    MonoidalClosed (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u, v} (R := k)

/-- The field Künneth monoidal structure on homology.

Use the field tensor-homology comparison to give homology its monoidal functor structure. -/
local instance homologyMonoidal : (homologyFunctor.{u, v} (R := k)).Monoidal := monoidalOfField.{u, v}

/-- The inverse homology unit comparison is the scalar unit map.

The inverse oplax unit comparison equals unitMap. -/
theorem homology_unit_inv :
    inv (Functor.OplaxMonoidal.η (homologyFunctor.{u, v} (R := k))) = unitMap.{u, v} (R := k) := by
  let H := homologyFunctor.{u, v} (R := k)
  apply (cancel_mono (Functor.OplaxMonoidal.η H)).1
  rw [IsIso.inv_hom_id]
  have h : unitMap.{u, v} (R := k) ≫ Functor.OplaxMonoidal.η H = 𝟙 _ := by
    exact Functor.Monoidal.ε_η H
  exact h.symm

/-- The homology functor on pointed comonoids.

Apply the monoidal homology functor to comonoids with a point from the trivial tensor-unit
comonoid. -/
def coaugmentedFunctor :
    Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ)) ⥤
      Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k))) :=
  (homologyFunctor.{u, v} (R := k)).mapPointedComon

/-- The point of the homology comonoid.

Its point is unitMap followed by homology of the chain coaugmentation. -/
theorem coaugmentedFunctor_obj_point
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    ((coaugmentedFunctor.{u, v} (k := k)).obj A).hom.hom =
      unitMap.{u, v} (R := k) ≫ (homologyFunctor.{u, v} (R := k)).map A.hom.hom := by
  have h := Functor.mapPointedComon_obj_point (homologyFunctor.{u, v} (R := k)) A
  exact h.trans (congrArg
    (fun u => u ≫ (homologyFunctor.{u, v} (R := k)).map A.hom.hom) homology_unit_inv)

/-- The stored chain point preserves comultiplication and counit.

The point map of an under-object is a comonoid morphism from the tensor unit. -/
theorem pointedChainMapIsComonHom
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    letI : ComonObj A.right.X := A.right.comon
    IsComonHom (show 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ) ⟶
      A.right.X from A.hom.hom) := A.hom.isComonHom_hom

/-- The direct pointed homology construction.

Apply the homology coaugmentation construction to the chain comonoid and its supplied point
map. -/
def coaugmentedExistingPointed
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k))) := by
  letI : ComonObj A.right.X := A.right.comon
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ) ⟶ A.right.X := A.hom.hom
  letI : IsComonHom η := pointedChainMapIsComonHom A
  exact coaugmented.{u, v} A.right.X η

/-- The comparison of the two pointed homology constructions.

The functorial and direct outputs are isomorphic through the identity on the homology
comonoid. -/
def coaugmentedFunctorObjIso
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    (coaugmentedFunctor.{u, v} (k := k)).obj A ≅ coaugmentedExistingPointed A := by
  refine Under.isoMk (Iso.refl _) ?_
  apply Comon.Hom.ext
  simp only [Comon.comp_hom']
  exact coaugmentedFunctor_obj_point A

/-- The underlying map of pointed homology functoriality.

A pointed chain morphism is sent to its homology map on the comonoid carriers. -/
theorem coaugmentedFunctor_map_hom
    {A B : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))}
    (f : A ⟶ B) :
    ((coaugmentedFunctor.{u, v} (k := k)).map f).right.hom =
      (homologyFunctor.{u, v} (R := k)).map f.right.hom := rfl

end HomologicalComplex.UniverseKunneth

end
