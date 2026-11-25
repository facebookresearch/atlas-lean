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
# The existing original-field homology functor on pointed comonoids

Specialize the general native pointed-comonoid functor to the already earned
original-field Künneth monoidal structure. Its inverse unit comparison is
the existing scalar `unitMap`; the underlying objects and point maps agree
with the existing `coaugmented` producer.
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
/-- The existing monoidal-closed structure over the original field and module height. -/
local instance instMonoidalClosedModules :
    MonoidalClosed (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u, v} (R := k)

/-- The original-field monoidal structure is the existing earned Künneth structure. -/
local instance homologyMonoidal : (homologyFunctor.{u, v} (R := k)).Monoidal := monoidalOfField.{u, v}

/-- The inverse unit comparison is exactly the existing original-field scalar unit map. -/
theorem homology_unit_inv :
    inv (Functor.OplaxMonoidal.η (homologyFunctor.{u, v} (R := k))) = unitMap.{u, v} (R := k) := by
  let H := homologyFunctor.{u, v} (R := k)
  apply (cancel_mono (Functor.OplaxMonoidal.η H)).1
  rw [IsIso.inv_hom_id]
  have h : unitMap.{u, v} (R := k) ≫ Functor.OplaxMonoidal.η H = 𝟙 _ := by
    exact Functor.Monoidal.ε_η H
  exact h.symm

/-- Specialization of the existing general pointed transport to original-field homology. -/
def coaugmentedFunctor :
    Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ)) ⥤
      Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k))) :=
  (homologyFunctor.{u, v} (R := k)).mapPointedComon

/-- The transported point is the existing canonical original-field homology coaugmentation. -/
theorem coaugmentedFunctor_obj_point
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    ((coaugmentedFunctor.{u, v} (k := k)).obj A).hom.hom =
      unitMap.{u, v} (R := k) ≫ (homologyFunctor.{u, v} (R := k)).map A.hom.hom := by
  have h := Functor.mapPointedComon_obj_point (homologyFunctor.{u, v} (R := k)) A
  exact h.trans (congrArg
    (fun u => u ≫ (homologyFunctor.{u, v} (R := k)).map A.hom.hom) homology_unit_inv)

/-- The original pointed chain map has its stored native tensor-unit comonoid laws. -/
theorem pointedChainMapIsComonHom
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    letI : ComonObj A.right.X := A.right.comon
    IsComonHom (show 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ) ⟶
      A.right.X from A.hom.hom) := A.hom.isComonHom_hom

/-- The existing original-field producer applied to the actual point, with its native laws. -/
def coaugmentedExistingPointed
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k))) := by
  letI : ComonObj A.right.X := A.right.comon
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ) ⟶ A.right.X := A.hom.hom
  letI : IsComonHom η := pointedChainMapIsComonHom A
  exact coaugmented.{u, v} A.right.X η

/-- The canonical native point comparison identifies the output with the existing producer. -/
def coaugmentedFunctorObjIso
    (A : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))) :
    (coaugmentedFunctor.{u, v} (k := k)).obj A ≅ coaugmentedExistingPointed A := by
  refine Under.isoMk (Iso.refl _) ?_
  apply Comon.Hom.ext
  simp only [Comon.comp_hom']
  exact coaugmentedFunctor_obj_point A

/-- The underlying pointed map remains the original homology map of the original chain morphism. -/
theorem coaugmentedFunctor_map_hom
    {A B : Under (Comon.trivial (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u, v} k) ℕ))}
    (f : A ⟶ B) :
    ((coaugmentedFunctor.{u, v} (k := k)).map f).right.hom =
      (homologyFunctor.{u, v} (R := k)).map f.right.hom := rfl

end HomologicalComplex.UniverseKunneth

end
