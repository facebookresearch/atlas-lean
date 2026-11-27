/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Cycles from a coaugmentation

Applying an additive functor to a coaugmentation gives a degree-zero cycle.
The cycle inclusion recovers the mapped coaugmentation, and a cochain
isomorphism transports the same cycle. Source and target category universes
are independent.
-/

@[expose] public section
section
noncomputable section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The image of a coaugmentation gives its degree-zero cycle. -/
def mappedCoaugmentationCycle (F : C ⥤ D) [F.Additive]
    {X : C} (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) :
    F.obj X ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).cycles 0 :=
  ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).liftCycles (F.map (ι.f 0)) 1 (by simp) (by
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map ((ι.comm 0 1).trans (by
        rw [HomologicalComplex.single_obj_d, zero_comp]))).trans (F.map_zero _ _)))

/-- The mapped augmentation cycle retains its exact coefficient arrow. -/
theorem mappedCoaugmentationCycle_i (F : C ⥤ D) [F.Additive]
    {X : C} (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) :
    F.mappedCoaugmentationCycle I ι ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).iCycles 0 = F.map (ι.f 0) := by
  apply HomologicalComplex.liftCycles_i

/-- Transporting the augmentation cycle by a cochain iso retains
the mapped coaugmentation coefficient under its forward map. -/
theorem mappedCoaugmentationCycle_transport_i (F : C ⥤ D) [F.Additive]
    {X : C} (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (K : CochainComplex D ℕ) (e : K ≅ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I) :
    (F.mappedCoaugmentationCycle I ι ≫ HomologicalComplex.cyclesMap e.inv 0) ≫
      K.iCycles 0 ≫ e.hom.f 0 = F.map (ι.f 0) := by
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  have hn := HomologicalComplex.cyclesMap_i e.inv 0
  have hid : e.inv.f 0 ≫ e.hom.f 0 = 𝟙 (L.X 0) :=
    (HomologicalComplex.comp_f e.inv e.hom 0).symm.trans
      ((HomologicalComplex.congr_hom e.inv_hom_id 0).trans (HomologicalComplex.id_f L 0))
  have hi := F.mappedCoaugmentationCycle_i I ι
  change (F.mappedCoaugmentationCycle I ι ≫ HomologicalComplex.cyclesMap e.inv 0) ≫
    K.iCycles 0 ≫ e.hom.f 0 = _
  rw [Category.assoc]
  exact (congrArg (fun q => F.mappedCoaugmentationCycle I ι ≫ q) (Category.assoc _ _ _).symm).trans
    ((congrArg (fun q => F.mappedCoaugmentationCycle I ι ≫ q ≫ e.hom.f 0) hn).trans
    (by
      have h' : F.mappedCoaugmentationCycle I ι ≫ L.iCycles 0 ≫ (e.inv.f 0 ≫ e.hom.f 0) =
          F.map (ι.f 0) := by
        rw [hid, Category.comp_id]
        exact hi
      simpa only [Category.assoc] using h'))

end CategoryTheory.Functor
end
