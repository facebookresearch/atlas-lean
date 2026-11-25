/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedQuotient.MapFunctor
public import MathlibExt.AlgebraicTopology.DoldKan.HomotopyNaturality
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Whiskering

/-!
# The canonical normalization isomorphism for an arbitrary additive functor

The existing quotient--Moore API supplies the canonical natural
isomorphism. Its split-projector preservation and native alternating
transport retain the actual Moore inclusion and retraction. This module
derives the component formulas and their homotopy comparison from that API.

The functor needs only additivity. It need not preserve arbitrary kernels,
exact sequences or homology. Both canonical maps agree with the maps in
the existing three-native-homotopy-equivalence construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.DoldKan

universe uC vC uD vD

namespace AlgebraicTopology.NormalizedQuotient

attribute [local implicit_reducible] normalizedMooreComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The canonical inverse retains the original mapped normalized inclusion square. -/
@[reassoc]
theorem mooreCompMapIso_inv_inclusion (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).inv ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) =
      inclusionOfMooreComplexMap (X ⋙ F) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X := by
  let e := ((mooreCompMapIso F).app X)
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X
  have h := mooreCompMapIso_hom_inclusion F X
  change e.hom ≫ inclusionOfMooreComplexMap (X ⋙ F) =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫ a.hom at h
  change e.inv ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) =
    inclusionOfMooreComplexMap (X ⋙ F) ≫ a.inv
  apply (cancel_mono a.hom).1
  calc
    (e.inv ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)) ≫ a.hom =
        e.inv ≫ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫ a.hom) :=
      Category.assoc _ _ _
    _ = e.inv ≫ (e.hom ≫ inclusionOfMooreComplexMap (X ⋙ F)) :=
      congrArg (fun f => e.inv ≫ f) h.symm
    _ = inclusionOfMooreComplexMap (X ⋙ F) := by rw [Iso.inv_hom_id_assoc]
    _ = (inclusionOfMooreComplexMap (X ⋙ F) ≫ a.inv) ≫ a.hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual forward component is the original mapped inclusion, native
alternating transport and original target normalization projection. -/
theorem mooreCompMapIso_hom (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
        PInftyToNormalizedMooreComplex (X ⋙ F) := by
  let e := ((mooreCompMapIso F).app X)
  let j := inclusionOfMooreComplexMap (X ⋙ F)
  let p := PInftyToNormalizedMooreComplex (X ⋙ F)
  have hs : j ≫ p = 𝟙 _ := (splitMonoInclusionOfMooreComplexMap (X ⋙ F)).id
  exact (Category.comp_id e.hom).symm.trans
    ((congrArg (fun q => e.hom ≫ q) hs.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ p) (mooreCompMapIso_hom_inclusion F X)).trans
          (Category.assoc _ _ _))))

/-- The actual inverse is the target inclusion, inverse alternating transport
and the original normalization projection mapped by the additive functor. -/
theorem mooreCompMapIso_inv (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).inv =
      inclusionOfMooreComplexMap (X ⋙ F) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (PInftyToNormalizedMooreComplex X) := by
  let e := ((mooreCompMapIso F).app X)
  let j := inclusionOfMooreComplexMap X
  let p := PInftyToNormalizedMooreComplex X
  have hs : j ≫ p = 𝟙 _ := (splitMonoInclusionOfMooreComplexMap X).id
  have hm : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map j ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map p = 𝟙 _ :=
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp j p).symm.trans
      ((congrArg (F.mapHomologicalComplex (ComplexShape.down ℕ)).map hs).trans
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map_id _))
  calc
    e.inv = e.inv ≫ 𝟙 _ := (Category.comp_id e.inv).symm
    _ = e.inv ≫ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map j ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) :=
      congrArg (fun q => e.inv ≫ q) hm.symm
    _ = (e.inv ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map j) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map p :=
      (Category.assoc _ _ _).symm
    _ = (inclusionOfMooreComplexMap (X ⋙ F) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map p :=
      congrArg (fun q => q ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) (mooreCompMapIso_inv_inclusion F X)
    _ = _ := Category.assoc _ _ _

/-- The forward map is exactly the existing composition of the three native
homotopy-equivalence maps. Its isomorphism property comes from the existing
quotient--Moore comparison. -/
theorem mooreCompMapIso_hom_eq_nativeHomotopyEquiv (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).hom =
      ((F.mapHomotopyEquiv
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X))).trans
        ((HomotopyEquiv.ofIso
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X)).trans
          (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X ⋙ F)).symm)).hom := by
  rw [mooreCompMapIso_hom]
  rfl

/-- The inverse map also agrees with the original native homotopy construction. -/
theorem mooreCompMapIso_inv_eq_nativeHomotopyEquiv (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).inv =
      ((F.mapHomotopyEquiv
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X))).trans
        ((HomotopyEquiv.ofIso
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X)).trans
          (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X ⋙ F)).symm)).inv := by
  rw [mooreCompMapIso_inv]
  exact (Category.assoc _ _ _).symm

/-- Every degree of the canonical forward map uses the original mapped
Moore inclusion and original target Moore projection. -/
theorem mooreCompMapIso_hom_f (X : SimplicialObject C) (n : ℕ) :
    (((mooreCompMapIso F).app X)).hom.f n =
      F.map ((inclusionOfMooreComplexMap X).f n) ≫
        (PInftyToNormalizedMooreComplex (X ⋙ F)).f n := by
  rw [mooreCompMapIso_hom]
  change F.map ((inclusionOfMooreComplexMap X).f n) ≫ 𝟙 _ ≫
    (PInftyToNormalizedMooreComplex (X ⋙ F)).f n = _
  rw [Category.id_comp]

/-- Every degree of the canonical inverse uses the original target
inclusion and the original Moore projection mapped by the additive functor. -/
theorem mooreCompMapIso_inv_f (X : SimplicialObject C) (n : ℕ) :
    (((mooreCompMapIso F).app X)).inv.f n =
      (inclusionOfMooreComplexMap (X ⋙ F)).f n ≫
        F.map ((PInftyToNormalizedMooreComplex X).f n) := by
  rw [mooreCompMapIso_inv]
  change (inclusionOfMooreComplexMap (X ⋙ F)).f n ≫ 𝟙 _ ≫
    F.map ((PInftyToNormalizedMooreComplex X).f n) = _
  rw [Category.id_comp]

end AlgebraicTopology.NormalizedQuotient
