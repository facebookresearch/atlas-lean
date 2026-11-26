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
# Normalized Moore chains under additive functors

Let `F : C ⥤ D` be an additive functor between abelian categories, and let `X` be a simplicial
object of `C`. The normalized Moore comparison is a natural isomorphism `F(NX) ≅ N(X ⋙ F)`.

Its forward map is the mapped Moore inclusion, the alternating-complex comparison, and the
target Moore projection. Its inverse is the target Moore inclusion, inverse alternating
comparison, and mapped source Moore projection. The two maps agree with the corresponding
composition of Dold–Kan normalization homotopy equivalences. In each degree the alternating
comparison is the identity on the component carrier.
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

/-- The inverse Moore comparison and mapped normalized inclusion.

The inverse comparison followed by `F` of the source Moore inclusion equals the target Moore
inclusion followed by the inverse alternating-complex comparison. -/
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

/-- The forward map of additive normalized Moore comparison.

The forward map `F(NX) → N(FX)` is `F` of the Moore inclusion, followed by alternating-complex
transport and the target Moore projection. -/
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

/-- The inverse map of additive normalized Moore comparison.

The inverse map `N(FX) → F(NX)` is the target Moore inclusion, inverse alternating-complex
transport, and `F` of the source Moore projection. -/
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

/-- The forward Moore comparison through normalization homotopy equivalences.

The forward isomorphism map equals the composite of the mapped source Dold–Kan homotopy
equivalence, the alternating-complex isomorphism, and the inverse target Dold–Kan homotopy
equivalence. -/
theorem mooreCompMapIso_hom_eq_nativeHomotopyEquiv (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).hom =
      ((F.mapHomotopyEquiv
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X))).trans
        ((HomotopyEquiv.ofIso
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X)).trans
          (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X ⋙ F)).symm)).hom := by
  rw [mooreCompMapIso_hom]
  rfl

/-- The inverse Moore comparison through normalization homotopy equivalences.

The inverse isomorphism map equals the inverse map of that composite normalization homotopy
equivalence. -/
theorem mooreCompMapIso_inv_eq_nativeHomotopyEquiv (X : SimplicialObject C) :
    (((mooreCompMapIso F).app X)).inv =
      ((F.mapHomotopyEquiv
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X))).trans
        ((HomotopyEquiv.ofIso
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X)).trans
          (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X ⋙ F)).symm)).inv := by
  rw [mooreCompMapIso_inv]
  exact (Category.assoc _ _ _).symm

/-- The degreewise formula for forward additive Moore comparison.

In degree `n`, the comparison is `F` of the source normalized inclusion followed by the target
Moore projection. -/
theorem mooreCompMapIso_hom_f (X : SimplicialObject C) (n : ℕ) :
    (((mooreCompMapIso F).app X)).hom.f n =
      F.map ((inclusionOfMooreComplexMap X).f n) ≫
        (PInftyToNormalizedMooreComplex (X ⋙ F)).f n := by
  rw [mooreCompMapIso_hom]
  change F.map ((inclusionOfMooreComplexMap X).f n) ≫ 𝟙 _ ≫
    (PInftyToNormalizedMooreComplex (X ⋙ F)).f n = _
  rw [Category.id_comp]

/-- The degreewise formula for inverse additive Moore comparison.

In degree `n`, the inverse comparison is the target normalized inclusion followed by `F` of
the source Moore projection. -/
theorem mooreCompMapIso_inv_f (X : SimplicialObject C) (n : ℕ) :
    (((mooreCompMapIso F).app X)).inv.f n =
      (inclusionOfMooreComplexMap (X ⋙ F)).f n ≫
        F.map ((PInftyToNormalizedMooreComplex X).f n) := by
  rw [mooreCompMapIso_inv]
  change (inclusionOfMooreComplexMap (X ⋙ F)).f n ≫ 𝟙 _ ≫
    F.map ((PInftyToNormalizedMooreComplex X).f n) = _
  rw [Category.id_comp]

end AlgebraicTopology.NormalizedQuotient
