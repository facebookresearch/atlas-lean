/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationDiagram

/-!
# Naturality of the first-quadrant horizontal filtration

A bicomplex map preserves every horizontal filtration stage of the signed
total complex.  This file constructs the stagewise chain maps, proves their
compatibility with the full total and with changes of filtration stage, and
packages the construction as a functor to filtered chain complexes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Degreewise map between horizontal filtration stages induced by a
bicomplex map. -/
noncomputable def horizontalFilteredTotalMapOfBicomplex
    (f : K ⟶ L) (k n : ℕ) :
    horizontalFilteredTotalObj K k n ⟶
      horizontalFilteredTotalObj L k n :=
  Sigma.desc fun pq : DownNatHorizontalFilteredFiber n k ↦
    (f.f pq.val.val.1).f pq.val.val.2 ≫
      horizontalFilteredTotalι L k n pq

omit [HasZeroObject C] in
/-- The stage map has the expected formula on every filtered bidegree
summand. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalι_mapOfBicomplex
    (f : K ⟶ L) (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫
        horizontalFilteredTotalMapOfBicomplex f k n =
      (f.f pq.val.val.1).f pq.val.val.2 ≫
        horizontalFilteredTotalι L k n pq := by
  apply Sigma.ι_comp_desc

omit [HasZeroObject C] in
/-- A stagewise bicomplex map commutes with inclusion into the full total
complex. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalMapOfBicomplex_toTotal
    (f : K ⟶ L) (k n : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f k n ≫
        horizontalFilteredTotalToTotal L k n =
      horizontalFilteredTotalToTotal K k n ≫
        (total.map f (ComplexShape.down ℕ)).f n := by
  apply Sigma.hom_ext
  intro pq
  change horizontalFilteredTotalι K k n pq ≫
      (horizontalFilteredTotalMapOfBicomplex f k n ≫
        horizontalFilteredTotalToTotal L k n) =
    horizontalFilteredTotalι K k n pq ≫
      (horizontalFilteredTotalToTotal K k n ≫
        (total.map f (ComplexShape.down ℕ)).f n)
  rw [← Category.assoc,
    horizontalFilteredTotalι_mapOfBicomplex,
    Category.assoc, horizontalFilteredTotalι_toTotal,
    ← Category.assoc, horizontalFilteredTotalι_toTotal,
    HomologicalComplex₂.ιTotal_map]

/-- The stagewise degree maps induced by a bicomplex map form a chain map. -/
noncomputable def horizontalFilteredTotalComplexMapOfBicomplex
    (f : K ⟶ L) (k : ℕ) :
    horizontalFilteredTotalComplex K k ⟶
      horizontalFilteredTotalComplex L k where
  f := horizontalFilteredTotalMapOfBicomplex f k
  comm' := by
    intro n m hnm
    obtain rfl : n = m + 1 := hnm.symm
    dsimp only [horizontalFilteredTotalComplex]
    apply (cancel_mono
      (horizontalFilteredTotalToTotal L k m)).1
    simp only [Category.assoc,
      horizontalFilteredTotalD_toTotal,
      horizontalFilteredTotalMapOfBicomplex_toTotal_assoc,
      horizontalFilteredTotalMapOfBicomplex_toTotal]
    rw [(total.map f (ComplexShape.down ℕ)).comm (m + 1) m]
    rw [horizontalFilteredTotalD_toTotal_assoc]

omit [HasZeroObject C] in
/-- The stagewise chain map commutes with the chain-map inclusion into the
full total complex. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalComplexMapOfBicomplex_toTotal
    (f : K ⟶ L) (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex f k ≫
        horizontalFilteredTotalComplexToTotal L k =
      horizontalFilteredTotalComplexToTotal K k ≫
        total.map f (ComplexShape.down ℕ) := by
  ext n
  dsimp only [HomologicalComplex.comp_f,
    horizontalFilteredTotalComplexMapOfBicomplex,
    horizontalFilteredTotalComplexToTotal]
  exact horizontalFilteredTotalMapOfBicomplex_toTotal f k n

omit [HasZeroObject C] in
/-- Stagewise bicomplex maps commute with increasing the filtration stage. -/
theorem horizontalFilteredTotalComplexMapOfBicomplex_naturality
    (f : K ⟶ L) {k l : ℕ} (h : k ≤ l) :
    horizontalFilteredTotalComplexMapOfBicomplex f k ≫
        horizontalFilteredTotalComplexMap L h =
      horizontalFilteredTotalComplexMap K h ≫
        horizontalFilteredTotalComplexMapOfBicomplex f l := by
  ext n
  dsimp only [HomologicalComplex.comp_f,
    horizontalFilteredTotalComplexMapOfBicomplex,
    horizontalFilteredTotalComplexMap]
  apply (cancel_mono
    (horizontalFilteredTotalToTotal L l n)).1
  simp only [Category.assoc,
    horizontalFilteredTotalMapOfBicomplex_toTotal,
    horizontalFilteredTotalMap_toTotal_assoc,
    horizontalFilteredTotalMap_toTotal]

/-- The total complex equipped with its horizontal filtration. -/
noncomputable def horizontalTotalFilteredObject
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    CategoryTheory.FilteredObject (ChainComplex C ℕ) ℕ where
  X := K.total (ComplexShape.down ℕ)
  filtration := horizontalTotalFiltration K

/-- A bicomplex map induces a morphism of horizontally filtered total
complexes. -/
noncomputable def horizontalTotalFilteredObjectMap (f : K ⟶ L) :
    horizontalTotalFilteredObject K ⟶
      horizontalTotalFilteredObject L :=
  CategoryTheory.FilteredObject.homMk
    (total.map f (ComplexShape.down ℕ))
    (fun k ↦ horizontalFilteredTotalComplexMapOfBicomplex f k)
    (fun k ↦ horizontalFilteredTotalComplexMapOfBicomplex_toTotal f k)

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFilteredObjectMap_hom (f : K ⟶ L) :
    (horizontalTotalFilteredObjectMap f).hom =
      total.map f (ComplexShape.down ℕ) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFilteredObjectMap_natTrans_app
    (f : K ⟶ L) (k : ℕ) :
    (horizontalTotalFilteredObjectMap f).natTrans.app k =
      horizontalFilteredTotalComplexMapOfBicomplex f k :=
  rfl

/-- First-quadrant bicomplexes map functorially to horizontally filtered
total complexes. -/
noncomputable def horizontalTotalFilteredObjectFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject (ChainComplex C ℕ) ℕ where
  obj := horizontalTotalFilteredObject
  map := horizontalTotalFilteredObjectMap
  map_id K := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_id K (ComplexShape.down ℕ)
  map_comp f g := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_comp f g (ComplexShape.down ℕ)

end HomologicalComplex₂

end
