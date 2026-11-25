/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration
public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationNaturality

/-!
# Naturality of the complete first-quadrant filtration

A bicomplex map preserves every extended-integer stage of the complete
horizontal filtration.  At bottom and negative finite indices this is the
zero map, at a nonnegative finite index it is the existing finite-stage map,
and at top it is the map of total complexes.

The resulting stage maps commute both with inclusion into the total complex
and with every transition in the complete filtration.  No spectral-object or
spectral-sequence construction is used here.
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
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A complete-stage bicomplex map bundled with its compatibility with the
inclusions into the total complexes. -/
noncomputable def horizontalCompleteFilteredTotalComplexMapOfBicomplexData
    (f : K ⟶ L) (i : EInt) :
    { g : horizontalCompleteFilteredTotalComplex K i ⟶
        horizontalCompleteFilteredTotalComplex L i //
      g ≫ horizontalCompleteFilteredTotalToTotal L i =
        horizontalCompleteFilteredTotalToTotal K i ≫
          total.map f (ComplexShape.down ℕ) } := by
  induction i using WithBotTop.rec with
  | bot =>
      refine ⟨0, ?_⟩
      change (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
          (HomologicalComplex.zero : ChainComplex C ℕ)) ≫ 0 =
        0 ≫ total.map f (ComplexShape.down ℕ)
      simp
  | coe a =>
      by_cases ha : 0 ≤ a
      · simp only [horizontalCompleteFilteredTotalComplex,
          horizontalCompleteFilteredTotalToTotal,
          horizontalCompleteFilteredTotalMonoOver,
          WithBotTop.rec_coe]
        rw [ite_eq_left ha, ite_eq_left ha]
        refine ⟨horizontalFilteredTotalComplexMapOfBicomplex f a.toNat, ?_⟩
        change horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
            horizontalFilteredTotalComplexToTotal L a.toNat =
          horizontalFilteredTotalComplexToTotal K a.toNat ≫
            total.map f (ComplexShape.down ℕ)
        exact horizontalFilteredTotalComplexMapOfBicomplex_toTotal
          f a.toNat
      · simp only [horizontalCompleteFilteredTotalComplex,
          horizontalCompleteFilteredTotalToTotal,
          horizontalCompleteFilteredTotalMonoOver,
          WithBotTop.rec_coe]
        rw [ite_eq_right ha, ite_eq_right ha]
        refine ⟨0, ?_⟩
        change (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
            (HomologicalComplex.zero : ChainComplex C ℕ)) ≫ 0 =
          0 ≫ total.map f (ComplexShape.down ℕ)
        simp
  | top =>
      simp only [horizontalCompleteFilteredTotalComplex,
        horizontalCompleteFilteredTotalToTotal,
        horizontalCompleteFilteredTotalMonoOver,
        WithBotTop.rec_top]
      refine ⟨total.map f (ComplexShape.down ℕ), ?_⟩
      change total.map f (ComplexShape.down ℕ) ≫ 𝟙 _ =
        𝟙 _ ≫ total.map f (ComplexShape.down ℕ)
      simp

/-- The map induced by a bicomplex map on an arbitrary extended-integer
stage of the complete horizontal filtration. -/
noncomputable def horizontalCompleteFilteredTotalComplexMapOfBicomplex
    (f : K ⟶ L) (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex L i :=
  (horizontalCompleteFilteredTotalComplexMapOfBicomplexData f i).1

/-- The map on every complete-filtration stage commutes with inclusion into
the corresponding total complex. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal
    (f : K ⟶ L) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalToTotal L i =
      horizontalCompleteFilteredTotalToTotal K i ≫
        total.map f (ComplexShape.down ℕ) :=
  (horizontalCompleteFilteredTotalComplexMapOfBicomplexData f i).2

/-- Bicomplex maps commute with every transition of the complete horizontal
filtration. -/
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    (f : K ⟶ L) {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalMap L h =
      horizontalCompleteFilteredTotalMap K h ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f j := by
  apply (cancel_mono
    (horizontalCompleteFilteredTotalToTotal L j)).1
  calc
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
          horizontalCompleteFilteredTotalMap L h) ≫
        horizontalCompleteFilteredTotalToTotal L j =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        (horizontalCompleteFilteredTotalMap L h ≫
          horizontalCompleteFilteredTotalToTotal L j) :=
      Category.assoc _ _ _
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalToTotal L i := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalToTotal K i ≫
        total.map f (ComplexShape.down ℕ) :=
      horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f i
    _ = (horizontalCompleteFilteredTotalMap K h ≫
          horizontalCompleteFilteredTotalToTotal K j) ≫
        total.map f (ComplexShape.down ℕ) := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalMap K h ≫
        (horizontalCompleteFilteredTotalToTotal K j ≫
          total.map f (ComplexShape.down ℕ)) :=
      Category.assoc _ _ _
    _ = horizontalCompleteFilteredTotalMap K h ≫
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f j ≫
          horizontalCompleteFilteredTotalToTotal L j) := by
      rw [horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = (horizontalCompleteFilteredTotalMap K h ≫
          horizontalCompleteFilteredTotalComplexMapOfBicomplex f j) ≫
        horizontalCompleteFilteredTotalToTotal L j :=
      (Category.assoc _ _ _).symm

/-- The total complex equipped with its complete extended-integer horizontal
filtration. -/
noncomputable def horizontalCompleteTotalFilteredObject
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    CategoryTheory.FilteredObject (ChainComplex C ℕ) EInt where
  X := K.total (ComplexShape.down ℕ)
  filtration := horizontalCompleteTotalFiltration K

/-- A bicomplex map induces a morphism between the completely filtered total
complexes. -/
noncomputable def horizontalCompleteTotalFilteredObjectMap (f : K ⟶ L) :
    horizontalCompleteTotalFilteredObject K ⟶
      horizontalCompleteTotalFilteredObject L :=
  CategoryTheory.FilteredObject.homMk
    (total.map f (ComplexShape.down ℕ))
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f)
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f)

@[simp]
theorem horizontalCompleteTotalFilteredObjectMap_hom (f : K ⟶ L) :
    (horizontalCompleteTotalFilteredObjectMap f).hom =
      total.map f (ComplexShape.down ℕ) :=
  rfl

@[simp]
theorem horizontalCompleteTotalFilteredObjectMap_natTrans_app
    (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteTotalFilteredObjectMap f).natTrans.app i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i :=
  rfl

end HomologicalComplex₂

end
