/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.TheoremAStar
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
public import MathlibExt.CategoryTheory.CategoryBar.CommaLeftComparison
public import MathlibExt.CategoryTheory.CategoryBar.CommaRightComparison

import MathlibExt.CategoryTheory.CategoryBar.CommaRightPointNaturality
import MathlibExt.CategoryTheory.CategoryBar.SimplicialReplacement
import MathlibExt.CategoryTheory.Enriched.WeightedBarSimplicial
import MathlibExt.CategoryTheory.NerveData
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Quillen's Theorem A for realization weak equivalences

This file proves the realization form of Quillen's Theorem A from weak
contractibility of the left comma categories `d ↓ F`.  The proof uses a
private two-sided weighted-bar carrier.  Its target fibers compare with the
specified left comma categories; its source fibers compare with right comma
categories having canonical terminal objects.

The carrier, fiber comparisons, deformations, and homotopy bridge are private.
No final/cofinal API, Theorem B, model structure, or strict-fiber/comma
identification is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial CartesianMonoidalCategory
open scoped CategoryTheory.Prod MonoidalCategory

universe u v w

namespace CategoryTheory

private noncomputable def quillenAMappingDiagram
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : C ⥤ SSet.{max u v} where
  obj c := CategoryBar.categoryBar
    (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj c))
    (L := CategoryBar.unitCoeffL D)
  map {c c'} f := CategoryBar.categoryBarMap
    (CategoryBar.commaCoeffRMap (𝟭 D) (F.map f))
    (𝟙 (CategoryBar.unitCoeffL D))
  map_id c := by
    rw [F.map_id]
    have hR : CategoryBar.commaCoeffRMap (𝟭 D) (𝟙 (F.obj c)) = 𝟙 _ := by
      ext X h
      induction X using Opposite.rec with
      | _ X =>
        change (X ⟶ F.obj c) at h
        change h ≫ 𝟙 (F.obj c) = h
        simp
    rw [hR, CategoryBar.categoryBarMap_id]
  map_comp {c c' c''} f g := by
    rw [F.map_comp]
    have hR : CategoryBar.commaCoeffRMap (𝟭 D) (F.map f ≫ F.map g) =
        CategoryBar.commaCoeffRMap (𝟭 D) (F.map f) ≫
          CategoryBar.commaCoeffRMap (𝟭 D) (F.map g) := by
      ext X h
      induction X using Opposite.rec with
      | _ X =>
        change (X ⟶ F.obj c) at h
        change h ≫ (F.map f ≫ F.map g) = (h ≫ F.map f) ≫ F.map g
        simp
    rw [hR]
    simpa only [Category.comp_id] using
      (CategoryBar.categoryBarMap_comp
        (CategoryBar.commaCoeffRMap (𝟭 D) (F.map f))
        (𝟙 (CategoryBar.unitCoeffL D))
        (CategoryBar.commaCoeffRMap (𝟭 D) (F.map g))
        (𝟙 (CategoryBar.unitCoeffL D))).symm

private noncomputable def quillenAMappingBisimplicial
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : SimplicialObject SSet.{max u v} :=
  StrictOrdinaryWeightedBar.wbarSimplicial
    (CategoryBar.replUnit C) (quillenAMappingDiagram F)

private noncomputable def quillenAMappingCarrier
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj (quillenAMappingBisimplicial F)

private abbrev quillenAMappingIndex
    {C : Type u} [Category.{v} C] (n : ℕ)
    (H : ComposableArrows C n) :
    StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n :=
  ⟨H, PUnit.unit⟩

private def quillenAMappingCarrierInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    ((quillenAMappingDiagram F).obj H.left).obj (op ⦋n⦌) := by
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n
  exact ⟨G, ULift.up PUnit.unit, theta⟩

private noncomputable def quillenAMappingCarrierIncl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) :=
  (StrictOrdinaryWeightedBar.wbarIncl
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
    (⟨H, PUnit.unit⟩ :
      StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)).app
      (op ⦋n⦌)
    (⟨G, ULift.up PUnit.unit, theta⟩ :
      CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
        (CategoryBar.unitCoeffL D) n)

private noncomputable def quillenAMappingCarrierRawEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) ≃
      Σ p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n,
        ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
  ((Limits.sigmaObjIso (C := Type (max u v))
      (fun p : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n =>
        (quillenAMappingDiagram F).obj p.1.left) (op ⦋n⦌)).trans
    (Types.coproductIso
      (fun p : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n =>
        ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)))).toEquiv

private theorem quillenAMappingCarrierRawEquiv_wbarIncl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawEquiv F n
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op ⦋n⦌) x) = ⟨p, x⟩ := by
  let f := fun p :
      StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n ↦
    (quillenAMappingDiagram F).obj p.1.left
  let a : SimplexCategoryᵒᵖ := op ⦋n⦌
  have hEval := ConcreteCategory.congr_hom
    (Limits.ι_comp_sigmaObjIso_hom f a p) x
  change (Types.coproductIso (fun s ↦ (f s).obj a)).toEquiv
      ((Limits.sigmaObjIso f a).toEquiv
        (ConcreteCategory.hom ((Limits.Sigma.ι f p).app a) x)) = ⟨p, x⟩
  change (Limits.sigmaObjIso f a).toEquiv
      (ConcreteCategory.hom ((Limits.Sigma.ι f p).app a) x) =
    ConcreteCategory.hom (Limits.Sigma.ι (fun s ↦ (f s).obj a) p) x at hEval
  rw [hEval]
  exact Types.coproductIso_ι_comp_hom_apply _ _ _

@[simp]
private theorem quillenAMappingCarrierRawEquiv_incl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierRawEquiv F n
        (quillenAMappingCarrierIncl F n H G theta) =
      ⟨⟨H, PUnit.unit⟩,
        (by
          change CategoryBar.barObj D
            (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
            (CategoryBar.unitCoeffL D) n
          exact ⟨G, ULift.up PUnit.unit, theta⟩)⟩ := by
  unfold quillenAMappingCarrierRawEquiv quillenAMappingCarrierIncl
    quillenAMappingCarrier
  unfold StrictOrdinaryWeightedBar.wbarIncl
    StrictOrdinaryWeightedBar.wbarObj
  let fam := fun p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n =>
    (quillenAMappingDiagram F).obj p.1.left
  let p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n := ⟨H, PUnit.unit⟩
  let z : fam p |>.obj (op ⦋n⦌) :=
    (⟨G, ULift.up PUnit.unit, theta⟩ :
      CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
        (CategoryBar.unitCoeffL D) n)
  let efam := fun q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n => (fam q).obj (op ⦋n⦌)
  change ((Types.coproductIso efam).hom :
      (∐ efam) → (Σ q, efam q))
      (((Limits.sigmaObjIso (C := Type (max u v)) fam (op ⦋n⦌)).hom :
        (∐ fam).obj (op ⦋n⦌) → ∐ efam)
        ((Limits.Sigma.ι fam p).app (op ⦋n⦌) z)) = ⟨p, z⟩
  have hσ := Limits.ι_comp_sigmaObjIso_hom fam (op ⦋n⦌) p
  have hσz := ConcreteCategory.congr_hom hσ z
  simp only [ConcreteCategory.comp_apply] at hσz
  rw [hσz]
  exact Types.coproductIso_ι_comp_hom_apply efam p z

private def quillenAMappingCarrierRawToTriple
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    (Σ p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n,
        ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) ≃
      Σ H : ComposableArrows C n,
        Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left where
  toFun
    | ⟨⟨H, _⟩, ⟨G, _, theta⟩⟩ => ⟨H, G, theta⟩
  invFun
    | ⟨H, G, theta⟩ =>
      ⟨⟨H, PUnit.unit⟩,
        (by
          change CategoryBar.barObj D
            (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
            (CategoryBar.unitCoeffL D) n
          exact ⟨G, ULift.up PUnit.unit, theta⟩)⟩
  left_inv := by
    rintro ⟨⟨H, q⟩, ⟨G, l, theta⟩⟩
    change PUnit at q
    obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
    change ULift PUnit at l
    obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
    rfl
  right_inv := by
    rintro ⟨H, G, theta⟩
    rfl

private noncomputable def quillenAMappingCarrierObjEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) ≃
      Σ H : ComposableArrows C n,
        Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
  (quillenAMappingCarrierRawEquiv F n).trans
    (quillenAMappingCarrierRawToTriple F n)

@[simp]
private theorem quillenAMappingCarrierObjEquiv_incl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierObjEquiv F n
        (quillenAMappingCarrierIncl F n H G theta) =
      ⟨H, G, theta⟩ := by
  rw [quillenAMappingCarrierObjEquiv, Equiv.trans_apply,
    quillenAMappingCarrierRawEquiv_incl]
  rfl

private noncomputable def quillenAMappingCarrierFaceZeroInnerOf
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n p).1.left).obj (op ⦋n⦌) :=
  (SrepBridge.srepFaceZeroComponent
    (quillenAMappingDiagram F) p.1).app (op ⦋n⦌)
      (((quillenAMappingDiagram F).obj p.1.left).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op x)

private noncomputable def quillenAMappingCarrierFaceZeroInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n
          (quillenAMappingIndex (n + 1) H)).1.left).obj
            (op (SimplexCategory.mk n)) := by
  change ((quillenAMappingDiagram F).obj
    (SrepBridge.srepDropFirst H).left).obj
      (op (SimplexCategory.mk n))
  exact quillenAMappingCarrierFaceZeroInnerOf F n
    (quillenAMappingIndex (n + 1) H)
    (quillenAMappingCarrierInner F (n + 1) H G theta)

private theorem quillenAMappingCarrierRawEquiv_δ_zero_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ 0
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit C) (quillenAMappingDiagram F)
              (n + 1) p).app (op ⦋n + 1⦌) x)) =
      ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n p,
        quillenAMappingCarrierFaceZeroInnerOf F n p x⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ (0 : Fin (n + 2))).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit C) n p
  let c0 := quillenAMappingCarrierFaceZeroInnerOf F n p x
  unfold quillenAMappingCarrier
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).app (op ⦋n⦌)
      (((quillenAMappingBisimplicial F).obj (op ⦋n + 1⦌)).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n 0).app
        (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality
          (SimplexCategory.δ (0 : Fin (n + 2))).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner', StrictOrdinaryWeightedBar.wbarδ_zero]
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceZero_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p
  have hOuterApp := NatTrans.congr_app hOuter (op ⦋n⦌)
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  change (StrictOrdinaryWeightedBar.wbarFaceZero
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).app
        (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n p)).app (op ⦋n⦌)
      ((SrepBridge.srepFaceZeroComponent
        (quillenAMappingDiagram F) p.1).app (op ⦋n⦌) x0) at hOuterPt
  dsimp only [p0, c0, x0,
    quillenAMappingCarrierFaceZeroInnerOf]
  exact hOuterPt

private theorem quillenAMappingCarrierRawEquiv_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ 0
          (quillenAMappingCarrierIncl F (n + 1) H G theta)) =
      ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n
            (quillenAMappingIndex (n + 1) H),
        quillenAMappingCarrierFaceZeroInner F n H G theta⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1) :=
    quillenAMappingIndex (n + 1) H
  let x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op (SimplexCategory.mk (n + 1))) := by
    change ((quillenAMappingDiagram F).obj H.left).obj
      (op (SimplexCategory.mk (n + 1)))
    exact quillenAMappingCarrierInner F (n + 1) H G theta
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ (0 : Fin (n + 2))).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit C) n p
  let c0 := quillenAMappingCarrierFaceZeroInner F n H G theta
  unfold quillenAMappingCarrier quillenAMappingCarrierIncl
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).app
        (op (SimplexCategory.mk n))
      (((quillenAMappingBisimplicial F).obj
        (op (SimplexCategory.mk (n + 1)))).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n 0).app
        (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality
          (SimplexCategory.δ (0 : Fin (n + 2))).op) x
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceZero_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p
  have hOuterApp := NatTrans.congr_app hOuter
    (op (SimplexCategory.mk n))
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner', StrictOrdinaryWeightedBar.wbarδ_zero]
  change (StrictOrdinaryWeightedBar.wbarFaceZero
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).app
        (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n p)).app
      (op (SimplexCategory.mk n))
        ((SrepBridge.srepFaceZeroComponent
          (quillenAMappingDiagram F) p.1).app
            (op (SimplexCategory.mk n)) x0) at hOuterPt
  dsimp only [p0, c0, p, quillenAMappingIndex,
    quillenAMappingCarrierFaceZeroInner]
  exact hOuterPt

private noncomputable def quillenAMappingCarrierFaceLastInnerOf
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n p).1.left).obj (op ⦋n⦌) :=
  (SrepBridge.srepFaceLastComponent
    (quillenAMappingDiagram F) p.1).app (op ⦋n⦌)
      (((quillenAMappingDiagram F).obj p.1.left).map
        (SimplexCategory.δ (Fin.last (n + 1))).op x)

private noncomputable def quillenAMappingCarrierFaceLastInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n
          (quillenAMappingIndex (n + 1) H)).1.left).obj
            (op (SimplexCategory.mk n)) := by
  change ((quillenAMappingDiagram F).obj
    (SrepBridge.srepDropLast H).left).obj
      (op (SimplexCategory.mk n))
  exact quillenAMappingCarrierFaceLastInnerOf F n
    (quillenAMappingIndex (n + 1) H)
    (quillenAMappingCarrierInner F (n + 1) H G theta)

private theorem quillenAMappingCarrierRawEquiv_δ_last_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ (Fin.last (n + 1))
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit C) (quillenAMappingDiagram F)
              (n + 1) p).app (op ⦋n + 1⦌) x)) =
      ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n p,
        quillenAMappingCarrierFaceLastInnerOf F n p x⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let i : Fin (n + 2) := Fin.last (n + 1)
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ i).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit C) n p
  let c0 := quillenAMappingCarrierFaceLastInnerOf F n p x
  unfold quillenAMappingCarrier
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ i).op).app (op ⦋n⦌)
      (((quillenAMappingBisimplicial F).obj (op ⦋n + 1⦌)).map
        (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality (SimplexCategory.δ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner']
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceLast_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p
  have hOuterApp := NatTrans.congr_app hOuter (op ⦋n⦌)
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  rw [show i = Fin.last (n + 1) from rfl,
    StrictOrdinaryWeightedBar.wbarδ_last]
  change (StrictOrdinaryWeightedBar.wbarFaceLast
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).app
        (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n p)).app (op ⦋n⦌)
      ((SrepBridge.srepFaceLastComponent
        (quillenAMappingDiagram F) p.1).app (op ⦋n⦌) x0) at hOuterPt
  dsimp only [p0, c0, x0, i,
    quillenAMappingCarrierFaceLastInnerOf]
  exact hOuterPt

private theorem quillenAMappingCarrierRawEquiv_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ (Fin.last (n + 1))
          (quillenAMappingCarrierIncl F (n + 1) H G theta)) =
      ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n
            (quillenAMappingIndex (n + 1) H),
        quillenAMappingCarrierFaceLastInner F n H G theta⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1) :=
    quillenAMappingIndex (n + 1) H
  let x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op (SimplexCategory.mk (n + 1))) := by
    change ((quillenAMappingDiagram F).obj H.left).obj
      (op (SimplexCategory.mk (n + 1)))
    exact quillenAMappingCarrierInner F (n + 1) H G theta
  let i : Fin (n + 2) := Fin.last (n + 1)
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ i).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit C) n p
  let c0 := quillenAMappingCarrierFaceLastInner F n H G theta
  unfold quillenAMappingCarrier quillenAMappingCarrierIncl
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ i).op).app (op (SimplexCategory.mk n))
      (((quillenAMappingBisimplicial F).obj
        (op (SimplexCategory.mk (n + 1)))).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality (SimplexCategory.δ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner']
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceLast_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p
  have hOuterApp := NatTrans.congr_app hOuter
    (op (SimplexCategory.mk n))
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  rw [show i = Fin.last (n + 1) from rfl,
    StrictOrdinaryWeightedBar.wbarδ_last]
  change (StrictOrdinaryWeightedBar.wbarFaceLast
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).app
        (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n p)).app
      (op (SimplexCategory.mk n))
        ((SrepBridge.srepFaceLastComponent
          (quillenAMappingDiagram F) p.1).app
            (op (SimplexCategory.mk n)) x0) at hOuterPt
  dsimp only [p0, c0, p, i, quillenAMappingIndex,
    quillenAMappingCarrierFaceLastInner]
  exact hOuterPt

private theorem quillenACastSucc_succ_ne_last {n : ℕ} (q : Fin n) :
    q.castSucc.succ ≠ Fin.last (n + 1) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
  omega

private noncomputable def quillenAMappingCarrierFaceInnerInnerOf
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q) p).1.left).obj
            (op ⦋n⦌) := by
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  exact (StrictOrdinaryWeightedBar.wFaceInnerComponent
    (quillenAMappingDiagram F) i hi0 p.1).app (op ⦋n⦌)
      (((quillenAMappingDiagram F).obj p.1.left).map
        (SimplexCategory.δ i).op x)

private noncomputable def quillenAMappingCarrierFaceInnerInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q)
          (quillenAMappingIndex (n + 1) H)).1.left).obj
            (op (SimplexCategory.mk n)) := by
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  change ((quillenAMappingDiagram F).obj
    (((StrictOmitDup.omitAt i).obj H).left)).obj
      (op (SimplexCategory.mk n))
  exact quillenAMappingCarrierFaceInnerInnerOf F n q
    (quillenAMappingIndex (n + 1) H)
    (quillenAMappingCarrierInner F (n + 1) H G theta)

private theorem quillenAMappingCarrierRawEquiv_δ_inner_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ q.castSucc.succ
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit C) (quillenAMappingDiagram F)
              (n + 1) p).app (op ⦋n + 1⦌) x)) =
      ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q) p,
        quillenAMappingCarrierFaceInnerInnerOf F n q p x⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  have hiLast : i ≠ Fin.last (n + 1) :=
    quillenACastSucc_succ_ne_last q
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ i).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceInnerIdx
    (CategoryBar.replUnit C) n i hiLast p
  let c0 := quillenAMappingCarrierFaceInnerInnerOf F n q p x
  unfold quillenAMappingCarrier
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ i).op).app (op ⦋n⦌)
      (((quillenAMappingBisimplicial F).obj (op ⦋n + 1⦌)).map
        (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op ⦋n⦌) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality (SimplexCategory.δ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner',
    StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ i hi0 hiLast]
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceInner_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F)
      n i hi0 hiLast p
  have hOuterApp := NatTrans.congr_app hOuter (op ⦋n⦌)
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  change (StrictOrdinaryWeightedBar.wbarFaceInner
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        n i hi0 hiLast).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n⦌) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n i hiLast p)).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wFaceInnerComponent
        (quillenAMappingDiagram F) i hi0 p.1).app
          (op ⦋n⦌) x0) at hOuterPt
  dsimp only [p0, c0, x0, i,
    quillenAMappingCarrierFaceInnerInnerOf]
  exact hOuterPt

private theorem quillenAMappingCarrierRawEquiv_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ q.castSucc.succ
          (quillenAMappingCarrierIncl F (n + 1) H G theta)) =
      ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q)
            (quillenAMappingIndex (n + 1) H),
        quillenAMappingCarrierFaceInnerInner F n q H G theta⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F n)
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  have hiLast : i ≠ Fin.last (n + 1) :=
    quillenACastSucc_succ_ne_last q
  let p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1) :=
    quillenAMappingIndex (n + 1) H
  let x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op (SimplexCategory.mk (n + 1))) := by
    change ((quillenAMappingDiagram F).obj H.left).obj
      (op (SimplexCategory.mk (n + 1)))
    exact quillenAMappingCarrierInner F (n + 1) H G theta
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.δ i).op x
  let p0 := StrictOrdinaryWeightedBar.wFaceInnerIdx
    (CategoryBar.replUnit C) n i hiLast p
  let c0 := quillenAMappingCarrierFaceInnerInner F n q H G theta
  unfold quillenAMappingCarrier quillenAMappingCarrierIncl
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.δ i).op).app (op (SimplexCategory.mk n))
      (((quillenAMappingBisimplicial F).obj
        (op (SimplexCategory.mk (n + 1)))).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ,
    StrictOrdinaryWeightedBar.wbarData_δ]
  change (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p0).app
          (op (SimplexCategory.mk n)) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        (n + 1) p).naturality (SimplexCategory.δ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)).map
          (SimplexCategory.δ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app
              (op (SimplexCategory.mk (n + 1))) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner',
    StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ i hi0 hiLast]
  have hOuter := StrictOrdinaryWeightedBar.wbarFaceInner_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F)
      n i hi0 hiLast p
  have hOuterApp := NatTrans.congr_app hOuter
    (op (SimplexCategory.mk n))
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  change (StrictOrdinaryWeightedBar.wbarFaceInner
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)
        n i hi0 hiLast).app (op (SimplexCategory.mk n))
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op (SimplexCategory.mk n)) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n i hiLast p)).app
      (op (SimplexCategory.mk n))
        ((StrictOrdinaryWeightedBar.wFaceInnerComponent
          (quillenAMappingDiagram F) i hi0 p.1).app
            (op (SimplexCategory.mk n)) x0) at hOuterPt
  dsimp only [p0, c0, p, i, quillenAMappingIndex,
    quillenAMappingCarrierFaceInnerInner]
  exact hOuterPt

private noncomputable def quillenAMappingCarrierDegInnerOf
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i p).1.left).obj
          (op ⦋n + 1⦌) :=
  (StrictOrdinaryWeightedBar.wDegInnerComponent
    (quillenAMappingDiagram F) i p.1).app (op ⦋n + 1⦌)
      (((quillenAMappingDiagram F).obj p.1.left).map
        (SimplexCategory.σ i).op x)

private noncomputable def quillenAMappingCarrierDegInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n)
    (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    ((quillenAMappingDiagram F).obj
      (StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i
          (quillenAMappingIndex n H)).1.left).obj
            (op (SimplexCategory.mk (n + 1))) := by
  change ((quillenAMappingDiagram F).obj
    (((StrictOmitDup.dupAt i).obj H).left)).obj
      (op (SimplexCategory.mk (n + 1)))
  exact quillenAMappingCarrierDegInnerOf F n i
    (quillenAMappingIndex n H)
    (quillenAMappingCarrierInner F n H G theta)

private theorem quillenAMappingCarrierRawEquiv_σ_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawEquiv F (n + 1)
        ((quillenAMappingCarrier F).σ i
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
              (op ⦋n⦌) x)) =
      ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i p,
        quillenAMappingCarrierDegInnerOf F n i p x⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F (n + 1))
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.σ i).op x
  let p0 := StrictOrdinaryWeightedBar.wDegInnerIdx
    (CategoryBar.replUnit C) n i p
  let c0 := quillenAMappingCarrierDegInnerOf F n i p x
  unfold quillenAMappingCarrier
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.σ i).op).app (op ⦋n + 1⦌)
      (((quillenAMappingBisimplicial F).obj (op ⦋n⦌)).map
        (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op ⦋n⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p0).app (op ⦋n + 1⦌) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_σ,
    StrictOrdinaryWeightedBar.wbarData_σ]
  change (StrictOrdinaryWeightedBar.wbarσ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op ⦋n + 1⦌)
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).map
          (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op ⦋n⦌) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p0).app (op ⦋n + 1⦌) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).naturality
        (SimplexCategory.σ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).map
          (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op ⦋n⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op ⦋n + 1⦌) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner']
  have hOuter := StrictOrdinaryWeightedBar.wbarσ_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i p
  have hOuterApp := NatTrans.congr_app hOuter (op ⦋n + 1⦌)
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  change (StrictOrdinaryWeightedBar.wbarσ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op ⦋n + 1⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op ⦋n + 1⦌) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
        (StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i p)).app (op ⦋n + 1⦌)
      ((StrictOrdinaryWeightedBar.wDegInnerComponent
        (quillenAMappingDiagram F) i p.1).app
          (op ⦋n + 1⦌) x0) at hOuterPt
  dsimp only [p0, c0, x0, quillenAMappingCarrierDegInnerOf]
  exact hOuterPt

private theorem quillenAMappingCarrierRawEquiv_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n)
    (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierRawEquiv F (n + 1)
        ((quillenAMappingCarrier F).σ i
          (quillenAMappingCarrierIncl F n H G theta)) =
      ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i (quillenAMappingIndex n H),
        quillenAMappingCarrierDegInner F n i H G theta⟩ := by
  rw [← quillenAMappingCarrierRawEquiv_wbarIncl]
  apply congrArg (quillenAMappingCarrierRawEquiv F (n + 1))
  let p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n := quillenAMappingIndex n H
  let x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op (SimplexCategory.mk n)) := by
    change ((quillenAMappingDiagram F).obj H.left).obj
      (op (SimplexCategory.mk n))
    exact quillenAMappingCarrierInner F n H G theta
  let x0 := ((quillenAMappingDiagram F).obj p.1.left).map
    (SimplexCategory.σ i).op x
  let p0 := StrictOrdinaryWeightedBar.wDegInnerIdx
    (CategoryBar.replUnit C) n i p
  let c0 := quillenAMappingCarrierDegInner F n i H G theta
  unfold quillenAMappingCarrier quillenAMappingCarrierIncl
  change ((quillenAMappingBisimplicial F).map
      (SimplexCategory.σ i).op).app
        (op (SimplexCategory.mk (n + 1)))
      (((quillenAMappingBisimplicial F).obj
        (op (SimplexCategory.mk n))).map
          (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op (SimplexCategory.mk n)) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p0).app
            (op (SimplexCategory.mk (n + 1))) c0
  unfold quillenAMappingBisimplicial
  unfold StrictOrdinaryWeightedBar.wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_σ,
    StrictOrdinaryWeightedBar.wbarData_σ]
  change (StrictOrdinaryWeightedBar.wbarσ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op (SimplexCategory.mk (n + 1)))
      ((StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).map
          (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op (SimplexCategory.mk n)) x)) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p0).app
            (op (SimplexCategory.mk (n + 1))) c0
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).naturality
        (SimplexCategory.σ i).op) x
  have hInner' :
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n).map
          (SimplexCategory.σ i).op
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
            (op (SimplexCategory.mk n)) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op (SimplexCategory.mk (n + 1))) x0 := by
    simpa only [x0, ConcreteCategory.comp_apply,
      CategoryTheory.comp_apply] using hInner.symm
  rw [hInner']
  have hOuter := StrictOrdinaryWeightedBar.wbarσ_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i p
  have hOuterApp := NatTrans.congr_app hOuter
    (op (SimplexCategory.mk (n + 1)))
  have hOuterPt := ConcreteCategory.congr_hom hOuterApp x0
  change (StrictOrdinaryWeightedBar.wbarσ
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i).app
        (op (SimplexCategory.mk (n + 1)))
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op (SimplexCategory.mk (n + 1))) x0) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
        (StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i p)).app
      (op (SimplexCategory.mk (n + 1)))
        ((StrictOrdinaryWeightedBar.wDegInnerComponent
          (quillenAMappingDiagram F) i p.1).app
            (op (SimplexCategory.mk (n + 1))) x0) at hOuterPt
  dsimp only [p0, c0, p, quillenAMappingIndex,
    quillenAMappingCarrierDegInner]
  exact hOuterPt

private def quillenABridgeComponent
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) (i : Fin (n + 1)) :
    G.obj i ⟶ F.obj (H.obj i) :=
  G.map' i.val n ≫ theta ≫ F.map (H.map' 0 i.val)

private def quillenAInnerTargetData
    {D : Type u} [Category.{v} D] (d : D) :
    CategoryBar.categoryBarData
        (R := CategoryBar.commaCoeffR (𝟭 D) d)
        (L := CategoryBar.unitCoeffL D) ⟶
      nerveData D where
  app _ := ↾fun x => CategoryBar.barChain x
  w_δ {n} i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · ext x
      change CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) d)
        (CategoryBar.unitCoeffL D) (n + 1) at x
      change (nerve D).δ 0 (CategoryBar.barChain x) =
        CategoryBar.barChain (CategoryBar.barδ 0 x)
      rw [CategoryBar.barδ_zero_eq]
      rcases x with ⟨F, l, r⟩
      rfl
    · refine Fin.lastCases ?_ (fun q => ?_) j
      · ext x
        change CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) d)
          (CategoryBar.unitCoeffL D) (n + 1) at x
        change (nerve D).δ (Fin.last (n + 1))
            (CategoryBar.barChain x) =
          CategoryBar.barChain
            (CategoryBar.barδ (Fin.last (n + 1)) x)
        rw [CategoryBar.barδ_last_eq]
        rcases x with ⟨F, l, r⟩
        rfl
      · ext x
        change CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) d)
          (CategoryBar.unitCoeffL D) (n + 1) at x
        change (nerve D).δ q.castSucc.succ
            (CategoryBar.barChain x) =
          CategoryBar.barChain
            (CategoryBar.barδ q.castSucc.succ x)
        rw [CategoryBar.barδ_castSucc_succ_eq]
        rcases x with ⟨F, l, r⟩
        rfl
  w_σ i := by
    ext x
    change (nerve D).σ i (CategoryBar.barChain x) =
      CategoryBar.barChain (CategoryBar.barσ i x)
    rfl

private noncomputable def quillenAInnerTarget
    {D : Type u} [Category.{v} D] (d : D) :
    CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) d)
        (L := CategoryBar.unitCoeffL D) ⟶
      nerve D :=
  by
    let t := SimplicialObject.Data.toSimplicialNatTrans
      (quillenAInnerTargetData d)
    change CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) d)
        (L := CategoryBar.unitCoeffL D) ⟶
      (nerveData D).toSimplicialObject at t
    exact t ≫ (nerveDataSimplicialIso D).hom

@[simp]
private theorem quillenAInnerTarget_app
    {D : Type u} [Category.{v} D] (d : D) (n : ℕ) :
    (quillenAInnerTarget d).app (op ⦋n⦌) =
      ↾fun x => CategoryBar.barChain x := by
  change (SimplicialObject.Data.toSimplicialNatTrans
      (quillenAInnerTargetData d) ≫
        (nerveDataSimplicialIso D).hom).app (op ⦋n⦌) = _
  simp only [NatTrans.comp_app,
    SimplicialObject.Data.toSimplicialNatTrans_app_mk,
    nerveDataSimplicialIso_hom_app]
  rfl

private noncomputable def quillenAMappingTargetCocone
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    quillenAMappingDiagram F ⟶ (Functor.const C).obj (nerve D) where
  app c := quillenAInnerTarget (F.obj c)
  naturality {c c'} a := by
    ext n x
    change (CategoryBar.barChain
      (CategoryBar.barCoeffMap
        (CategoryBar.commaCoeffRMap (𝟭 D) (F.map a))
        (𝟙 (CategoryBar.unitCoeffL D)) x)) =
      CategoryBar.barChain x
    induction n using Opposite.rec with
    | _ n =>
      induction n using SimplexCategory.rec with
      | _ n =>
        change CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) (F.obj c))
          (CategoryBar.unitCoeffL D) n at x
        rcases x with ⟨G, l, r⟩
        rfl

private theorem quillenASrepFaceZeroComponent_comp_cocone
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    (τ : E ⟶ (Functor.const J).obj Z) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceZeroComponent E s ≫
        τ.app (SrepBridge.srepDropFirst s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropFirst s).left :=
    eqToHom (SrepBridge.srepLeftZero s) ≫ s.map' 0 1 ≫
      eqToHom (SrepBridge.srepDropFirst_left s).symm
  have hcomp : SrepBridge.srepFaceZeroComponent E s = E.map a := by
    simp only [SrepBridge.srepFaceZeroComponent, a, Functor.map_comp,
      eqToHom_map]
  rw [hcomp]
  calc
    E.map a ≫ τ.app (SrepBridge.srepDropFirst s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      exact Category.comp_id _

private theorem quillenASrepFaceLastComponent_comp_cocone
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    (τ : E ⟶ (Functor.const J).obj Z) {n : ℕ}
    (s : SrepBridge.SrepIdx J (n + 1)) :
    SrepBridge.srepFaceLastComponent E s ≫
        τ.app (SrepBridge.srepDropLast s).left =
      τ.app s.left := by
  let a : s.left ⟶ (SrepBridge.srepDropLast s).left :=
    eqToHom (SrepBridge.srepDropLast_left s).symm
  have hcomp : SrepBridge.srepFaceLastComponent E s = E.map a := by
    simp only [SrepBridge.srepFaceLastComponent, a, eqToHom_map]
  rw [hcomp]
  calc
    E.map a ≫ τ.app (SrepBridge.srepDropLast s).left =
        τ.app s.left ≫ ((Functor.const J).obj Z).map a := τ.naturality a
    _ = τ.app s.left := by
      rw [Functor.const_obj_map]
      exact Category.comp_id _

private noncomputable def quillenAWbarAugmentationZero
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) E 0 ⟶ Z :=
  StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) E 0
    (fun p => τ.app p.1.left)

private theorem quillenAWbarAugmentationZero_isBalanced
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) :
    SimplicialObject.Data.IsBalanced
      (X := StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) E)
      (quillenAWbarAugmentationZero τ) := by
  refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
  let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit J) 0 p
  let p1 := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit J) 0 p
  have hzero :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) E 0 0) ≫
            quillenAWbarAugmentationZero τ =
        τ.app p.1.left := by
    have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
      (CategoryBar.replUnit J) E 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) E 0 (fun p => τ.app p.1.left) p0
    calc
      _ = (SrepBridge.srepFaceZeroComponent E p.1 ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E 0 p0) ≫
              quillenAWbarAugmentationZero τ := by
          apply congrArg (fun z => z ≫ quillenAWbarAugmentationZero τ)
          rw [StrictOrdinaryWeightedBar.wbarδ_zero]
          exact hface
      _ = SrepBridge.srepFaceZeroComponent E p.1 ≫
            (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E 0 p0 ≫
              quillenAWbarAugmentationZero τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceZeroComponent E p.1 ≫ τ.app p0.1.left :=
        congrArg (fun z => SrepBridge.srepFaceZeroComponent E p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
        change SrepBridge.srepFaceZeroComponent E p.1 ≫
          τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
        exact quillenASrepFaceZeroComponent_comp_cocone τ p.1
  have hone :
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E 1 p ≫
          StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) E 0 1) ≫
            quillenAWbarAugmentationZero τ =
        τ.app p.1.left := by
    have hlast : (1 : Fin 2) = Fin.last 1 := rfl
    have hface := StrictOrdinaryWeightedBar.wbarFaceLast_ι
      (CategoryBar.replUnit J) E 0 p
    have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) E 0 (fun p => τ.app p.1.left) p1
    calc
      _ = (SrepBridge.srepFaceLastComponent E p.1 ≫
          StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E 0 p1) ≫
            quillenAWbarAugmentationZero τ := by
          apply congrArg (fun z => z ≫ quillenAWbarAugmentationZero τ)
          rw [hlast, StrictOrdinaryWeightedBar.wbarδ_last]
          exact hface
      _ = SrepBridge.srepFaceLastComponent E p.1 ≫
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E 0 p1 ≫
            quillenAWbarAugmentationZero τ) := Category.assoc _ _ _
      _ = SrepBridge.srepFaceLastComponent E p.1 ≫ τ.app p1.1.left :=
        congrArg (fun z => SrepBridge.srepFaceLastComponent E p.1 ≫ z) hdesc
      _ = τ.app p.1.left := by
        change SrepBridge.srepFaceLastComponent E p.1 ≫
          τ.app (SrepBridge.srepDropLast p.1).left = τ.app p.1.left
        exact quillenASrepFaceLastComponent_comp_cocone τ p.1
  exact hzero.trans hone.symm

private noncomputable def quillenAWbarAugmentationData
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) E ⟶
      SimplicialObject.Data.constData Z :=
  SimplicialObject.Data.balancedHom
    (quillenAWbarAugmentationZero_isBalanced τ)

private theorem quillenAWbarAugmentationData_app
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (quillenAWbarAugmentationData τ).app n =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) E n
        (fun p => τ.app p.1.left) := by
  induction n with
  | zero =>
      change (quillenAWbarAugmentationData τ).app 0 =
        quillenAWbarAugmentationZero τ
      unfold quillenAWbarAugmentationData
      exact SimplicialObject.Data.balancedHom_app_zero
        (quillenAWbarAugmentationZero_isBalanced τ)
  | succ n ih =>
      have hs : (quillenAWbarAugmentationData τ).app (n + 1) =
          StrictOrdinaryWeightedBar.wbarδ
            (CategoryBar.replUnit J) E n 0 ≫
            (quillenAWbarAugmentationData τ).app n := rfl
      rw [hs, ih]
      refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
      let p0 := StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit J) n p
      have hface := StrictOrdinaryWeightedBar.wbarFaceZero_ι
        (CategoryBar.replUnit J) E n p
      have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) E n (fun p => τ.app p.1.left) p0
      have hdescTop := StrictOrdinaryWeightedBar.wbarDesc_ι
        (CategoryBar.replUnit J) E (n + 1) (fun p => τ.app p.1.left) p
      calc
        _ = (StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarδ
                (CategoryBar.replUnit J) E n 0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) E n
                  (fun p => τ.app p.1.left) :=
            (Category.assoc _ _ _).symm
        _ = (SrepBridge.srepFaceZeroComponent E p.1 ≫
              StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) E n p0) ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) E n
                  (fun p => τ.app p.1.left) := by
            apply congrArg (fun z => z ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) E n
                  (fun p => τ.app p.1.left))
            rw [StrictOrdinaryWeightedBar.wbarδ_zero]
            exact hface
        _ = SrepBridge.srepFaceZeroComponent E p.1 ≫
              (StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) E n p0 ≫
                StrictOrdinaryWeightedBar.wbarDesc
                  (CategoryBar.replUnit J) E n
                    (fun p => τ.app p.1.left)) := Category.assoc _ _ _
        _ = SrepBridge.srepFaceZeroComponent E p.1 ≫ τ.app p0.1.left :=
          congrArg (fun z => SrepBridge.srepFaceZeroComponent E p.1 ≫ z) hdesc
        _ = τ.app p.1.left := by
          change SrepBridge.srepFaceZeroComponent E p.1 ≫
            τ.app (SrepBridge.srepDropFirst p.1).left = τ.app p.1.left
          exact quillenASrepFaceZeroComponent_comp_cocone τ p.1
        _ = StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E (n + 1) p ≫
              StrictOrdinaryWeightedBar.wbarDesc
                (CategoryBar.replUnit J) E (n + 1)
                  (fun p => τ.app p.1.left) := hdescTop.symm

private noncomputable def quillenAWbarAugmentation
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) :
    StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) E ⟶
      (SimplicialObject.const SSet.{w}).obj Z :=
  SimplicialObject.Data.toSimplicialFunctor.map
      (quillenAWbarAugmentationData τ) ≫
    (SimplicialObject.Data.constDataIso Z).hom

@[simp]
private theorem quillenAWbarAugmentation_app_mk
    {J : Type u} [Category.{v} J] {E : J ⥤ SSet.{w}} {Z : SSet.{w}}
    [∀ n, Limits.HasCoproduct (fun p :
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n =>
        E.obj p.1.left)]
    (τ : E ⟶ (Functor.const J).obj Z) (n : ℕ) :
    (quillenAWbarAugmentation τ).app (op ⦋n⦌) =
      StrictOrdinaryWeightedBar.wbarDesc (CategoryBar.replUnit J) E n
        (fun p => τ.app p.1.left) := by
  unfold quillenAWbarAugmentation StrictOrdinaryWeightedBar.wbarSimplicial
  change (SimplicialObject.Data.toSimplicialFunctor.map
      (quillenAWbarAugmentationData τ)).app (op ⦋n⦌) ≫
      (SimplicialObject.Data.constDataIso Z).hom.app (op ⦋n⦌) = _
  rw [SimplicialObject.Data.toSimplicialFunctor_map_app_mk,
    SimplicialObject.Data.constDataIso_hom_app_mk]
  exact (Category.comp_id ((quillenAWbarAugmentationData τ).app n)).trans
    (quillenAWbarAugmentationData_app τ n)

private noncomputable def quillenADiagonalConstIso (Z : SSet.{w}) :
    SSet.simplicialDiagonalFunctor.obj
      ((SimplicialObject.const SSet.{w}).obj Z) ≅ Z :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b k
    rfl)

private noncomputable def quillenATarget
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : quillenAMappingCarrier F ⟶ nerve D :=
  SSet.simplicialDiagonalFunctor.map
      (quillenAWbarAugmentation (quillenAMappingTargetCocone F)) ≫
    (quillenADiagonalConstIso (nerve D)).hom

@[simp]
private theorem quillenATarget_carrierIncl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    (quillenATarget F).app (op ⦋n⦌)
      (quillenAMappingCarrierIncl F n H G theta) = G := by
  change ((quillenAWbarAugmentation
      (quillenAMappingTargetCocone F)).app (op ⦋n⦌)).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (⟨H, PUnit.unit⟩ :
          StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n)).app (op ⦋n⦌)
          (⟨G, ULift.up PUnit.unit, theta⟩ :
            CategoryBar.barObj D
              (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
              (CategoryBar.unitCoeffL D) n)) = G
  rw [quillenAWbarAugmentation_app_mk]
  have hdesc := StrictOrdinaryWeightedBar.wbarDesc_ι
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
    (fun p => (quillenAMappingTargetCocone F).app p.1.left)
    (⟨H, PUnit.unit⟩ :
      StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
  have happ := NatTrans.congr_app hdesc (op ⦋n⦌)
  have hpt := ConcreteCategory.congr_hom happ
    (⟨G, ULift.up PUnit.unit, theta⟩ :
      CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
        (CategoryBar.unitCoeffL D) n)
  change (StrictOrdinaryWeightedBar.wbarDesc
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
      (fun p => (quillenAMappingTargetCocone F).app p.1.left)).app
        (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
          (⟨H, PUnit.unit⟩ :
            StrictOrdinaryWeightedBar.WIdx C
              (CategoryBar.replUnit C) n)).app (op ⦋n⦌)
            (⟨G, ULift.up PUnit.unit, theta⟩ :
              CategoryBar.barObj D
                (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
                (CategoryBar.unitCoeffL D) n)) =
      (quillenAInnerTarget (F.obj H.left)).app (op ⦋n⦌)
        (⟨G, ULift.up PUnit.unit, theta⟩ :
          CategoryBar.barObj D
            (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
            (CategoryBar.unitCoeffL D) n) at hpt
  refine hpt.trans ?_
  change (quillenAInnerTarget (F.obj H.left)).app (op ⦋n⦌)
    (⟨G, ULift.up PUnit.unit, theta⟩ :
      CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
        (CategoryBar.unitCoeffL D) n) = G
  rw [quillenAInnerTarget_app]
  rfl

private theorem quillenATarget_apply
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    (quillenATarget F).app (op ⦋n⦌) z =
      (quillenAMappingCarrierObjEquiv F n z).2.1 := by
  rcases h : quillenAMappingCarrierObjEquiv F n z with
    ⟨H, G, theta⟩
  have hz : z = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [h, quillenAMappingCarrierObjEquiv_incl]
  subst z
  simpa only [quillenAMappingCarrierObjEquiv_incl] using
    quillenATarget_carrierIncl F n H G theta

private theorem quillenATarget_eq_raw_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    (quillenATarget F).app (op ⦋n⦌) z =
      CategoryBar.barChain (quillenAMappingCarrierRawEquiv F n z).2 := by
  rw [quillenATarget_apply]
  rfl

private abbrev quillenADiscreteSSet : Type w ⥤ SSet.{w} :=
  Functor.const SimplexCategoryᵒᵖ

private abbrev quillenASourceTargetData
    (C : Type u) [Category.{v} C] : SimplicialObject.Data SSet.{max u v} where
  obj n := quillenADiscreteSSet.obj ((nerve C).obj (op ⦋n⦌))
  δ i := quillenADiscreteSSet.map ((nerve C).δ i)
  σ i := quillenADiscreteSSet.map ((nerve C).σ i)
  δ_comp_δ {n} {i j} h := by
    simpa only [← Functor.map_comp] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).δ_comp_δ h)
  δ_comp_σ_of_le {n} {i j} h := by
    simpa only [← Functor.map_comp] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).δ_comp_σ_of_le h)
  δ_comp_σ_self {n} {i} := by
    simpa only [← Functor.map_comp, Functor.map_id] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).δ_comp_σ_self (i := i))
  δ_comp_σ_succ {n} {i} := by
    simpa only [← Functor.map_comp, Functor.map_id] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).δ_comp_σ_succ (i := i))
  δ_comp_σ_of_gt {n} {i j} h := by
    simpa only [← Functor.map_comp] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).δ_comp_σ_of_gt h)
  σ_comp_σ {n} {i j} h := by
    simpa only [← Functor.map_comp] using
      congrArg (fun k => quillenADiscreteSSet.map k)
        ((nerve C).σ_comp_σ h)

private def quillenASourceConst
    (X : SSet.{max u v}) (C : Type u) [Category.{v} C] (n : ℕ)
    (H : (nerve C).obj (op ⦋n⦌)) :
    X ⟶ (quillenASourceTargetData C).obj n :=
  SSet.const H

private theorem quillenASourceConst_δ
    (X : SSet.{max u v}) (C : Type u) [Category.{v} C]
    {n : ℕ} (H : (nerve C).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    quillenASourceConst X C (n + 1) H ≫
        (quillenASourceTargetData C).δ i =
      quillenASourceConst X C n ((nerve C).δ i H) := by
  change SSet.const (X := X)
      (Y := (quillenASourceTargetData C).obj (n + 1)) H ≫
        (quillenASourceTargetData C).δ i =
    SSet.const (X := X) (Y := (quillenASourceTargetData C).obj n)
      ((nerve C).δ i H)
  rw [SSet.const_comp]
  rfl

private theorem quillenASourceConst_σ
    (X : SSet.{max u v}) (C : Type u) [Category.{v} C]
    {n : ℕ} (H : (nerve C).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    quillenASourceConst X C n H ≫
        (quillenASourceTargetData C).σ i =
      quillenASourceConst X C (n + 1) ((nerve C).σ i H) := by
  change SSet.const (X := X)
      (Y := (quillenASourceTargetData C).obj n) H ≫
        (quillenASourceTargetData C).σ i =
    SSet.const (X := X) (Y := (quillenASourceTargetData C).obj (n + 1))
      ((nerve C).σ i H)
  rw [SSet.const_comp]
  rfl

private theorem quillenAComp_sourceConst
    {C : Type u} [Category.{v} C]
    {X Y : SSet.{max u v}} (f : X ⟶ Y) {n : ℕ}
    (H : (nerve C).obj (op ⦋n⦌)) :
    f ≫ quillenASourceConst Y C n H =
      quillenASourceConst X C n H := by
  change f ≫ SSet.const (X := Y)
      (Y := (quillenASourceTargetData C).obj n) H =
    SSet.const (X := X) (Y := (quillenASourceTargetData C).obj n) H
  exact SSet.comp_const (X := X) (Y := Y)
    (Z := (quillenASourceTargetData C).obj n) f H

private def quillenAChainAsNerve
    (C : Type u) [Category.{v} C] {n : ℕ}
    (H : ComposableArrows C n) : (nerve C).obj (op ⦋n⦌) :=
  H

@[reassoc]
private theorem quillenASourceDesc_ι
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n) :
    StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p ≫
      StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (fun q => quillenASourceConst
          ((quillenAMappingDiagram F).obj q.1.left) C n
            (quillenAChainAsNerve C q.1)) =
      quillenASourceConst
        ((quillenAMappingDiagram F).obj p.1.left) C n
          (quillenAChainAsNerve C p.1) :=
  StrictOrdinaryWeightedBar.wbarDesc_ι _ _ _ _ _

private noncomputable def quillenASourceData
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    StrictOrdinaryWeightedBar.wbarData
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) ⟶
      quillenASourceTargetData C where
  app n := StrictOrdinaryWeightedBar.wbarDesc
    (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
    (fun p => quillenASourceConst
      ((quillenAMappingDiagram F).obj p.1.left) C n
        (quillenAChainAsNerve C p.1))
  w_δ {n} i := by
    change (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
        (fun p => quillenASourceConst
          ((quillenAMappingDiagram F).obj p.1.left) C (n + 1)
            (quillenAChainAsNerve C p.1))) ≫
          (quillenASourceTargetData C).δ i =
      StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i ≫
        StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
          (fun p => quillenASourceConst
            ((quillenAMappingDiagram F).obj p.1.left) C n
              (quillenAChainAsNerve C p.1))
    refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
    change StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1) p ≫
          (StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
            (fun q => quillenASourceConst
              ((quillenAMappingDiagram F).obj q.1.left) C (n + 1)
                (quillenAChainAsNerve C q.1)) ≫
            (quillenASourceTargetData C).δ i) =
      StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1) p ≫
          (StrictOrdinaryWeightedBar.wbarδ
            (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
              (fun q => quillenASourceConst
                ((quillenAMappingDiagram F).obj q.1.left) C n
                  (quillenAChainAsNerve C q.1)))
    rw [← Category.assoc,
      quillenASourceDesc_ι,
      quillenASourceConst_δ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← Category.assoc,
        StrictOrdinaryWeightedBar.wbarδ_zero,
        StrictOrdinaryWeightedBar.wbarFaceZero_ι]
      unfold StrictOrdinaryWeightedBar.wFaceZeroIdx
      rw [Category.assoc, quillenASourceDesc_ι,
        quillenAComp_sourceConst]
      rfl
    · refine Fin.lastCases ?_ (fun q => ?_) j
      · rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl]
        rw [← Category.assoc,
          StrictOrdinaryWeightedBar.wbarδ_last,
          StrictOrdinaryWeightedBar.wbarFaceLast_ι]
        unfold StrictOrdinaryWeightedBar.wFaceLastIdx
        rw [Category.assoc, quillenASourceDesc_ι,
          quillenAComp_sourceConst]
        apply congrArg (fun K => quillenASourceConst
          ((quillenAMappingDiagram F).obj p.1.left) C n K)
        change (nerve C).δ (Fin.last (n + 1)) p.1 =
          SrepBridge.srepDropLast p.1
        have hidx :
            (SimplexCategory.δ
              (Fin.last (n + 1))).toOrderHom.toFunctor =
              Fin.castSuccFunctor (n + 1) := by
          refine Functor.ext (fun k => Fin.succAbove_last_apply k) ?_
          intro a b f
          apply Subsingleton.elim
        change p.1.whiskerLeft
            (SimplexCategory.δ
              (Fin.last (n + 1))).toOrderHom.toFunctor =
          p.1.whiskerLeft (Fin.castSuccFunctor (n + 1))
        rw [hidx]
      · have h0 : q.castSucc.succ ≠ (0 : Fin (n + 2)) := by simp
        have hlast : q.castSucc.succ ≠ Fin.last (n + 1) := by
          apply ne_of_apply_ne Fin.val
          rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
          omega
        rw [← Category.assoc,
          StrictOrdinaryWeightedBar.wbarδ_inner _ _ _
            (i := q.castSucc.succ) h0 hlast,
          StrictOrdinaryWeightedBar.wbarFaceInner_ι]
        unfold StrictOrdinaryWeightedBar.wFaceInnerIdx
        rw [Category.assoc, quillenASourceDesc_ι,
          quillenAComp_sourceConst]
        rfl
  w_σ {n} i := by
    change (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (fun p => quillenASourceConst
          ((quillenAMappingDiagram F).obj p.1.left) C n
            (quillenAChainAsNerve C p.1))) ≫
          (quillenASourceTargetData C).σ i =
      StrictOrdinaryWeightedBar.wbarσ
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i ≫
        StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
          (fun p => quillenASourceConst
            ((quillenAMappingDiagram F).obj p.1.left) C (n + 1)
              (quillenAChainAsNerve C p.1))
    refine Limits.Sigma.hom_ext _ _ (fun p => ?_)
    change StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p ≫
          (StrictOrdinaryWeightedBar.wbarDesc
            (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
            (fun q => quillenASourceConst
              ((quillenAMappingDiagram F).obj q.1.left) C n
                (quillenAChainAsNerve C q.1)) ≫
            (quillenASourceTargetData C).σ i) =
      StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p ≫
          (StrictOrdinaryWeightedBar.wbarσ
            (CategoryBar.replUnit C) (quillenAMappingDiagram F) n i ≫
            StrictOrdinaryWeightedBar.wbarDesc
              (CategoryBar.replUnit C) (quillenAMappingDiagram F) (n + 1)
              (fun q => quillenASourceConst
                ((quillenAMappingDiagram F).obj q.1.left) C (n + 1)
                  (quillenAChainAsNerve C q.1)))
    rw [← Category.assoc,
      quillenASourceDesc_ι,
      quillenASourceConst_σ]
    rw [← Category.assoc,
      StrictOrdinaryWeightedBar.wbarσ_ι]
    unfold StrictOrdinaryWeightedBar.wDegInnerIdx
    rw [Category.assoc, quillenASourceDesc_ι,
      quillenAComp_sourceConst]
    rfl

private noncomputable def quillenASourceBisimplicialMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    quillenAMappingBisimplicial F ⟶
      (quillenASourceTargetData C).toSimplicialObject := by
  change (StrictOrdinaryWeightedBar.wbarData
      (CategoryBar.replUnit C) (quillenAMappingDiagram F)).toSimplicialObject ⟶
    (quillenASourceTargetData C).toSimplicialObject
  exact SimplicialObject.Data.toSimplicialNatTrans (quillenASourceData F)

private noncomputable def quillenASourceTargetIso
    (C : Type u) [Category.{v} C] :
    (quillenASourceTargetData C).toSimplicialObject ≅
      ((SimplicialObject.whiskering (Type (max u v)) SSet.{max u v}).obj
        quillenADiscreteSSet).obj ((nerveData C).toSimplicialObject) := by
  change (SimplicialObject.Data.mapObj quillenADiscreteSSet
      (nerveData C)).toSimplicialObject ≅ _
  exact (SimplicialObject.Data.toSimplicialObject_mapObjIso
    quillenADiscreteSSet (nerveData C)).symm

private noncomputable def quillenADiscreteDiagonalIso
    (K : SimplicialObject (Type w)) :
    SSet.simplicialDiagonalFunctor.obj
      (((SimplicialObject.whiskering (Type w) SSet.{w}).obj
        quillenADiscreteSSet).obj K) ≅ K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b k
    rfl)

private noncomputable def quillenASourceDiagonalIso
    (C : Type u) [Category.{v} C] :
    SSet.simplicialDiagonalFunctor.obj
        (quillenASourceTargetData C).toSimplicialObject ≅ nerve C :=
  (SSet.simplicialDiagonalFunctor.mapIso
      (quillenASourceTargetIso C)).trans
    ((quillenADiscreteDiagonalIso (nerveData C).toSimplicialObject).trans
      (nerveDataSimplicialIso C))

private noncomputable def quillenASource
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : quillenAMappingCarrier F ⟶ nerve C :=
  SSet.simplicialDiagonalFunctor.map (quillenASourceBisimplicialMap F) ≫
    (quillenASourceDiagonalIso C).hom

@[simp]
private theorem quillenASource_carrierIncl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    (quillenASource F).app (op ⦋n⦌)
      (quillenAMappingCarrierIncl F n H G theta) = H := by
  change ((quillenASourceData F).app n).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (⟨H, PUnit.unit⟩ :
          StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n)).app (op ⦋n⦌)
          (⟨G, ULift.up PUnit.unit, theta⟩ :
            CategoryBar.barObj D
              (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
              (CategoryBar.unitCoeffL D) n)) = H
  change (StrictOrdinaryWeightedBar.wbarDesc
      (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
      (fun q => quillenASourceConst
        ((quillenAMappingDiagram F).obj q.1.left) C n
          (quillenAChainAsNerve C q.1))).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n
        (⟨H, PUnit.unit⟩ :
          StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n)).app (op ⦋n⦌)
          (⟨G, ULift.up PUnit.unit, theta⟩ :
            CategoryBar.barObj D
              (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
              (CategoryBar.unitCoeffL D) n)) = H
  have hdesc := quillenASourceDesc_ι F n
    (⟨H, PUnit.unit⟩ :
      StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
  have happ := NatTrans.congr_app hdesc (op ⦋n⦌)
  have hpt := ConcreteCategory.congr_hom happ
    (⟨G, ULift.up PUnit.unit, theta⟩ :
      CategoryBar.barObj D
        (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
        (CategoryBar.unitCoeffL D) n)
  refine hpt.trans ?_
  rfl

private theorem quillenASource_apply
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    (quillenASource F).app (op ⦋n⦌) z =
      (quillenAMappingCarrierObjEquiv F n z).1 := by
  rcases h : quillenAMappingCarrierObjEquiv F n z with
    ⟨H, G, theta⟩
  have hz : z = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [h, quillenAMappingCarrierObjEquiv_incl]
  subst z
  simpa only [quillenAMappingCarrierObjEquiv_incl] using
    quillenASource_carrierIncl F n H G theta

private theorem quillenASource_eq_raw_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    (quillenASource F).app (op ⦋n⦌) z =
      (quillenAMappingCarrierRawEquiv F n z).1.1 := by
  rw [quillenASource_apply]
  rfl

private noncomputable def quillenATargetFiberRetractionFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y) :
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌) := by
  let p := r.1
  let x := r.2
  let G := CategoryBar.barChain x
  let theta := CategoryBar.barCoeffR x
  have hMapRight : ((nerve D).map alpha.op y).right =
      y.obj (alpha.toOrderHom (Fin.last n)) := rfl
  have hRight : G.right =
      y.obj (alpha.toOrderHom (Fin.last n)) :=
    (congrArg (fun K : ComposableArrows D n ↦ K.right) hG).trans
      hMapRight
  refine ⟨p.1, ?_, p.2⟩
  change y.obj 0 ⟶ F.obj p.1.left
  exact y.map
      (homOfLE (Fin.zero_le (alpha.toOrderHom (Fin.last n)))) ≫
    eqToHom hRight.symm ≫ theta

private theorem quillenATargetFiberRetractionFromRaw_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    {alpha alpha' : SimplexCategory.mk n ⟶ SimplexCategory.mk m}
    {r r' : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)}
    (ha : alpha = alpha') (hr : r = r')
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y)
    (hG' : CategoryBar.barChain r'.2 = (nerve D).map alpha'.op y) :
    quillenATargetFiberRetractionFromRaw F y n alpha r hG =
      quillenATargetFiberRetractionFromRaw F y n alpha' r' hG' := by
  cases ha
  cases hr
  rfl

private noncomputable def quillenATargetFiberRetractionDecoded
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y}) :
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌) := by
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  have hTarget : (quillenATarget F).app (op ⦋n⦌) d.1.1 =
      CategoryBar.barChain r.2 :=
    quillenATarget_eq_raw_chain F n d.1.1
  have hG : CategoryBar.barChain r.2 = (nerve D).map d.1.2.op y :=
    hTarget.symm.trans d.2
  exact quillenATargetFiberRetractionFromRaw F y n d.1.2 r hG

private noncomputable def quillenATargetFiberRetractionAppRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌) :=
  quillenATargetFiberRetractionDecoded F y n
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌) z)

private def quillenATargetFiberFirstVertexMap (m n : ℕ) :
    SimplexCategory.mk n ⟶ SimplexCategory.mk m :=
  SimplexCategory.const (SimplexCategory.mk n)
    (SimplexCategory.mk m) 0

private noncomputable def quillenATargetFiberSectionApp
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌)) :
    (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌) := by
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) n at z
  let H := z.1
  let phi := z.2.1
  let alpha := quillenATargetFiberFirstVertexMap m n
  let G : ComposableArrows D n := (nerve D).map alpha.op y
  have hRight : G.right = y.obj 0 := rfl
  let theta : G.right ⟶ F.obj H.left := eqToHom hRight ≫ phi
  exact (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).symm
      ⟨⟨quillenAMappingCarrierIncl F n H G theta, alpha⟩, by
        rw [quillenATarget_carrierIncl]⟩

private noncomputable def quillenATargetFiberDecodedMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (d : {p : (quillenAMappingCarrier F).obj a ×
        (a.unop ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app a p.1 = (nerve D).map p.2.op y}) :
    {p : (quillenAMappingCarrier F).obj b ×
        (b.unop ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app b p.1 = (nerve D).map p.2.op y} :=
  ⟨⟨(quillenAMappingCarrier F).map k d.1.1,
      k.unop ≫ d.1.2⟩, by
    calc
      (quillenATarget F).app b
          ((quillenAMappingCarrier F).map k d.1.1) =
          (nerve D).map k ((quillenATarget F).app a d.1.1) := by
        exact ConcreteCategory.congr_hom
          ((quillenATarget F).naturality k) d.1.1
      _ = (nerve D).map k ((nerve D).map d.1.2.op y) := by
        rw [d.2]
      _ = (nerve D).map (k.unop ≫ d.1.2).op y := by
        have h := ConcreteCategory.congr_hom
          ((nerve D).map_comp d.1.2.op k) y
        exact h.symm⟩

private theorem quillenATargetFiberDecodedMap_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (z : (SSet.leftFiber (quillenATarget F) y).obj a) :
    quillenATargetFiberDecodedMap F y k
        (SSet.leftFiber.objEquiv (quillenATarget F) y a z) =
      SSet.leftFiber.objEquiv (quillenATarget F) y b
        ((SSet.leftFiber (quillenATarget F) y).map k z) := by
  rw [SSet.leftFiber.objEquiv_map]
  apply Subtype.ext
  rfl

private noncomputable def quillenASourceFiberRetractionFromTriple
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (T : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hH : T.1 = x.whiskerLeft alpha.toOrderHom.toFunctor) :
    Σ G : ComposableArrows D n,
      ULift.{0} PUnit × (G.right ⟶ F.obj x.right) :=
  let k : T.1.left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH) ≫
      x.map' (alpha.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
  ⟨T.2.1, ULift.up PUnit.unit, T.2.2 ≫ F.map k⟩

private theorem quillenAConstLast_whisker_left
    {C : Type u} [Category.{v} C] {m : ℕ}
    (x : ComposableArrows C m) (n : ℕ) :
    (x.whiskerLeft
      (SimplexCategory.const ⦋n⦌ ⦋m⦌
        (Fin.last m)).toOrderHom.toFunctor).left = x.right := by
  change x.obj ((SimplexCategory.const ⦋n⦌ ⦋m⦌
    (Fin.last m)).toOrderHom 0) = x.obj (Fin.last m)
  exact congrArg x.obj
    (SimplexCategory.const_apply ⦋n⦌ ⦋m⦌ (Fin.last m) 0)

private theorem quillenASourceFiberRetractionFromTriple_constLast_aux
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (G : ComposableArrows D n) (theta : G.right ⟶ F.obj x.right)
    (H : ComposableArrows C n)
    (hH : H = x.whiskerLeft
      (SimplexCategory.const ⦋n⦌ ⦋m⦌
        (Fin.last m)).toOrderHom.toFunctor)
    (hleft : H.left = x.right) :
    quillenASourceFiberRetractionFromTriple F x
      ⟨H, G, theta ≫ F.map (eqToHom hleft.symm)⟩
      (SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)) hH =
        ⟨G, ULift.up PUnit.unit, theta⟩ := by
  unfold quillenASourceFiberRetractionFromTriple
  change (⟨G, (ULift.up PUnit.unit, _)⟩ :
      Σ G : ComposableArrows D n,
        ULift.{0} PUnit × (G.right ⟶ F.obj x.right)) =
    (⟨G, (ULift.up PUnit.unit, theta)⟩ :
      Σ G : ComposableArrows D n,
        ULift.{0} PUnit × (G.right ⟶ F.obj x.right))
  congr 2
  have hconst :
      (x.whiskerLeft
        (SimplexCategory.const ⦋n⦌ ⦋m⦌
          (Fin.last m)).toOrderHom.toFunctor).left = x.right :=
    quillenAConstLast_whisker_left x n
  have hxmap : x.map'
      ((SimplexCategory.const ⦋n⦌ ⦋m⦌
        (Fin.last m)).toOrderHom 0).val m
        (Nat.le_of_lt_succ
          ((SimplexCategory.const ⦋n⦌ ⦋m⦌
            (Fin.last m)).toOrderHom 0).isLt) le_rfl =
      eqToHom hconst := by
    simp only [SimplexCategory.const_apply, Fin.val_last]
    rw [x.map'_self m (hi := le_rfl)]
    congr
  rw [hxmap, eqToHom_trans]
  have hpath : (congrArg ComposableArrows.left hH).trans hconst = hleft :=
    Subsingleton.elim _ _
  rw [hpath, Category.assoc, ← F.map_comp, eqToHom_trans]
  simp

private theorem quillenASourceFiberRetractionFromTriple_constLast
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (G : ComposableArrows D n) (theta : G.right ⟶ F.obj x.right) :
    let alpha : ⦋n⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
    let H : ComposableArrows C n :=
      x.whiskerLeft alpha.toOrderHom.toFunctor
    let hleft : H.left = x.right :=
      quillenAConstLast_whisker_left x n
    let theta' : G.right ⟶ F.obj H.left :=
      theta ≫ F.map (eqToHom hleft.symm)
    quillenASourceFiberRetractionFromTriple F x
      ⟨H, G, theta'⟩ alpha rfl =
        ⟨G, ULift.up PUnit.unit, theta⟩ := by
  apply quillenASourceFiberRetractionFromTriple_constLast_aux
  exact quillenAConstLast_whisker_left x n

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromTriple_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH0 : SrepBridge.srepDropFirst H = x.whiskerLeft
      (SimplexCategory.δ (0 : Fin (n + 2)) ≫
        alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromTriple F x
        ⟨SrepBridge.srepDropFirst H, SrepBridge.srepDropFirst G,
          theta ≫ F.map (H.map' 0 1)⟩
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha) hH0 =
      ⟨SrepBridge.srepDropFirst G, ULift.up PUnit.unit,
        (quillenASourceFiberRetractionFromTriple F x
          ⟨H, G, theta⟩ alpha hH).2.2⟩ := by
  unfold quillenASourceFiberRetractionFromTriple
  dsimp only
  congr 2
  let alpha0 := SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha
  let k0 : (SrepBridge.srepDropFirst H).left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH0) ≫
      x.map' (alpha0.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha0.toOrderHom 0).isLt) le_rfl
  let k : H.left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH) ≫
      x.map' (alpha.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
  change (theta ≫ F.map (H.map' 0 1)) ≫ F.map k0 =
    theta ≫ F.map k
  rw [Category.assoc, ← F.map_comp]
  congr 1
  apply congrArg F.map
  subst H
  unfold k0 k alpha0
  simp only [eqToHom_refl, Category.id_comp]
  have hij : (alpha.toOrderHom 0).val ≤ (alpha.toOrderHom 1).val :=
    Fin.le_iff_val_le_val.mp (alpha.toOrderHom.monotone (Fin.zero_le _))
  have hjm : (alpha.toOrderHom 1).val ≤ m :=
    Nat.le_of_lt_succ (alpha.toOrderHom 1).isLt
  change x.map' (alpha.toOrderHom 0).val (alpha.toOrderHom 1).val
      hij hjm ≫ x.map' (alpha.toOrderHom 1).val m hjm le_rfl =
    x.map' (alpha.toOrderHom 0).val m (hij.trans hjm) le_rfl
  exact (x.map'_comp _ _ _ hij hjm le_rfl).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromTriple_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHlast : SrepBridge.srepDropLast H = x.whiskerLeft
      (SimplexCategory.δ (Fin.last (n + 1)) ≫
        alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromTriple F x
        ⟨SrepBridge.srepDropLast H, SrepBridge.srepDropLast G,
          G.map' n (n + 1) ≫ theta⟩
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha) hHlast =
      ⟨SrepBridge.srepDropLast G, ULift.up PUnit.unit,
        G.map' n (n + 1) ≫
          (quillenASourceFiberRetractionFromTriple F x
            ⟨H, G, theta⟩ alpha hH).2.2⟩ := by
  unfold quillenASourceFiberRetractionFromTriple
  dsimp only
  congr 2
  let alphaLast := SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha
  let kLast : (SrepBridge.srepDropLast H).left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hHlast) ≫
      x.map' (alphaLast.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alphaLast.toOrderHom 0).isLt) le_rfl
  let k : H.left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH) ≫
      x.map' (alpha.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
  change (G.map' n (n + 1) ≫ theta) ≫ F.map kLast =
    G.map' n (n + 1) ≫ (theta ≫ F.map k)
  rw [Category.assoc]

private theorem quillenABridgeFaceInnerZero (n : ℕ) (q : Fin n) :
    (SimplexCategory.δ
      q.castSucc.succ).toOrderHom.toFunctor.obj 0 = 0 := by
  change q.castSucc.succ.succAbove 0 = 0
  exact Fin.succAbove_ne_zero_zero (by simp)

private theorem quillenABridgeFaceInnerLast (n : ℕ) (q : Fin n) :
    (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor.obj
        (Fin.last n) = Fin.last (n + 1) := by
  exact Fin.succAbove_ne_last_last (quillenACastSucc_succ_ne_last q)

private theorem quillenABridgeFaceInnerLeftObj
    {C : Type u} [Category.{v} C] (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1)) :
    H.left = (H.whiskerLeft
      (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor).left := by
  change H.obj 0 = H.obj
    ((SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor.obj 0)
  exact congrArg H.obj (quillenABridgeFaceInnerZero n q).symm

private theorem quillenABridgeFaceInnerRightObj
    {D : Type u} [Category.{v} D] (n : ℕ) (q : Fin n)
    (G : ComposableArrows D (n + 1)) :
    (G.whiskerLeft
      (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor).right =
        G.right := by
  change G.obj
      ((SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor.obj
        (Fin.last n)) = G.obj (Fin.last (n + 1))
  exact congrArg G.obj (quillenABridgeFaceInnerLast n q)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromTriple_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (q : Fin n) (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHi : (StrictOmitDup.omitAt q.castSucc.succ).obj H =
      x.whiskerLeft
        (SimplexCategory.δ q.castSucc.succ ≫
          alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromTriple F x
        ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj H,
          (StrictOmitDup.omitAt q.castSucc.succ).obj G,
          eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
            F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))⟩
        (SimplexCategory.δ q.castSucc.succ ≫ alpha) hHi =
      ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj G,
        ULift.up PUnit.unit,
        eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫
          (quillenASourceFiberRetractionFromTriple F x
            ⟨H, G, theta⟩ alpha hH).2.2⟩ := by
  unfold quillenASourceFiberRetractionFromTriple
  dsimp only
  congr 2
  let j : Fin (n + 2) := q.castSucc.succ
  let alphaI := SimplexCategory.δ j ≫ alpha
  let ki : ((StrictOmitDup.omitAt j).obj H).left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hHi) ≫
      x.map' (alphaI.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alphaI.toOrderHom 0).isLt) le_rfl
  let k : H.left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH) ≫
      x.map' (alpha.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
  change (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
      F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))) ≫
        F.map ki =
    eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫
      (theta ≫ F.map k)
  simp only [Category.assoc]
  congr 2
  rw [← F.map_comp]
  apply congrArg F.map
  subst H
  unfold ki k alphaI
  rw [← Category.assoc, eqToHom_trans]

private theorem quillenASourceFiberDegLeftObj
    {C : Type u} [Category.{v} C] {n : ℕ} (i : Fin (n + 1))
    (H : ComposableArrows C n) :
    H.left = ((StrictOmitDup.dupAt i).obj H).left := by
  change H.obj 0 = H.obj
    ((SimplexCategory.σ i).toOrderHom.toFunctor.obj 0)
  exact congrArg H.obj (Fin.predAbove_right_zero (i := i)).symm

private theorem quillenASourceFiberDegRightObj
    {C : Type u} [Category.{v} C] {n : ℕ} (i : Fin (n + 1))
    (H : ComposableArrows C n) :
    ((StrictOmitDup.dupAt i).obj H).right = H.right := by
  change H.obj
    ((SimplexCategory.σ i).toOrderHom.toFunctor.obj (Fin.last (n + 1))) =
      H.obj (Fin.last n)
  exact congrArg H.obj Fin.predAbove_right_last

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromTriple_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (i : Fin (n + 1)) (H : ComposableArrows C n)
    (G : ComposableArrows D n) (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHs : (StrictOmitDup.dupAt i).obj H = x.whiskerLeft
      (SimplexCategory.σ i ≫ alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromTriple F x
        ⟨(StrictOmitDup.dupAt i).obj H,
          (StrictOmitDup.dupAt i).obj G,
          eqToHom (quillenASourceFiberDegRightObj i G) ≫ theta ≫
            F.map (eqToHom (quillenASourceFiberDegLeftObj i H))⟩
        (SimplexCategory.σ i ≫ alpha) hHs =
      ⟨(StrictOmitDup.dupAt i).obj G, ULift.up PUnit.unit,
        eqToHom (quillenASourceFiberDegRightObj i G) ≫
          (quillenASourceFiberRetractionFromTriple F x
            ⟨H, G, theta⟩ alpha hH).2.2⟩ := by
  unfold quillenASourceFiberRetractionFromTriple
  dsimp only
  congr 2
  let alphaSigma := SimplexCategory.σ i ≫ alpha
  let kSigma : ((StrictOmitDup.dupAt i).obj H).left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hHs) ≫
      x.map' (alphaSigma.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alphaSigma.toOrderHom 0).isLt) le_rfl
  let k : H.left ⟶ x.right :=
    eqToHom (congrArg ComposableArrows.left hH) ≫
      x.map' (alpha.toOrderHom 0).val m
        (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
  change (eqToHom (quillenASourceFiberDegRightObj i G) ≫ theta ≫
      F.map (eqToHom (quillenASourceFiberDegLeftObj i H))) ≫
        F.map kSigma =
    eqToHom (quillenASourceFiberDegRightObj i G) ≫
      (theta ≫ F.map k)
  simp only [Category.assoc]
  congr 2
  rw [← F.map_comp]
  apply congrArg F.map
  subst H
  unfold kSigma k alphaSigma
  rw [← Category.assoc, eqToHom_trans]

private noncomputable def quillenARealizedTensorSndHomotopyEquiv
    (X : SSet.{w}) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((Δ[1] : SSet.{w}) ⊗ X))
      (SSet.toTop.obj X) where
  toFun :=
    (SSet.toTop.map
      (snd _ _ : (Δ[1] : SSet.{w}) ⊗ X ⟶ X)).hom
  invFun := (SSet.toTop.map (SSet.stdSimplexProdLastSection 1 X)).hom
  left_inv := by
    refine ⟨?_⟩
    have H := SSet.realizeHomotopy
      ((Δ[1] : SSet.{w}) ⊗ X)
      ((Δ[1] : SSet.{w}) ⊗ X)
      (𝟙 _)
      ((snd _ _ : (Δ[1] : SSet.{w}) ⊗ X ⟶ X) ≫
        SSet.stdSimplexProdLastSection 1 X)
      (SSet.stdSimplexProdContraction 1 X)
    apply ContinuousMap.Homotopy.cast H.symm
    · rw [Functor.map_comp]
      rfl
    · exact congrArg ConcreteCategory.hom
        (CategoryTheory.Functor.map_id SSet.toTop _)
  right_inv := by
    have hcomp :
        (SSet.toTop.map
            (snd _ _ : (Δ[1] : SSet.{w}) ⊗ X ⟶ X)).hom.comp
          (SSet.toTop.map (SSet.stdSimplexProdLastSection 1 X)).hom =
            ContinuousMap.id (SSet.toTop.obj X) := by
      rw [← TopCat.hom_comp, ← Functor.map_comp,
        SSet.stdSimplexProdLastSection_snd,
        CategoryTheory.Functor.map_id]
      rfl
    rw [hcomp]

private theorem quillenATensorSnd_mem_realizationWeakEquivalences
    (X : SSet.{w}) :
    SSet.realizationWeakEquivalences
      (snd _ _ : (Δ[1] : SSet.{w}) ⊗ X ⟶ X) := by
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map
      (snd _ _ : (Δ[1] : SSet.{w}) ⊗ X ⟶ X))
  exact TopCat.mem_of_eq_toFun
    (quillenARealizedTensorSndHomotopyEquiv X) rfl

private theorem quillenAStandardCylinderProjection_mem_realizationWeakEquivalences
    (X : SSet.{w}) :
    SSet.realizationWeakEquivalences (fst X (Δ[1] : SSet.{w})) := by
  have hb : SSet.realizationWeakEquivalences
      ((β_ X (Δ[1] : SSet.{w})).hom) :=
    MorphismProperty.of_isIso SSet.realizationWeakEquivalences _
  have hs : SSet.realizationWeakEquivalences
      (snd (Δ[1] : SSet.{w}) X) :=
    quillenATensorSnd_mem_realizationWeakEquivalences X
  have hc := SSet.realizationWeakEquivalences.comp_mem
    ((β_ X (Δ[1] : SSet.{w})).hom)
    (snd (Δ[1] : SSet.{w}) X) hb hs
  simpa only [braiding_hom_snd] using hc

private theorem quillenARealizationWeakEquivalences_of_homotopy
    {X Y : SSet.{w}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences g := by
  have hp := quillenAStandardCylinderProjection_mem_realizationWeakEquivalences X
  have hi0 : SSet.realizationWeakEquivalences
      (SSet.ι₀ : X ⟶ X ⊗ Δ[1]) := by
    apply SSet.realizationWeakEquivalences.of_postcomp
      (SSet.ι₀ : X ⟶ X ⊗ Δ[1])
      (fst X (Δ[1] : SSet.{w})) hp
    rw [SSet.ι₀_fst]
    exact SSet.realizationWeakEquivalences.id_mem X
  have hi1 : SSet.realizationWeakEquivalences
      (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) := by
    apply SSet.realizationWeakEquivalences.of_postcomp
      (SSet.ι₁ : X ⟶ X ⊗ Δ[1])
      (fst X (Δ[1] : SSet.{w})) hp
    rw [SSet.ι₁_fst]
    exact SSet.realizationWeakEquivalences.id_mem X
  have hH : SSet.realizationWeakEquivalences H.h := by
    apply SSet.realizationWeakEquivalences.of_precomp
      (SSet.ι₀ : X ⟶ X ⊗ Δ[1]) H.h hi0
    simpa only [SSet.Homotopy.h₀] using hf
  have hg : SSet.realizationWeakEquivalences
      ((SSet.ι₁ : X ⟶ X ⊗ Δ[1]) ≫ H.h) :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hi1 hH
  simpa only [SSet.Homotopy.h₁] using hg

private def quillenABridgeNatTrans
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) : G ⟶ H ⋙ F where
  app i := quillenABridgeComponent F H G theta i
  naturality {i j} a := by
    have hG : G.map a ≫ G.map' j.val n = G.map' i.val n := by
      rw [← G.map_comp]
      congr 1
    have hH : H.map' 0 i.val ≫ H.map a = H.map' 0 j.val := by
      rw [← H.map_comp]
      congr 1
    change G.map a ≫ (G.map' j.val n ≫ theta ≫
        F.map (H.map' 0 j.val)) =
      (G.map' i.val n ≫ theta ≫ F.map (H.map' 0 i.val)) ≫
        F.map (H.map a)
    rw [← Category.assoc, hG]
    simp only [Category.assoc, ← F.map_comp, hH]

private def quillenANerveCylinderFunctor
    {A : Type w} [Category.{0} A]
    {D : Type u} [Category.{v} D] {P Q : A ⥤ D}
    (eta : P ⟶ Q) : A × Fin 2 ⥤ D :=
  Prod.swap A (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ eta)

@[simp]
private theorem quillenANerveCylinderFunctor_map_zero
    {A : Type w} [Category.{0} A]
    {D : Type u} [Category.{v} D] {P Q : A ⥤ D}
    (eta : P ⟶ Q) {X Y : A} (f : X ⟶ Y) :
    (quillenANerveCylinderFunctor eta).map
        (f ×ₘ 𝟙 (0 : Fin 2)) = P.map f := by
  simp only [quillenANerveCylinderFunctor, Functor.comp_map,
    Prod.swap_map, Functor.uncurry_obj_map]
  change 𝟙 (P.obj X) ≫ P.map f = P.map f
  simp

@[simp]
private theorem quillenANerveCylinderFunctor_map_one
    {A : Type w} [Category.{0} A]
    {D : Type u} [Category.{v} D] {P Q : A ⥤ D}
    (eta : P ⟶ Q) {X Y : A} (f : X ⟶ Y) :
    (quillenANerveCylinderFunctor eta).map
        (f ×ₘ 𝟙 (1 : Fin 2)) = Q.map f := by
  simp only [quillenANerveCylinderFunctor, Functor.comp_map,
    Prod.swap_map, Functor.uncurry_obj_map]
  change 𝟙 (Q.obj X) ≫ Q.map f = Q.map f
  simp

private noncomputable def quillenACylinderChain
    {A : Type w} [Category.{0} A]
    {D : Type u} [Category.{v} D] {P Q : A ⥤ D}
    (eta : P ⟶ Q) {n : ℕ} (X : ComposableArrows A n)
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    ComposableArrows D n :=
  ((quillenANerveCylinderFunctor eta).mapComposableArrows n).obj
    (X.prod' (SSet.stdSimplex.asOrderHom t).toFunctor)

private theorem quillenACylinderChain_map
    {A : Type w} [Category.{0} A]
    {D : Type u} [Category.{v} D] {P Q : A ⥤ D}
    (eta : P ⟶ Q) {m n : ℕ}
    (k : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (X : ComposableArrows A n)
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    (nerve D).map k.op (quillenACylinderChain eta X t) =
      quillenACylinderChain eta ((nerve A).map k.op X)
        ((Δ[1] : SSet.{max u v w}).map k.op t) := by
  rfl

private theorem quillenACylinderChain_precomp
    {A' A : Type} [Category A'] [Category A]
    {D : Type u} [Category.{v} D] (K : A' ⥤ A)
    {P Q : A ⥤ D} (eta : P ⟶ Q) {n : ℕ}
    (X : ComposableArrows A' n)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenACylinderChain (Functor.whiskerLeft K eta) X t =
      quillenACylinderChain eta ((K.mapComposableArrows n).obj X) t := by
  have hCyl : quillenANerveCylinderFunctor (Functor.whiskerLeft K eta) =
      (K.prod (𝟭 (Fin 2))) ⋙ quillenANerveCylinderFunctor eta := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [quillenANerveCylinderFunctor, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [quillenANerveCylinderFunctor, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [quillenANerveCylinderFunctor, ComposableArrows.mk₁]
  unfold quillenACylinderChain
  rw [hCyl]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

private noncomputable def quillenABridgePrismChain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    ComposableArrows D n :=
  quillenACylinderChain (quillenABridgeNatTrans F H G theta)
    (𝟭 (Fin (n + 1))) t

private theorem quillenABridgePrismChain_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    {H H' : ComposableArrows C n} {G G' : ComposableArrows D n}
    {theta : G.right ⟶ F.obj H.left}
    {theta' : G'.right ⟶ F.obj H'.left}
    {t t' : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)}
    (hH : H = H') (hG : G = G') (hTheta : HEq theta theta')
    (ht : t = t') :
    quillenABridgePrismChain F H G theta t =
      quillenABridgePrismChain F H' G' theta' t' := by
  cases hH
  cases hG
  cases hTheta
  cases ht
  rfl

private noncomputable def quillenABridgeRawApp
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    ComposableArrows D n :=
  quillenABridgePrismChain F p.1 (CategoryBar.barChain x)
    (CategoryBar.barCoeffR x) t

private noncomputable def quillenABridgeFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    ComposableArrows D n :=
  quillenABridgeRawApp F n r.1 r.2 t

private theorem quillenABridgeFromRaw_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    {r r' : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)}
    (hr : r = r')
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenABridgeFromRaw F n r t =
      quillenABridgeFromRaw F n r' t := by
  cases hr
  rfl

private noncomputable def quillenABridgeApp
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    ((quillenAMappingCarrier F) ⊗
      (Δ[1] : SSet.{max u v})).obj (op ⦋n⦌) →
      (nerve D).obj (op ⦋n⦌) :=
  fun z ↦
    let r := quillenAMappingCarrierRawEquiv F n z.1
    quillenABridgeFromRaw F n r z.2

private theorem quillenABridgeApp_incl
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenABridgeApp F n
        ⟨quillenAMappingCarrierIncl F n H G theta, t⟩ =
      quillenABridgePrismChain F H G theta t := by
  unfold quillenABridgeApp
  rw [quillenAMappingCarrierRawEquiv_incl]
  rfl

private theorem quillenABridgePrismChain_of_const_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌))
    (ht : (SSet.stdSimplex.asOrderHom t).toFunctor =
      (Functor.const (Fin (n + 1))).obj (0 : Fin 2)) :
    quillenABridgePrismChain F H G theta t = G := by
  unfold quillenABridgePrismChain
  let eta := quillenABridgeNatTrans F H G theta
  change ((quillenANerveCylinderFunctor eta).mapComposableArrows n).obj
      ((𝟭 (Fin (n + 1))).prod'
        (SSet.stdSimplex.asOrderHom t).toFunctor) = G
  rw [ht]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    change (quillenANerveCylinderFunctor eta).map
        (f ×ₘ 𝟙 (0 : Fin 2)) ≍ G.map f
    exact heq_of_eq (quillenANerveCylinderFunctor_map_zero eta f)

private theorem quillenABridgePrismChain_of_const_one
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ}
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌))
    (ht : (SSet.stdSimplex.asOrderHom t).toFunctor =
      (Functor.const (Fin (n + 1))).obj (1 : Fin 2)) :
    quillenABridgePrismChain F H G theta t =
      (F.mapComposableArrows n).obj H := by
  unfold quillenABridgePrismChain
  let eta := quillenABridgeNatTrans F H G theta
  change ((quillenANerveCylinderFunctor eta).mapComposableArrows n).obj
      ((𝟭 (Fin (n + 1))).prod'
        (SSet.stdSimplex.asOrderHom t).toFunctor) =
    (F.mapComposableArrows n).obj H
  rw [ht]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    change (quillenANerveCylinderFunctor eta).map
        (f ×ₘ 𝟙 (1 : Fin 2)) ≍ (H ⋙ F).map f
    exact heq_of_eq (quillenANerveCylinderFunctor_map_one eta f)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeNatTrans_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenABridgeNatTrans F ((nerve C).δ 0 H)
        ((nerve D).δ 0 G) (theta ≫ F.map (H.map' 0 1)) =
      Functor.whiskerLeft
        (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.toFunctor
        (quillenABridgeNatTrans F H G theta) := by
  ext i
  change quillenABridgeComponent F ((nerve C).δ 0 H)
      ((nerve D).δ 0 G) (theta ≫ F.map (H.map' 0 1)) i =
    quillenABridgeComponent F H G theta
      ((SimplexCategory.δ
        (0 : Fin (n + 2))).toOrderHom.toFunctor.obj i)
  have hi : i.val ≤ n := by
    simpa only [SimplexCategory.len_mk] using
      Nat.le_of_lt_succ i.isLt
  have hiObj :
      (SimplexCategory.δ
        (0 : Fin (n + 2))).toOrderHom.toFunctor.obj i =
        (⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hi)⟩ :
          Fin (n + 2)) := by
    rfl
  cases hiObj
  unfold quillenABridgeComponent
  have hG : ((nerve D).δ 0 G).map' i.val n hi le_rfl =
      G.map' (i.val + 1) (n + 1) (Nat.succ_le_succ hi) le_rfl := by
    rfl
  have hH : H.map' 0 1 (by omega) (by omega) ≫
      ((nerve C).δ 0 H).map' 0 i.val (Nat.zero_le _) hi =
        H.map' 0 (i.val + 1) (Nat.zero_le _)
          (Nat.succ_le_succ hi) := by
    change H.map' 0 1 ≫ H.map' 1 (i.val + 1) =
      H.map' 0 (i.val + 1)
    exact (H.map'_comp 0 1 (i.val + 1)).symm
  rw [hG]
  simp only [Category.assoc, ← F.map_comp, hH]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgePrismChain_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ 0 (quillenABridgePrismChain F H G theta t) =
      quillenABridgePrismChain F ((nerve C).δ 0 H)
        ((nerve D).δ 0 G) (theta ≫ F.map (H.map' 0 1))
        ((Δ[1] : SSet.{max u v}).δ 0 t) := by
  unfold quillenABridgePrismChain
  change (nerve D).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op
        (quillenACylinderChain (quillenABridgeNatTrans F H G theta)
          (𝟭 (Fin (n + 2))) t) =
    quillenACylinderChain
      (quillenABridgeNatTrans F ((nerve C).δ 0 H)
        ((nerve D).δ 0 G) (theta ≫ F.map (H.map' 0 1)))
      (𝟭 (Fin (n + 1)))
      ((Δ[1] : SSet.{max u v}).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op t)
  rw [quillenACylinderChain_map,
    quillenABridgeNatTrans_δ_zero,
    quillenACylinderChain_precomp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceZeroInner_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    CategoryBar.barChain
        (quillenAMappingCarrierFaceZeroInner F n H G theta) =
      (nerve D).δ 0 G := by
  unfold quillenAMappingCarrierFaceZeroInner
    quillenAMappingCarrierFaceZeroInnerOf
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op x =
        CategoryBar.barδ 0 x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op) x =
      CategoryBar.barδ 0 x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  have hSrep :
      SrepBridge.srepFaceZeroComponent
          (quillenAMappingDiagram F) H =
        (quillenAMappingDiagram F).map (H.map' 0 1) := by
    unfold SrepBridge.srepFaceZeroComponent
    change 𝟙 _ ≫ (quillenAMappingDiagram F).map (H.map' 0 1) ≫
      𝟙 _ = (quillenAMappingDiagram F).map (H.map' 0 1)
    simp
  rw [hInnerMap, hSrep]
  dsimp only [x, quillenAMappingCarrierInner]
  rw [CategoryBar.barδ_zero_eq]
  simp only [quillenAMappingDiagram,
    CategoryBar.categoryBarMap_app_mk]
  dsimp only [id, CategoryBar.barCoeffMap, CategoryBar.barChain]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceZeroInner_theta
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    HEq (CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceZeroInner F n H G theta))
      (theta ≫ F.map (H.map' 0 1)) := by
  unfold quillenAMappingCarrierFaceZeroInner
    quillenAMappingCarrierFaceZeroInnerOf
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op x =
        CategoryBar.barδ 0 x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op) x =
      CategoryBar.barδ 0 x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  have hSrep :
      SrepBridge.srepFaceZeroComponent
          (quillenAMappingDiagram F) H =
        (quillenAMappingDiagram F).map (H.map' 0 1) := by
    unfold SrepBridge.srepFaceZeroComponent
    change 𝟙 _ ≫ (quillenAMappingDiagram F).map (H.map' 0 1) ≫
      𝟙 _ = (quillenAMappingDiagram F).map (H.map' 0 1)
    simp
  rw [hInnerMap, hSrep]
  dsimp only [x, quillenAMappingCarrierInner]
  rw [CategoryBar.barδ_zero_eq]
  simp only [quillenAMappingDiagram,
    CategoryBar.categoryBarMap_app_mk]
  dsimp only [id, CategoryBar.barCoeffMap]
  change HEq (CategoryBar.barCoeffR (CategoryBar.barCoeffMap
    (CategoryBar.commaCoeffRMap (𝟭 D) (F.map (H.map' 0 1)))
    (𝟙 (CategoryBar.unitCoeffL D)) _)) _
  rw [CategoryBar.barCoeffMap_coeffR]
  rfl

private theorem quillenAMappingCarrierFaceZeroIndex_chain
    {C : Type u} [Category.{v} C] (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    (StrictOrdinaryWeightedBar.wFaceZeroIdx
      (CategoryBar.replUnit C) n p).1 = (nerve C).δ 0 p.1 := by
  rfl

private theorem quillenAMappingCarrierFaceZeroInnerOf_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    CategoryBar.barChain
        (quillenAMappingCarrierFaceZeroInnerOf F n p x) =
      (nerve D).δ 0 (CategoryBar.barChain x) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenAMappingCarrierFaceZeroInner_chain F n H G theta

private theorem quillenAMappingCarrierFaceZeroInnerOf_theta
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    HEq (CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceZeroInnerOf F n p x))
      (CategoryBar.barCoeffR x ≫
        F.map (p.1.map' 0 1)) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenAMappingCarrierFaceZeroInner_theta F n H G theta

private theorem quillenAProd_heq
    {α α' : Type u} {β β' : Type v}
    {a : α} {a' : α'} {b : β} {b' : β'}
    (ha : HEq a a') (hb : HEq b b') :
    HEq (a, b) (a', b') := by
  cases ha
  cases hb
  rfl

private theorem quillenASigma_heq
    {α : Type u} {β : α → Type v}
    {a a' : α} {b : β a} {b' : β a'}
    (ha : HEq a a') (hb : HEq b b') :
    HEq (⟨a, b⟩ : Σ x, β x) (⟨a', b'⟩ : Σ x, β x) := by
  cases ha
  cases hb
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceZeroInner_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierFaceZeroInner F n H G theta =
      quillenAMappingCarrierInner F n
        ((nerve C).δ 0 H) ((nerve D).δ 0 G)
        (theta ≫ F.map (H.map' 0 1)) := by
  have hchain := quillenAMappingCarrierFaceZeroInner_chain
    F n H G theta
  have htheta := quillenAMappingCarrierFaceZeroInner_theta
    F n H G theta
  refine Sigma.ext hchain ?_
  apply quillenAProd_heq
  · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · exact htheta

private theorem quillenAMappingCarrierFaceZeroTripleOf
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawToTriple F n
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceZeroInnerOf F n p z⟩ =
      ⟨SrepBridge.srepDropFirst p.1,
        (nerve D).δ 0 (CategoryBar.barChain z),
        CategoryBar.barCoeffR z ≫ F.map (p.1.map' 0 1)⟩ := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift.{0} PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  unfold quillenAMappingCarrierRawToTriple
  change (⟨(StrictOrdinaryWeightedBar.wFaceZeroIdx
      (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩).1,
    ⟨CategoryBar.barChain
        (quillenAMappingCarrierFaceZeroInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩),
      CategoryBar.barCoeffR
        (quillenAMappingCarrierFaceZeroInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩)⟩⟩ :
    Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left) = _
  apply Sigma.ext (quillenAMappingCarrierFaceZeroIndex_chain n
    ⟨H, PUnit.unit⟩)
  apply heq_of_eq
  apply Sigma.ext
  · exact quillenAMappingCarrierFaceZeroInner_chain F n H G theta
  · exact quillenAMappingCarrierFaceZeroInner_theta F n H G theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (hG : G = (nerve D).map alpha.op y)
    (hG0 : CategoryBar.barChain
        (quillenAMappingCarrierFaceZeroInner F n H G theta) =
      (nerve D).map
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
          quillenAMappingCarrierFaceZeroInner F n H G theta⟩ hG0 =
      CategoryBar.barδ 0
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H G theta⟩ hG) := by
  let Gy : ComposableArrows D (n + 1) := (nerve D).map alpha.op y
  change G = Gy at hG
  subst G
  let rFace : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
      quillenAMappingCarrierFaceZeroInner F n H Gy theta⟩
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨⟨(nerve C).δ 0 H, PUnit.unit⟩,
      quillenAMappingCarrierInner F n
        ((nerve C).δ 0 H) ((nerve D).δ 0 Gy)
        (theta ≫ F.map (H.map' 0 1))⟩
  have hRaw : rFace = rCanonical := by
    have hp : rFace.1 = rCanonical.1 := by
      refine Sigma.ext rfl ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceZeroInner_eq_canonical F n H Gy theta)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha).op y := by
    rw [← hRaw]
    exact hG0
  have hReplace := quillenATargetFiberRetractionFromRaw_congr
    F y n (rfl :
      (SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha =
        (SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha)
      hRaw hG0 hGCanonical
  calc
    _ = quillenATargetFiberRetractionFromRaw F y n
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha)
        rCanonical hGCanonical := by
      simpa only [rFace] using hReplace
    _ = CategoryBar.barδ 0
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H Gy theta⟩
            (by rfl)) := by
      rw [CategoryBar.barδ_zero_eq]
      unfold rCanonical quillenATargetFiberRetractionFromRaw
      dsimp only [quillenAMappingCarrierInner]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Prod.ext
      · simp only [Functor.op_obj,
          SimplexCategoryGenRel.fromSimplexCategory_obj,
          CategoryBar.commaCoeffL_obj,
          SimplexCategory.comp_toOrderHom, homOfLE_leOfHom,
          CategoryBar.commaCoeffR_obj, Functor.id_obj,
          ComposableArrows.map', Fin.zero_eta, Fin.mk_one, id_eq,
          eqToHom_refl, Category.id_comp, ComposableArrows.obj', cast_eq]
        change y.map
            (homOfLE (Fin.zero_le
              (alpha.toOrderHom (Fin.last (n + 1))))) ≫
              (theta ≫ F.map (H.map' 0 1)) =
            (y.map
              (homOfLE (Fin.zero_le
                (alpha.toOrderHom (Fin.last (n + 1))))) ≫
                theta) ≫ F.map (H.map' 0 1)
        exact (Category.assoc _ _ _).symm
      · change (PUnit.unit : PUnit) = PUnit.unit
        rfl

private theorem quillenABridgeRawApp_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ 0 (quillenABridgePrismChain F H G theta t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n
            (quillenAMappingIndex (n + 1) H))
        (quillenAMappingCarrierFaceZeroInner F n H G theta)
        ((Δ[1] : SSet.{max u v}).δ 0 t) := by
  calc
    _ = quillenABridgePrismChain F ((nerve C).δ 0 H)
        ((nerve D).δ 0 G) (theta ≫ F.map (H.map' 0 1))
        ((Δ[1] : SSet.{max u v}).δ 0 t) :=
      quillenABridgePrismChain_δ_zero F n H G theta t
    _ = _ := by
      unfold quillenABridgeRawApp
      apply quillenABridgePrismChain_congr F
      · exact (quillenAMappingCarrierFaceZeroIndex_chain n
          (quillenAMappingIndex (n + 1) H)).symm
      · exact (quillenAMappingCarrierFaceZeroInner_chain
          F n H G theta).symm
      · exact (quillenAMappingCarrierFaceZeroInner_theta
          F n H G theta).symm
      · rfl

private theorem quillenABridgeRawApp_δ_zero_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ 0 (quillenABridgeRawApp F (n + 1) p x t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n p)
        (quillenAMappingCarrierFaceZeroInnerOf F n p x)
        ((Δ[1] : SSet.{max u v}).δ 0 t) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenABridgeRawApp_δ_zero F n H G theta t

private theorem quillenABridgeApp_δ_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ 0 (quillenABridgeApp F (n + 1) ⟨z, t⟩) =
      quillenABridgeApp F n
        ⟨(quillenAMappingCarrier F).δ 0 z,
          (Δ[1] : SSet.{max u v}).δ 0 t⟩ := by
  rcases hraw : quillenAMappingCarrierRawEquiv F (n + 1) z with
    ⟨p, x⟩
  have hz : z =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [hraw, quillenAMappingCarrierRawEquiv_wbarIncl]
  subst z
  unfold quillenABridgeApp quillenABridgeFromRaw
  rw [quillenAMappingCarrierRawEquiv_wbarIncl,
    quillenAMappingCarrierRawEquiv_δ_zero_of]
  exact quillenABridgeRawApp_δ_zero_of F n p x t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeFaceLastIndex
    (n : ℕ) (i : Fin (n + 1)) :
    (SimplexCategory.δ
      (Fin.last (n + 1))).toOrderHom.toFunctor.obj i = i.castSucc :=
  Fin.succAbove_last_apply i

private theorem quillenABridgeFaceLastRight
    {D : Type u} [Category.{v} D] (n : ℕ)
    (G : ComposableArrows D (n + 1)) :
    ((nerve D).δ (Fin.last (n + 1)) G).right = G.obj' n := by
  change G.obj
      ((SimplexCategory.δ
        (Fin.last (n + 1))).toOrderHom.toFunctor.obj (Fin.last n)) =
    G.obj ⟨n, by omega⟩
  exact congrArg G.obj (quillenABridgeFaceLastIndex n (Fin.last n))

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceLastInner_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    CategoryBar.barChain
        (quillenAMappingCarrierFaceLastInner F n H G theta) =
      (nerve D).δ (Fin.last (n + 1)) G := by
  unfold quillenAMappingCarrierFaceLastInner
    quillenAMappingCarrierFaceLastInnerOf
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ (Fin.last (n + 1))).op x =
        CategoryBar.barδ (Fin.last (n + 1)) x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ (Fin.last (n + 1))).op) x =
      CategoryBar.barδ (Fin.last (n + 1)) x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  have hSrep : SrepBridge.srepFaceLastComponent
      (quillenAMappingDiagram F) H = 𝟙 _ := by
    unfold SrepBridge.srepFaceLastComponent
    change 𝟙 _ = 𝟙 _
    rfl
  rw [hInnerMap, hSrep]
  simp only [NatTrans.id_app, id_eq]
  dsimp only [x, quillenAMappingCarrierInner]
  rw [CategoryBar.barδ_last_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceLastInner_theta
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    HEq (CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceLastInner F n H G theta))
      (G.map' n (n + 1) ≫ theta) := by
  unfold quillenAMappingCarrierFaceLastInner
    quillenAMappingCarrierFaceLastInnerOf
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ (Fin.last (n + 1))).op x =
        CategoryBar.barδ (Fin.last (n + 1)) x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ (Fin.last (n + 1))).op) x =
      CategoryBar.barδ (Fin.last (n + 1)) x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  have hSrep : SrepBridge.srepFaceLastComponent
      (quillenAMappingDiagram F) H = 𝟙 _ := by
    unfold SrepBridge.srepFaceLastComponent
    change 𝟙 _ = 𝟙 _
    rfl
  rw [hInnerMap, hSrep]
  simp only [NatTrans.id_app, id_eq]
  dsimp only [x, quillenAMappingCarrierInner]
  rw [CategoryBar.barδ_last_eq]
  exact cast_heq _ _

private theorem quillenAMappingCarrierFaceLastIndex_chain
    {C : Type u} [Category.{v} C] (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    (StrictOrdinaryWeightedBar.wFaceLastIdx
      (CategoryBar.replUnit C) n p).1 =
        (nerve C).δ (Fin.last (n + 1)) p.1 := by
  rcases p with ⟨H, q⟩
  have hidx :
      (SimplexCategory.δ
        (Fin.last (n + 1))).toOrderHom.toFunctor =
        Fin.castSuccFunctor (n + 1) := by
    refine Functor.ext (fun k ↦ Fin.succAbove_last_apply k) ?_
    intro a b f
    apply Subsingleton.elim
  change H.whiskerLeft (Fin.castSuccFunctor (n + 1)) =
    H.whiskerLeft
      (SimplexCategory.δ
        (Fin.last (n + 1))).toOrderHom.toFunctor
  rw [hidx]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceLastInner_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierFaceLastInner F n H G theta =
      quillenAMappingCarrierInner F n
        ((nerve C).δ (Fin.last (n + 1)) H)
        ((nerve D).δ (Fin.last (n + 1)) G)
        (eqToHom (quillenABridgeFaceLastRight n G) ≫
          G.map' n (n + 1) ≫ theta) := by
  refine Sigma.ext (quillenAMappingCarrierFaceLastInner_chain
    F n H G theta) ?_
  apply quillenAProd_heq
  · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · exact (quillenAMappingCarrierFaceLastInner_theta
      F n H G theta).trans
      (CategoryTheory.eqToHom_comp_heq
        (G.map' n (n + 1) ≫ theta)
        (quillenABridgeFaceLastRight n G)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (hG : G = (nerve D).map alpha.op y)
    (hGl : CategoryBar.barChain
        (quillenAMappingCarrierFaceLastInner F n H G theta) =
      (nerve D).map
        ((SimplexCategory.δ (Fin.last (n + 1))) ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        ((SimplexCategory.δ (Fin.last (n + 1))) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
          quillenAMappingCarrierFaceLastInner F n H G theta⟩ hGl =
      CategoryBar.barδ (Fin.last (n + 1))
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H G theta⟩ hG) := by
  let Gy : ComposableArrows D (n + 1) := (nerve D).map alpha.op y
  change G = Gy at hG
  subst G
  let i : Fin (n + 2) := Fin.last (n + 1)
  let rFace : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
      quillenAMappingCarrierFaceLastInner F n H Gy theta⟩
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨⟨(nerve C).δ i H, PUnit.unit⟩,
      quillenAMappingCarrierInner F n
        ((nerve C).δ i H) ((nerve D).δ i Gy)
        (eqToHom (quillenABridgeFaceLastRight n Gy) ≫
          Gy.map' n (n + 1) ≫ theta)⟩
  have hRaw : rFace = rCanonical := by
    have hp : rFace.1 = rCanonical.1 := by
      refine Sigma.ext
        (quillenAMappingCarrierFaceLastIndex_chain
          n ⟨H, PUnit.unit⟩) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceLastInner_eq_canonical F n H Gy theta)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map (SimplexCategory.δ i ≫ alpha).op y := by
    rw [← hRaw]
    exact hGl
  have hReplace := quillenATargetFiberRetractionFromRaw_congr
    F y n (rfl : SimplexCategory.δ i ≫ alpha =
      SimplexCategory.δ i ≫ alpha) hRaw hGl hGCanonical
  calc
    _ = quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ i ≫ alpha)
        rCanonical hGCanonical := by
      simpa only [rFace, i] using hReplace
    _ = CategoryBar.barδ i
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H Gy theta⟩
            (by rfl)) := by
      dsimp only [i]
      rw [CategoryBar.barδ_last_eq]
      unfold rCanonical quillenATargetFiberRetractionFromRaw
      dsimp only [quillenAMappingCarrierInner]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Prod.ext
      · simp only [Functor.op_obj,
          SimplexCategoryGenRel.fromSimplexCategory_obj,
          CategoryBar.commaCoeffL_obj,
          SimplexCategory.comp_toOrderHom, homOfLE_leOfHom,
          CategoryBar.commaCoeffR_obj, Functor.id_obj,
          ComposableArrows.obj', ComposableArrows.map', id_eq,
          eqToHom_refl, Category.id_comp, cast_eq]
        dsimp only [CategoryBar.barCoeffR]
        let K : Fin (n + 1) ⥤ Fin (n + 2) :=
          (SimplexCategory.δ
            (Fin.last (n + 1))).toOrderHom.toFunctor
        let A : Fin (n + 2) ⥤ Fin (m + 1) :=
          alpha.toOrderHom.toFunctor
        let a : (0 : Fin (m + 1)) ⟶ A.obj (K.obj (Fin.last n)) :=
          homOfLE (Fin.zero_le _)
        have hIdx : A.obj (K.obj (Fin.last n)) =
            A.obj (⟨n, by omega⟩ : Fin (n + 2)) :=
          congrArg A.obj
            (quillenABridgeFaceLastIndex n (Fin.last n))
        let eIdx : A.obj (K.obj (Fin.last n)) ⟶
            A.obj (⟨n, by omega⟩ : Fin (n + 2)) :=
          eqToHom hIdx
        let b : A.obj (⟨n, by omega⟩ : Fin (n + 2)) ⟶
            A.obj (Fin.last (n + 1)) :=
          A.map (homOfLE (Fin.le_last _))
        let d : (0 : Fin (m + 1)) ⟶
            A.obj (Fin.last (n + 1)) := homOfLE (Fin.zero_le _)
        have hPath : y.map a ≫ y.map eIdx ≫ y.map b =
            y.map d := by
          rw [← y.map_comp, ← y.map_comp]
          apply congrArg y.map
          apply Subsingleton.elim
        change y.map a ≫ eqToHom (congrArg y.obj hIdx) ≫
          y.map b ≫ theta = y.map d ≫ theta
        rw [← eqToHom_map y hIdx]
        change y.map a ≫ y.map eIdx ≫ y.map b ≫ theta =
          y.map d ≫ theta
        simpa only [Category.assoc] using congrArg
          (fun q ↦ q ≫ theta) hPath
      · change (PUnit.unit : PUnit) = PUnit.unit
        rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeNatTrans_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenABridgeNatTrans F
        ((nerve C).δ (Fin.last (n + 1)) H)
        ((nerve D).δ (Fin.last (n + 1)) G)
        (eqToHom (quillenABridgeFaceLastRight n G) ≫
          G.map' n (n + 1) ≫ theta) =
      Functor.whiskerLeft
        (SimplexCategory.δ
          (Fin.last (n + 1))).toOrderHom.toFunctor
        (quillenABridgeNatTrans F H G theta) := by
  ext i
  change Fin (n + 1) at i
  let K : Fin (n + 1) ⥤ Fin (n + 2) :=
    (SimplexCategory.δ
      (Fin.last (n + 1))).toOrderHom.toFunctor
  let a : K.obj i ⟶ K.obj (Fin.last n) :=
    K.map (homOfLE (Fin.le_last i))
  let eIdx : K.obj (Fin.last n) ⟶ (⟨n, by omega⟩ : Fin (n + 2)) :=
    eqToHom (quillenABridgeFaceLastIndex n (Fin.last n))
  let b : (⟨n, by omega⟩ : Fin (n + 2)) ⟶ Fin.last (n + 1) :=
    homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n))
  let d : K.obj i ⟶ Fin.last (n + 1) := homOfLE (Fin.le_last _)
  let c : (0 : Fin (n + 1)) ⟶ i := homOfLE (Fin.zero_le _)
  let e : (0 : Fin (n + 2)) ⟶ K.obj i := homOfLE (Fin.zero_le _)
  have hPathG : G.map a ≫ G.map eIdx ≫ G.map b = G.map d := by
    rw [← G.map_comp, ← G.map_comp]
    apply congrArg G.map
    apply Subsingleton.elim
  have hPathH : H.map (K.map c) = H.map e := by
    apply congrArg H.map
    apply Subsingleton.elim
  change quillenABridgeComponent F
      ((nerve C).δ (Fin.last (n + 1)) H)
      ((nerve D).δ (Fin.last (n + 1)) G)
      (eqToHom (quillenABridgeFaceLastRight n G) ≫
        G.map' n (n + 1) ≫ theta) i =
    quillenABridgeComponent F H G theta (K.obj i)
  unfold quillenABridgeComponent
  change G.map a ≫
      (eqToHom (congrArg G.obj
        (quillenABridgeFaceLastIndex n (Fin.last n))) ≫
          G.map b ≫ theta) ≫
      F.map (H.map (K.map c)) =
    G.map d ≫ theta ≫ F.map (H.map e)
  rw [← eqToHom_map]
  change G.map a ≫ (G.map eIdx ≫ G.map b ≫ theta) ≫
      F.map (H.map (K.map c)) =
    G.map d ≫ theta ≫ F.map (H.map e)
  rw [hPathH]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ theta ≫ F.map (H.map e)) hPathG

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgePrismChain_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ (Fin.last (n + 1))
        (quillenABridgePrismChain F H G theta t) =
      quillenABridgePrismChain F
        ((nerve C).δ (Fin.last (n + 1)) H)
        ((nerve D).δ (Fin.last (n + 1)) G)
        (eqToHom (quillenABridgeFaceLastRight n G) ≫
          G.map' n (n + 1) ≫ theta)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := by
  unfold quillenABridgePrismChain
  change (nerve D).map
      (SimplexCategory.δ (Fin.last (n + 1))).op
        (quillenACylinderChain (quillenABridgeNatTrans F H G theta)
          (𝟭 (Fin (n + 2))) t) =
    quillenACylinderChain
      (quillenABridgeNatTrans F
        ((nerve C).δ (Fin.last (n + 1)) H)
        ((nerve D).δ (Fin.last (n + 1)) G)
        (eqToHom (quillenABridgeFaceLastRight n G) ≫
          G.map' n (n + 1) ≫ theta))
      (𝟭 (Fin (n + 1)))
      ((Δ[1] : SSet.{max u v}).map
        (SimplexCategory.δ (Fin.last (n + 1))).op t)
  rw [quillenACylinderChain_map,
    quillenABridgeNatTrans_δ_last,
    quillenACylinderChain_precomp]
  rfl

private theorem quillenABridgeRawApp_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ (Fin.last (n + 1))
        (quillenABridgePrismChain F H G theta t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n
            (quillenAMappingIndex (n + 1) H))
        (quillenAMappingCarrierFaceLastInner F n H G theta)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := by
  calc
    _ = quillenABridgePrismChain F
        ((nerve C).δ (Fin.last (n + 1)) H)
        ((nerve D).δ (Fin.last (n + 1)) G)
        (eqToHom (quillenABridgeFaceLastRight n G) ≫
          G.map' n (n + 1) ≫ theta)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) :=
      quillenABridgePrismChain_δ_last F n H G theta t
    _ = _ := by
      unfold quillenABridgeRawApp
      apply quillenABridgePrismChain_congr F
      · exact (quillenAMappingCarrierFaceLastIndex_chain n
          (quillenAMappingIndex (n + 1) H)).symm
      · exact (quillenAMappingCarrierFaceLastInner_chain
          F n H G theta).symm
      · exact (CategoryTheory.eqToHom_comp_heq
          (G.map' n (n + 1) ≫ theta)
          (quillenABridgeFaceLastRight n G)).trans
          (quillenAMappingCarrierFaceLastInner_theta
            F n H G theta).symm
      · rfl

private theorem quillenABridgeRawApp_δ_last_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ (Fin.last (n + 1))
        (quillenABridgeRawApp F (n + 1) p x t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n p)
        (quillenAMappingCarrierFaceLastInnerOf F n p x)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenABridgeRawApp_δ_last F n H G theta t

private theorem quillenABridgeApp_δ_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ (Fin.last (n + 1))
        (quillenABridgeApp F (n + 1) ⟨z, t⟩) =
      quillenABridgeApp F n
        ⟨(quillenAMappingCarrier F).δ (Fin.last (n + 1)) z,
          (Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t⟩ := by
  rcases hraw : quillenAMappingCarrierRawEquiv F (n + 1) z with
    ⟨p, x⟩
  have hz : z =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [hraw, quillenAMappingCarrierRawEquiv_wbarIncl]
  subst z
  unfold quillenABridgeApp quillenABridgeFromRaw
  rw [quillenAMappingCarrierRawEquiv_wbarIncl,
    quillenAMappingCarrierRawEquiv_δ_last_of]
  exact quillenABridgeRawApp_δ_last_of F n p x t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceInnerInner_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    CategoryBar.barChain
        (quillenAMappingCarrierFaceInnerInner F n q H G theta) =
      (nerve D).δ q.castSucc.succ G := by
  unfold quillenAMappingCarrierFaceInnerInner
    quillenAMappingCarrierFaceInnerInnerOf
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ i).op x = CategoryBar.barδ i x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ i).op) x = CategoryBar.barδ i x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  dsimp only
  rw [hInnerMap]
  unfold StrictOrdinaryWeightedBar.wFaceInnerComponent
  dsimp only [x, quillenAMappingCarrierInner]
  rw [show i = q.castSucc.succ from rfl,
    CategoryBar.barδ_castSucc_succ_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceInnerInner_theta
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    HEq (CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceInnerInner F n q H G theta)) theta := by
  unfold quillenAMappingCarrierFaceInnerInner
    quillenAMappingCarrierFaceInnerInnerOf
  let i : Fin (n + 2) := q.castSucc.succ
  have hi0 : i ≠ 0 := by
    intro h
    simpa [i] using congrArg Fin.val h
  let x := quillenAMappingCarrierInner F (n + 1) H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.δ i).op x = CategoryBar.barδ i x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.δ i).op) x = CategoryBar.barδ i x
    rw [CategoryBar.categoryBar_map_δ]
    rfl
  dsimp only
  rw [hInnerMap]
  unfold StrictOrdinaryWeightedBar.wFaceInnerComponent
  dsimp only [x, quillenAMappingCarrierInner]
  rw [show i = q.castSucc.succ from rfl,
    CategoryBar.barδ_castSucc_succ_eq]
  exact cast_heq _ _

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeNatTrans_whisker
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ}
    (K : Fin (m + 1) ⥤ Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (h0 : K.obj 0 = 0) (hLast : K.obj (Fin.last m) = Fin.last n) :
    quillenABridgeNatTrans F (H.whiskerLeft K) (G.whiskerLeft K)
        (eqToHom (congrArg G.obj hLast) ≫ theta ≫
          F.map (eqToHom (congrArg H.obj h0).symm)) =
      Functor.whiskerLeft K (quillenABridgeNatTrans F H G theta) := by
  ext i
  change Fin (m + 1) at i
  let a : K.obj i ⟶ K.obj (Fin.last m) :=
    K.map (homOfLE (Fin.le_last i))
  let eLast : K.obj (Fin.last m) ⟶ Fin.last n := eqToHom hLast
  let d : K.obj i ⟶ Fin.last n := homOfLE (Fin.le_last _)
  let c : (0 : Fin (m + 1)) ⟶ i := homOfLE (Fin.zero_le _)
  let eZero : (0 : Fin (n + 1)) ⟶ K.obj 0 := eqToHom h0.symm
  let e : (0 : Fin (n + 1)) ⟶ K.obj i := homOfLE (Fin.zero_le _)
  have hPathG : G.map a ≫ G.map eLast = G.map d := by
    rw [← G.map_comp]
    apply congrArg G.map
    apply Subsingleton.elim
  have hPathH : H.map eZero ≫ H.map (K.map c) = H.map e := by
    rw [← H.map_comp]
    apply congrArg H.map
    apply Subsingleton.elim
  change quillenABridgeComponent F (H.whiskerLeft K)
      (G.whiskerLeft K)
      (eqToHom (congrArg G.obj hLast) ≫ theta ≫
        F.map (eqToHom (congrArg H.obj h0).symm)) i =
    quillenABridgeComponent F H G theta (K.obj i)
  unfold quillenABridgeComponent
  have hGa : (G.whiskerLeft K).map' i.val m = G.map a := by
    rfl
  have hHc : (H.whiskerLeft K).map' 0 i.val = H.map (K.map c) := by
    rfl
  have hGd : G.map' (K.obj i).val n = G.map d := by
    change G.map _ = G.map _
    apply congrArg G.map
    apply Subsingleton.elim
  have hHe : H.map' 0 (K.obj i).val = H.map e := by
    change H.map _ = H.map _
    apply congrArg H.map
    apply Subsingleton.elim
  rw [hGa, hHc, hGd, hHe,
    ← eqToHom_map G hLast, ← eqToHom_map H h0.symm]
  change G.map a ≫
      (G.map eLast ≫ theta ≫ F.map (H.map eZero)) ≫
        F.map (H.map (K.map c)) =
    G.map d ≫ theta ≫ F.map (H.map e)
  simp only [Category.assoc, ← F.map_comp]
  rw [hPathH]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ theta ≫ F.map (H.map e)) hPathG

private theorem quillenABridgeFaceInnerThetaHEq
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    HEq (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
      F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))) theta := by
  rw [eqToHom_map]
  exact (heq_of_eq (Category.assoc
      (eqToHom (quillenABridgeFaceInnerRightObj n q G)) theta
      (eqToHom (congrArg F.obj
        (quillenABridgeFaceInnerLeftObj n q H))))).symm.trans
    ((CategoryTheory.comp_eqToHom_heq
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta)
        (congrArg F.obj
          (quillenABridgeFaceInnerLeftObj n q H))).trans
      (CategoryTheory.eqToHom_comp_heq theta
        (quillenABridgeFaceInnerRightObj n q G)))

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceInnerInner_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierFaceInnerInner F n q H G theta =
      quillenAMappingCarrierInner F n
        ((nerve C).δ q.castSucc.succ H)
        ((nerve D).δ q.castSucc.succ G)
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))) := by
  refine Sigma.ext (quillenAMappingCarrierFaceInnerInner_chain
    F n q H G theta) ?_
  apply quillenAProd_heq
  · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · exact (quillenAMappingCarrierFaceInnerInner_theta
      F n q H G theta).trans
      (quillenABridgeFaceInnerThetaHEq F n q H G theta).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeNatTrans_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left) :
    quillenABridgeNatTrans F
        ((nerve C).δ q.castSucc.succ H)
        ((nerve D).δ q.castSucc.succ G)
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))) =
      Functor.whiskerLeft
        (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor
        (quillenABridgeNatTrans F H G theta) := by
  change quillenABridgeNatTrans F
      (H.whiskerLeft
        (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor)
      (G.whiskerLeft
        (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor) _ = _
  simpa only [] using quillenABridgeNatTrans_whisker F
    (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor
    H G theta (quillenABridgeFaceInnerZero n q)
      (quillenABridgeFaceInnerLast n q)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgePrismChain_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ q.castSucc.succ
        (quillenABridgePrismChain F H G theta t) =
      quillenABridgePrismChain F
        ((nerve C).δ q.castSucc.succ H)
        ((nerve D).δ q.castSucc.succ G)
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H)))
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := by
  unfold quillenABridgePrismChain
  change (nerve D).map (SimplexCategory.δ q.castSucc.succ).op
        (quillenACylinderChain (quillenABridgeNatTrans F H G theta)
          (𝟭 (Fin (n + 2))) t) =
    quillenACylinderChain
      (quillenABridgeNatTrans F
        ((nerve C).δ q.castSucc.succ H)
        ((nerve D).δ q.castSucc.succ G)
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))))
      (𝟭 (Fin (n + 1)))
      ((Δ[1] : SSet.{max u v}).map
        (SimplexCategory.δ q.castSucc.succ).op t)
  rw [quillenACylinderChain_map,
    quillenABridgeNatTrans_δ_inner,
    quillenACylinderChain_precomp]
  rfl

private theorem quillenAMappingCarrierFaceInnerIndex_chain
    {C : Type u} [Category.{v} C] (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    (StrictOrdinaryWeightedBar.wFaceInnerIdx
      (CategoryBar.replUnit C) n q.castSucc.succ
        (quillenACastSucc_succ_ne_last q) p).1 =
      (nerve C).δ q.castSucc.succ p.1 := by
  rcases p with ⟨H, w⟩
  have hidx : StrictOmitDup.omitFinFunctor n q.castSucc.succ =
      (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor := by
    refine Functor.ext (fun k ↦ rfl) ?_
    intro a b f
    apply Subsingleton.elim
  change H.whiskerLeft (StrictOmitDup.omitFinFunctor n q.castSucc.succ) =
    H.whiskerLeft
      (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor
  rw [hidx]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (hG : G = (nerve D).map alpha.op y)
    (hGi : CategoryBar.barChain
        (quillenAMappingCarrierFaceInnerInner F n q H G theta) =
      (nerve D).map
        (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ q.castSucc.succ ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) ⟨H, PUnit.unit⟩,
          quillenAMappingCarrierFaceInnerInner F n q H G theta⟩ hGi =
      CategoryBar.barδ q.castSucc.succ
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H G theta⟩ hG) := by
  let Gy : ComposableArrows D (n + 1) := (nerve D).map alpha.op y
  change G = Gy at hG
  subst G
  let i : Fin (n + 2) := q.castSucc.succ
  let thetaI := eqToHom
      (quillenABridgeFaceInnerRightObj n q Gy) ≫ theta ≫
    F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))
  let rFace : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n i
          (quillenACastSucc_succ_ne_last q) ⟨H, PUnit.unit⟩,
      quillenAMappingCarrierFaceInnerInner F n q H Gy theta⟩
  let rCanonical : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨⟨(nerve C).δ i H, PUnit.unit⟩,
      quillenAMappingCarrierInner F n
        ((nerve C).δ i H) ((nerve D).δ i Gy) thetaI⟩
  have hRaw : rFace = rCanonical := by
    have hp : rFace.1 = rCanonical.1 := by
      refine Sigma.ext
        (quillenAMappingCarrierFaceInnerIndex_chain
          n q ⟨H, PUnit.unit⟩) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceInnerInner_eq_canonical F n q H Gy theta)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map (SimplexCategory.δ i ≫ alpha).op y := by
    rw [← hRaw]
    exact hGi
  have hReplace := quillenATargetFiberRetractionFromRaw_congr
    F y n (rfl : SimplexCategory.δ i ≫ alpha =
      SimplexCategory.δ i ≫ alpha) hRaw hGi hGCanonical
  calc
    _ = quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ i ≫ alpha)
        rCanonical hGCanonical := by
      simpa only [rFace, i] using hReplace
    _ = CategoryBar.barδ i
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F (n + 1) H Gy theta⟩
            (by rfl)) := by
      dsimp only [i]
      rw [CategoryBar.barδ_castSucc_succ_eq]
      unfold rCanonical quillenATargetFiberRetractionFromRaw
      dsimp only [thetaI, quillenAMappingCarrierInner]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Prod.ext
      · simp only [Functor.op_obj,
          SimplexCategoryGenRel.fromSimplexCategory_obj,
          CategoryBar.commaCoeffL_obj,
          SimplexCategory.comp_toOrderHom, homOfLE_leOfHom,
          CategoryBar.commaCoeffR_obj, Functor.id_obj,
          eqToHom_refl, id_eq, Category.id_comp, cast_eq]
        dsimp only [CategoryBar.barCoeffR]
        let K : Fin (n + 1) ⥤ Fin (n + 2) :=
          (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor
        let A : Fin (n + 2) ⥤ Fin (m + 1) :=
          alpha.toOrderHom.toFunctor
        let a : (0 : Fin (m + 1)) ⟶ A.obj (K.obj (Fin.last n)) :=
          homOfLE (Fin.zero_le _)
        have hIdx : A.obj (K.obj (Fin.last n)) =
            A.obj (Fin.last (n + 1)) :=
          congrArg A.obj (quillenABridgeFaceInnerLast n q)
        let eIdx : A.obj (K.obj (Fin.last n)) ⟶
            A.obj (Fin.last (n + 1)) := eqToHom hIdx
        let d : (0 : Fin (m + 1)) ⟶
            A.obj (Fin.last (n + 1)) := homOfLE (Fin.zero_le _)
        have hPath : y.map a ≫ y.map eIdx = y.map d := by
          rw [← y.map_comp]
          apply congrArg y.map
          apply Subsingleton.elim
        change y.map a ≫ eqToHom (congrArg y.obj hIdx) ≫ theta ≫
            F.map (𝟙 H.left) = y.map d ≫ theta
        rw [← eqToHom_map y hIdx, F.map_id]
        simp only [Category.comp_id]
        change y.map a ≫ y.map eIdx ≫ theta = y.map d ≫ theta
        simpa only [Category.assoc] using congrArg
          (fun r ↦ r ≫ theta) hPath
      · change (PUnit.unit : PUnit) = PUnit.unit
        rfl

private theorem quillenABridgeRawApp_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ q.castSucc.succ
        (quillenABridgePrismChain F H G theta t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q)
            (quillenAMappingIndex (n + 1) H))
        (quillenAMappingCarrierFaceInnerInner F n q H G theta)
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := by
  calc
    _ = quillenABridgePrismChain F
        ((nerve C).δ q.castSucc.succ H)
        ((nerve D).δ q.castSucc.succ G)
        (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H)))
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) :=
      quillenABridgePrismChain_δ_inner F n q H G theta t
    _ = _ := by
      unfold quillenABridgeRawApp
      apply quillenABridgePrismChain_congr F
      · exact (quillenAMappingCarrierFaceInnerIndex_chain n q
          (quillenAMappingIndex (n + 1) H)).symm
      · exact (quillenAMappingCarrierFaceInnerInner_chain
          F n q H G theta).symm
      · exact (quillenABridgeFaceInnerThetaHEq F n q H G theta).trans
          (quillenAMappingCarrierFaceInnerInner_theta
            F n q H G theta).symm
      · rfl

private theorem quillenABridgeRawApp_δ_inner_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ q.castSucc.succ
        (quillenABridgeRawApp F (n + 1) p x t) =
      quillenABridgeRawApp F n
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q) p)
        (quillenAMappingCarrierFaceInnerInnerOf F n q p x)
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := by
  rcases p with ⟨H, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenABridgeRawApp_δ_inner F n q H G theta t

private theorem quillenABridgeApp_δ_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (z : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).δ q.castSucc.succ
        (quillenABridgeApp F (n + 1) ⟨z, t⟩) =
      quillenABridgeApp F n
        ⟨(quillenAMappingCarrier F).δ q.castSucc.succ z,
          (Δ[1] : SSet.{max u v}).δ q.castSucc.succ t⟩ := by
  rcases hraw : quillenAMappingCarrierRawEquiv F (n + 1) z with
    ⟨p, x⟩
  have hz : z =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [hraw, quillenAMappingCarrierRawEquiv_wbarIncl]
  subst z
  unfold quillenABridgeApp quillenABridgeFromRaw
  rw [quillenAMappingCarrierRawEquiv_wbarIncl,
    quillenAMappingCarrierRawEquiv_δ_inner_of]
  exact quillenABridgeRawApp_δ_inner_of F n q p x t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierDegInner_chain
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    CategoryBar.barChain
        (quillenAMappingCarrierDegInner F n i H G theta) =
      (nerve D).σ i G := by
  unfold quillenAMappingCarrierDegInner
    quillenAMappingCarrierDegInnerOf
  let x := quillenAMappingCarrierInner F n H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.σ i).op x = CategoryBar.barσ i x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.σ i).op) x = CategoryBar.barσ i x
    rw [CategoryBar.categoryBar_map_σ]
    rfl
  dsimp only
  rw [hInnerMap]
  unfold StrictOrdinaryWeightedBar.wDegInnerComponent
  dsimp only [x, quillenAMappingCarrierInner]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierDegInner_theta
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    HEq (CategoryBar.barCoeffR
      (quillenAMappingCarrierDegInner F n i H G theta)) theta := by
  unfold quillenAMappingCarrierDegInner
    quillenAMappingCarrierDegInnerOf
  let x := quillenAMappingCarrierInner F n H G theta
  have hInnerMap :
      ((quillenAMappingDiagram F).obj H.left).map
          (SimplexCategory.σ i).op x = CategoryBar.barσ i x := by
    change ((CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (L := CategoryBar.unitCoeffL D)).map
        (SimplexCategory.σ i).op) x = CategoryBar.barσ i x
    rw [CategoryBar.categoryBar_map_σ]
    rfl
  dsimp only
  rw [hInnerMap]
  unfold StrictOrdinaryWeightedBar.wDegInnerComponent
  dsimp only [x, quillenAMappingCarrierInner]
  exact cast_heq _ _

private theorem quillenABridgeDegInnerZero (n : ℕ) (i : Fin (n + 1)) :
    (SimplexCategory.σ i).toOrderHom.toFunctor.obj 0 = 0 := by
  change i.predAbove 0 = 0
  exact Fin.predAbove_right_zero

private theorem quillenABridgeDegInnerLast (n : ℕ) (i : Fin (n + 1)) :
    (SimplexCategory.σ i).toOrderHom.toFunctor.obj (Fin.last (n + 1)) =
      Fin.last n := by
  change i.predAbove (Fin.last (n + 1)) = Fin.last n
  exact Fin.predAbove_right_last

private theorem quillenABridgeDegInnerLeftObj
    {C : Type u} [Category.{v} C] (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) :
    H.left = (H.whiskerLeft
      (SimplexCategory.σ i).toOrderHom.toFunctor).left := by
  change H.obj 0 = H.obj
    ((SimplexCategory.σ i).toOrderHom.toFunctor.obj 0)
  exact congrArg H.obj (quillenABridgeDegInnerZero n i).symm

private theorem quillenABridgeDegInnerRightObj
    {D : Type u} [Category.{v} D] (n : ℕ) (i : Fin (n + 1))
    (G : ComposableArrows D n) :
    (G.whiskerLeft (SimplexCategory.σ i).toOrderHom.toFunctor).right =
      G.right := by
  change G.obj ((SimplexCategory.σ i).toOrderHom.toFunctor.obj
      (Fin.last (n + 1))) = G.obj (Fin.last n)
  exact congrArg G.obj (quillenABridgeDegInnerLast n i)

private theorem quillenABridgeDegInnerThetaHEq
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    HEq (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
      F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))) theta := by
  rw [eqToHom_map]
  exact (heq_of_eq (Category.assoc
      (eqToHom (quillenABridgeDegInnerRightObj n i G)) theta
      (eqToHom (congrArg F.obj
        (quillenABridgeDegInnerLeftObj n i H))))).symm.trans
    ((CategoryTheory.comp_eqToHom_heq
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta)
        (congrArg F.obj
          (quillenABridgeDegInnerLeftObj n i H))).trans
      (CategoryTheory.eqToHom_comp_heq theta
        (quillenABridgeDegInnerRightObj n i G)))

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierDegInner_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    quillenAMappingCarrierDegInner F n i H G theta =
      quillenAMappingCarrierInner F (n + 1)
        ((nerve C).σ i H) ((nerve D).σ i G)
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))) := by
  refine Sigma.ext (quillenAMappingCarrierDegInner_chain
    F n i H G theta) ?_
  apply quillenAProd_heq
  · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · exact (quillenAMappingCarrierDegInner_theta F n i H G theta).trans
      (quillenABridgeDegInnerThetaHEq F n i H G theta).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgeNatTrans_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left) :
    quillenABridgeNatTrans F ((nerve C).σ i H) ((nerve D).σ i G)
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))) =
      Functor.whiskerLeft (SimplexCategory.σ i).toOrderHom.toFunctor
        (quillenABridgeNatTrans F H G theta) := by
  change quillenABridgeNatTrans F
      (H.whiskerLeft (SimplexCategory.σ i).toOrderHom.toFunctor)
      (G.whiskerLeft (SimplexCategory.σ i).toOrderHom.toFunctor) _ = _
  simpa only [] using quillenABridgeNatTrans_whisker F
    (SimplexCategory.σ i).toOrderHom.toFunctor H G theta
      (quillenABridgeDegInnerZero n i)
      (quillenABridgeDegInnerLast n i)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenABridgePrismChain_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (nerve D).σ i (quillenABridgePrismChain F H G theta t) =
      quillenABridgePrismChain F ((nerve C).σ i H)
        ((nerve D).σ i G)
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H)))
        ((Δ[1] : SSet.{max u v}).σ i t) := by
  unfold quillenABridgePrismChain
  change (nerve D).map (SimplexCategory.σ i).op
        (quillenACylinderChain (quillenABridgeNatTrans F H G theta)
          (𝟭 (Fin (n + 1))) t) =
    quillenACylinderChain
      (quillenABridgeNatTrans F ((nerve C).σ i H)
        ((nerve D).σ i G)
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))))
      (𝟭 (Fin (n + 2)))
      ((Δ[1] : SSet.{max u v}).map (SimplexCategory.σ i).op t)
  rw [quillenACylinderChain_map, quillenABridgeNatTrans_σ,
    quillenACylinderChain_precomp]
  rfl

private theorem quillenAMappingCarrierDegIndex_chain
    {C : Type u} [Category.{v} C] (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n) :
    (StrictOrdinaryWeightedBar.wDegInnerIdx
      (CategoryBar.replUnit C) n i p).1 = (nerve C).σ i p.1 := by
  rcases p with ⟨H, w⟩
  have hidx : StrictOmitDup.dupFinFunctor n i =
      (SimplexCategory.σ i).toOrderHom.toFunctor := by
    refine Functor.ext (fun k ↦ rfl) ?_
    intro a b f
    apply Subsingleton.elim
  change H.whiskerLeft (StrictOmitDup.dupFinFunctor n i) =
    H.whiskerLeft (SimplexCategory.σ i).toOrderHom.toFunctor
  rw [hidx]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (i : Fin (n + 1))
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (hG : G = (nerve D).map alpha.op y)
    (hGs : CategoryBar.barChain
        (quillenAMappingCarrierDegInner F n i H G theta) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y (n + 1)
        (SimplexCategory.σ i ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i ⟨H, PUnit.unit⟩,
          quillenAMappingCarrierDegInner F n i H G theta⟩ hGs =
      CategoryBar.barσ i
        (quillenATargetFiberRetractionFromRaw F y n
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F n H G theta⟩ hG) := by
  let Gy : ComposableArrows D n := (nerve D).map alpha.op y
  change G = Gy at hG
  subst G
  let K : Fin (n + 2) ⥤ Fin (n + 1) :=
    (SimplexCategory.σ i).toOrderHom.toFunctor
  let thetaS := eqToHom (quillenABridgeDegInnerRightObj n i Gy) ≫
    theta ≫ F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))
  let rFace : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌) :=
    ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i ⟨H, PUnit.unit⟩,
      quillenAMappingCarrierDegInner F n i H Gy theta⟩
  let rCanonical : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌) :=
    ⟨⟨(nerve C).σ i H, PUnit.unit⟩,
      quillenAMappingCarrierInner F (n + 1)
        ((nerve C).σ i H) ((nerve D).σ i Gy) thetaS⟩
  have hRaw : rFace = rCanonical := by
    have hp : rFace.1 = rCanonical.1 := by
      refine Sigma.ext
        (quillenAMappingCarrierDegIndex_chain n i ⟨H, PUnit.unit⟩) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierDegInner_eq_canonical F n i H Gy theta)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y := by
    rw [← hRaw]
    exact hGs
  have hReplace := quillenATargetFiberRetractionFromRaw_congr
    F y (n + 1) (rfl : SimplexCategory.σ i ≫ alpha =
      SimplexCategory.σ i ≫ alpha) hRaw hGs hGCanonical
  calc
    _ = quillenATargetFiberRetractionFromRaw F y (n + 1)
        (SimplexCategory.σ i ≫ alpha)
        rCanonical hGCanonical := by
      simpa only [rFace] using hReplace
    _ = CategoryBar.barσ i
        (quillenATargetFiberRetractionFromRaw F y n
          alpha ⟨⟨H, PUnit.unit⟩,
            quillenAMappingCarrierInner F n H Gy theta⟩
            (by rfl)) := by
      unfold rCanonical quillenATargetFiberRetractionFromRaw
      dsimp only [thetaS, quillenAMappingCarrierInner,
        CategoryBar.barσ]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Prod.ext
      · simp only [Functor.op_obj,
          SimplexCategoryGenRel.fromSimplexCategory_obj,
          CategoryBar.commaCoeffL_obj,
          SimplexCategory.comp_toOrderHom, homOfLE_leOfHom,
          CategoryBar.commaCoeffR_obj, Functor.id_obj,
          eqToHom_refl, id_eq, Category.id_comp, cast_eq]
        dsimp only [CategoryBar.barCoeffR]
        let A : Fin (n + 1) ⥤ Fin (m + 1) :=
          alpha.toOrderHom.toFunctor
        let a : (0 : Fin (m + 1)) ⟶ A.obj (K.obj (Fin.last (n + 1))) :=
          homOfLE (Fin.zero_le _)
        have hIdx : A.obj (K.obj (Fin.last (n + 1))) =
            A.obj (Fin.last n) :=
          congrArg A.obj (quillenABridgeDegInnerLast n i)
        let eIdx : A.obj (K.obj (Fin.last (n + 1))) ⟶
            A.obj (Fin.last n) := eqToHom hIdx
        let d : (0 : Fin (m + 1)) ⟶
            A.obj (Fin.last n) := homOfLE (Fin.zero_le _)
        have hPath : y.map a ≫ y.map eIdx = y.map d := by
          rw [← y.map_comp]
          apply congrArg y.map
          apply Subsingleton.elim
        change y.map a ≫ eqToHom (congrArg y.obj hIdx) ≫ theta ≫
            F.map (𝟙 H.left) = y.map d ≫ theta
        rw [← eqToHom_map y hIdx, F.map_id]
        simp only [Category.comp_id]
        change y.map a ≫ y.map eIdx ≫ theta = y.map d ≫ theta
        simpa only [Category.assoc] using congrArg
          (fun r ↦ r ≫ theta) hPath
      · change (PUnit.unit : PUnit) = PUnit.unit
        rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_zero_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hG0 : CategoryBar.barChain
        (quillenAMappingCarrierFaceZeroInnerOf F n p x) =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceZeroInnerOf F n p x⟩ hG0 =
      CategoryBar.barδ 0
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨p, x⟩ hG) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenATargetFiberRetractionFromRaw_delta_zero
    F y n alpha H G theta hG hG0

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_last_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGl : CategoryBar.barChain
        (quillenAMappingCarrierFaceLastInnerOf F n p x) =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceLastInnerOf F n p x⟩ hGl =
      CategoryBar.barδ (Fin.last (n + 1))
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨p, x⟩ hG) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenATargetFiberRetractionFromRaw_delta_last
    F y n alpha H G theta hG hGl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_delta_inner_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (alpha : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGi : CategoryBar.barChain
        (quillenAMappingCarrierFaceInnerInnerOf F n q p x) =
      (nerve D).map
        (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y n
        (SimplexCategory.δ q.castSucc.succ ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) p,
          quillenAMappingCarrierFaceInnerInnerOf F n q p x⟩ hGi =
      CategoryBar.barδ q.castSucc.succ
        (quillenATargetFiberRetractionFromRaw F y (n + 1)
          alpha ⟨p, x⟩ hG) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenATargetFiberRetractionFromRaw_delta_inner
    F y n q alpha H G theta hG hGi

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionFromRaw_sigma_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (i : Fin (n + 1))
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGs : CategoryBar.barChain
        (quillenAMappingCarrierDegInnerOf F n i p x) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y) :
    quillenATargetFiberRetractionFromRaw F y (n + 1)
        (SimplexCategory.σ i ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i p,
          quillenAMappingCarrierDegInnerOf F n i p x⟩ hGs =
      CategoryBar.barσ i
        (quillenATargetFiberRetractionFromRaw F y n
          alpha ⟨p, x⟩ hG) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenATargetFiberRetractionFromRaw_sigma
    F y n i alpha H G theta hG hGs

private theorem quillenABridgeRawApp_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n) (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (nerve D).σ i (quillenABridgePrismChain F H G theta t) =
      quillenABridgeRawApp F (n + 1)
        (StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i (quillenAMappingIndex n H))
        (quillenAMappingCarrierDegInner F n i H G theta)
        ((Δ[1] : SSet.{max u v}).σ i t) := by
  calc
    _ = quillenABridgePrismChain F ((nerve C).σ i H)
        ((nerve D).σ i G)
        (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H)))
        ((Δ[1] : SSet.{max u v}).σ i t) :=
      quillenABridgePrismChain_σ F n i H G theta t
    _ = _ := by
      unfold quillenABridgeRawApp
      apply quillenABridgePrismChain_congr F
      · exact (quillenAMappingCarrierDegIndex_chain n i
          (quillenAMappingIndex n H)).symm
      · exact (quillenAMappingCarrierDegInner_chain
          F n i H G theta).symm
      · exact (quillenABridgeDegInnerThetaHEq F n i H G theta).trans
          (quillenAMappingCarrierDegInner_theta F n i H G theta).symm
      · rfl

private theorem quillenABridgeRawApp_σ_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (nerve D).σ i (quillenABridgeRawApp F n p x t) =
      quillenABridgeRawApp F (n + 1)
        (StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i p)
        (quillenAMappingCarrierDegInnerOf F n i p x)
        ((Δ[1] : SSet.{max u v}).σ i t) := by
  rcases p with ⟨H, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenABridgeRawApp_σ F n i H G theta t

private theorem quillenABridgeApp_σ
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌))
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (nerve D).σ i (quillenABridgeApp F n ⟨z, t⟩) =
      quillenABridgeApp F (n + 1)
        ⟨(quillenAMappingCarrier F).σ i z,
          (Δ[1] : SSet.{max u v}).σ i t⟩ := by
  rcases hraw : quillenAMappingCarrierRawEquiv F n z with ⟨p, x⟩
  have hz : z =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F) n p).app
          (op ⦋n⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F n).injective
    rw [hraw, quillenAMappingCarrierRawEquiv_wbarIncl]
  subst z
  unfold quillenABridgeApp quillenABridgeFromRaw
  rw [quillenAMappingCarrierRawEquiv_wbarIncl,
    quillenAMappingCarrierRawEquiv_σ_of]
  exact quillenABridgeRawApp_σ_of F n i p x t

private noncomputable def quillenABridgeAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (a : SimplexCategoryᵒᵖ) :
    ((quillenAMappingCarrier F) ⊗
      (Δ[1] : SSet.{max u v})).obj a ⟶ (nerve D).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenABridgeApp F n)

@[simp]
private theorem quillenABridgeAppNat_mk
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) :
    quillenABridgeAppNat F (op ⦋n⦌) = ↾(quillenABridgeApp F n) := by
  rfl

private noncomputable def quillenABridgeMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    quillenAMappingCarrier F ⊗ (Δ[1] : SSet.{max u v}) ⟶ nerve D where
  app a := quillenABridgeAppNat F a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      ((quillenAMappingCarrier F) ⊗
          (Δ[1] : SSet.{max u v})).map f.op ≫
          quillenABridgeAppNat F (op A) =
        quillenABridgeAppNat F (op B) ≫ (nerve D).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      rcases z with ⟨z, t⟩
      change quillenABridgeApp F n
          ⟨(quillenAMappingCarrier F).δ i z,
            (Δ[1] : SSet.{max u v}).δ i t⟩ =
        (nerve D).δ i (quillenABridgeApp F (n + 1) ⟨z, t⟩)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact (quillenABridgeApp_δ_zero F n z t).symm
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact (quillenABridgeApp_δ_last F n z t).symm
        · exact (quillenABridgeApp_δ_inner F n q z t).symm
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      rcases z with ⟨z, t⟩
      change quillenABridgeApp F (n + 1)
          ⟨(quillenAMappingCarrier F).σ i z,
            (Δ[1] : SSet.{max u v}).σ i t⟩ =
        (nerve D).σ i (quillenABridgeApp F n ⟨z, t⟩)
      exact (quillenABridgeApp_σ F n i z t).symm
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

private theorem quillenABridgeApp_ι₀
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    quillenABridgeApp F n
        (SSet.ι₀.app (op ⦋n⦌) z) =
      (quillenATarget F).app (op ⦋n⦌) z := by
  rcases h : quillenAMappingCarrierObjEquiv F n z with
    ⟨H, G, theta⟩
  have hz : z = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [h, quillenAMappingCarrierObjEquiv_incl]
  subst z
  rw [quillenATarget_carrierIncl]
  change quillenABridgeApp F n
      ⟨quillenAMappingCarrierIncl F n H G theta,
        (SSet.ι₀.app (op ⦋n⦌)
          (quillenAMappingCarrierIncl F n H G theta)).2⟩ = G
  rw [quillenABridgeApp_incl]
  apply quillenABridgePrismChain_of_const_zero
  rfl

private theorem quillenABridgeApp_ι₁
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (z : (quillenAMappingCarrier F).obj (op ⦋n⦌)) :
    quillenABridgeApp F n
        (SSet.ι₁.app (op ⦋n⦌) z) =
      ((quillenASource F ≫ nerveMap F).app (op ⦋n⦌)) z := by
  rcases h : quillenAMappingCarrierObjEquiv F n z with
    ⟨H, G, theta⟩
  have hz : z = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [h, quillenAMappingCarrierObjEquiv_incl]
  subst z
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    quillenASource_carrierIncl]
  change quillenABridgeApp F n
      ⟨quillenAMappingCarrierIncl F n H G theta,
        (SSet.ι₁.app (op ⦋n⦌)
          (quillenAMappingCarrierIncl F n H G theta)).2⟩ =
    (F.mapComposableArrows n).obj H
  rw [quillenABridgeApp_incl]
  apply quillenABridgePrismChain_of_const_one
  rfl

private theorem quillenABridgeMap_h₀
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    SSet.ι₀ ≫ quillenABridgeMap F = quillenATarget F := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenABridgeApp_ι₀ F n z

private theorem quillenABridgeMap_h₁
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    SSet.ι₁ ≫ quillenABridgeMap F =
      quillenASource F ≫ nerveMap F := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenABridgeApp_ι₁ F n z

private noncomputable def quillenAMappingHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    SSet.Homotopy (quillenATarget F)
      (quillenASource F ≫ nerveMap F) where
  h := quillenABridgeMap F
  h₀ := quillenABridgeMap_h₀ F
  h₁ := quillenABridgeMap_h₁ F
  rel := by
    ext a z
    exact z.1.2.elim

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionAppRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRetractionAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op z) =
      (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
          (quillenATargetFiberRetractionAppRaw F y (n + 1) z) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n + 1⦌) z
  let d0 := SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
    ((SSet.leftFiber (quillenATarget F) y).map k z)
  have hd : quillenATargetFiberDecodedMap F y k d = d0 :=
    quillenATargetFiberDecodedMap_objEquiv F y k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let x := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {a : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
        (quillenATarget F).app (op ⦋n + 1⦌) a.1 =
          (nerve D).map a.2.op y} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenATargetFiberRetractionDecoded F y n d0 =
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).map k
        (quillenATargetFiberRetractionDecoded F y (n + 1) d)
  calc
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k d) :=
      congrArg (quillenATargetFiberRetractionDecoded F y n) hd.symm
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k dIncl) :=
      congrArg (fun e ↦ quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k e)) hD
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_zero_of F n p x
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ (0 : Fin (n + 2))).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
      let e := quillenATargetFiberDecodedMap F y k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hGFace : CategoryBar.barChain rFace.2 =
          (nerve D).map alphaFace.op y :=
        (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
      let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceZeroInnerOf F n p x⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ (0 : Fin (n + 2))).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = rExpected
        exact hRaw
      have hGExpected : CategoryBar.barChain rExpected.2 =
          (nerve D).map alphaFace.op y := by
        rw [← hRawE]
        exact hGFace
      have hReplace := quillenATargetFiberRetractionFromRaw_congr
        F y n (rfl : alphaFace = alphaFace)
          hRawE hGFace hGExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, x⟩
      have hTopRaw : rTop = rTopExpected := by
        exact quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p x
      have hGTop : CategoryBar.barChain rTop.2 =
          (nerve D).map dIncl.1.2.op y :=
        (quillenATarget_eq_raw_chain F (n + 1) dIncl.1.1).symm.trans
          dIncl.2
      have hGTopExpected : CategoryBar.barChain rTopExpected.2 =
          (nerve D).map dIncl.1.2.op y := by
        rw [← hTopRaw]
        exact hGTop
      have hTopReplace := quillenATargetFiberRetractionFromRaw_congr
        F y (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hGTop hGTopExpected
      unfold quillenATargetFiberRetractionDecoded
      unfold quillenATargetFiberDecodedMap
      dsimp only [k, dIncl]
      rw [CategoryBar.simplicialReplacement_map_δ]
      change quillenATargetFiberRetractionFromRaw F y n
          alphaFace rFace hGFace =
        CategoryBar.barδ 0
          (quillenATargetFiberRetractionFromRaw F y (n + 1)
            dIncl.1.2 rTop hGTop)
      calc
        _ = quillenATargetFiberRetractionFromRaw F y n
            alphaFace rExpected hGExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ 0
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTopExpected hGTopExpected) := by
          exact quillenATargetFiberRetractionFromRaw_delta_zero_of
            F y n dIncl.1.2 p x hGTopExpected hGExpected
        _ = CategoryBar.barδ 0
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTop hGTop) := by
          exact congrArg (CategoryBar.barδ
            (R := CategoryBar.replUnit C)
            (L := CategoryBar.commaCoeffL F (y.obj 0))
              (0 : Fin (n + 2))) hTopReplace.symm
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) d) :=
      congrArg ((CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k)
        (congrArg (quillenATargetFiberRetractionDecoded F y (n + 1)) hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionAppRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRetractionAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y).map
          (SimplexCategory.δ (Fin.last (n + 1))).op z) =
      (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map
          (SimplexCategory.δ (Fin.last (n + 1))).op
          (quillenATargetFiberRetractionAppRaw F y (n + 1) z) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n + 1⦌) z
  let d0 := SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
    ((SSet.leftFiber (quillenATarget F) y).map k z)
  have hd : quillenATargetFiberDecodedMap F y k d = d0 :=
    quillenATargetFiberDecodedMap_objEquiv F y k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let x := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {a : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
        (quillenATarget F).app (op ⦋n + 1⦌) a.1 =
          (nerve D).map a.2.op y} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenATargetFiberRetractionDecoded F y n d0 =
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).map k
        (quillenATargetFiberRetractionDecoded F y (n + 1) d)
  calc
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k d) :=
      congrArg (quillenATargetFiberRetractionDecoded F y n) hd.symm
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k dIncl) :=
      congrArg (fun e ↦ quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k e)) hD
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_last_of F n p x
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ (Fin.last (n + 1))).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
      let e := quillenATargetFiberDecodedMap F y k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hGFace : CategoryBar.barChain rFace.2 =
          (nerve D).map alphaFace.op y :=
        (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
      let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceLastInnerOf F n p x⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ (Fin.last (n + 1))).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = rExpected
        exact hRaw
      have hGExpected : CategoryBar.barChain rExpected.2 =
          (nerve D).map alphaFace.op y := by
        rw [← hRawE]
        exact hGFace
      have hReplace := quillenATargetFiberRetractionFromRaw_congr
        F y n (rfl : alphaFace = alphaFace)
          hRawE hGFace hGExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, x⟩
      have hTopRaw : rTop = rTopExpected := by
        exact quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p x
      have hGTop : CategoryBar.barChain rTop.2 =
          (nerve D).map dIncl.1.2.op y :=
        (quillenATarget_eq_raw_chain F (n + 1) dIncl.1.1).symm.trans
          dIncl.2
      have hGTopExpected : CategoryBar.barChain rTopExpected.2 =
          (nerve D).map dIncl.1.2.op y := by
        rw [← hTopRaw]
        exact hGTop
      have hTopReplace := quillenATargetFiberRetractionFromRaw_congr
        F y (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hGTop hGTopExpected
      unfold quillenATargetFiberRetractionDecoded
      unfold quillenATargetFiberDecodedMap
      dsimp only [k, dIncl]
      rw [CategoryBar.simplicialReplacement_map_δ]
      change quillenATargetFiberRetractionFromRaw F y n
          alphaFace rFace hGFace =
        CategoryBar.barδ (Fin.last (n + 1))
          (quillenATargetFiberRetractionFromRaw F y (n + 1)
            dIncl.1.2 rTop hGTop)
      calc
        _ = quillenATargetFiberRetractionFromRaw F y n
            alphaFace rExpected hGExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ (Fin.last (n + 1))
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTopExpected hGTopExpected) := by
          exact quillenATargetFiberRetractionFromRaw_delta_last_of
            F y n dIncl.1.2 p x hGTopExpected hGExpected
        _ = CategoryBar.barδ (Fin.last (n + 1))
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTop hGTop) := by
          exact congrArg (CategoryBar.barδ
            (R := CategoryBar.replUnit C)
            (L := CategoryBar.commaCoeffL F (y.obj 0))
              (Fin.last (n + 1))) hTopReplace.symm
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) d) :=
      congrArg ((CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k)
        (congrArg (quillenATargetFiberRetractionDecoded F y (n + 1)) hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionAppRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRetractionAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y).map
          (SimplexCategory.δ q.castSucc.succ).op z) =
      (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map
          (SimplexCategory.δ q.castSucc.succ).op
          (quillenATargetFiberRetractionAppRaw F y (n + 1) z) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n + 1⦌) z
  let d0 := SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
    ((SSet.leftFiber (quillenATarget F) y).map k z)
  have hd : quillenATargetFiberDecodedMap F y k d = d0 :=
    quillenATargetFiberDecodedMap_objEquiv F y k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let x := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {a : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
        (quillenATarget F).app (op ⦋n + 1⦌) a.1 =
          (nerve D).map a.2.op y} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenATargetFiberRetractionDecoded F y n d0 =
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).map k
        (quillenATargetFiberRetractionDecoded F y (n + 1) d)
  calc
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k d) :=
      congrArg (quillenATargetFiberRetractionDecoded F y n) hd.symm
    _ = quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k dIncl) :=
      congrArg (fun e ↦ quillenATargetFiberRetractionDecoded F y n
        (quillenATargetFiberDecodedMap F y k e)) hD
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_inner_of F n q p x
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ q.castSucc.succ).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
      let e := quillenATargetFiberDecodedMap F y k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hGFace : CategoryBar.barChain rFace.2 =
          (nerve D).map alphaFace.op y :=
        (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
      let rExpected : Σ s : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj s.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) p,
          quillenAMappingCarrierFaceInnerInnerOf F n q p x⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map
            (SimplexCategory.δ q.castSucc.succ).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) x)) = rExpected
        exact hRaw
      have hGExpected : CategoryBar.barChain rExpected.2 =
          (nerve D).map alphaFace.op y := by
        rw [← hRawE]
        exact hGFace
      have hReplace := quillenATargetFiberRetractionFromRaw_congr
        F y n (rfl : alphaFace = alphaFace)
          hRawE hGFace hGExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ s : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj s.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, x⟩
      have hTopRaw : rTop = rTopExpected := by
        exact quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p x
      have hGTop : CategoryBar.barChain rTop.2 =
          (nerve D).map dIncl.1.2.op y :=
        (quillenATarget_eq_raw_chain F (n + 1) dIncl.1.1).symm.trans
          dIncl.2
      have hGTopExpected : CategoryBar.barChain rTopExpected.2 =
          (nerve D).map dIncl.1.2.op y := by
        rw [← hTopRaw]
        exact hGTop
      have hTopReplace := quillenATargetFiberRetractionFromRaw_congr
        F y (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hGTop hGTopExpected
      unfold quillenATargetFiberRetractionDecoded
      unfold quillenATargetFiberDecodedMap
      dsimp only [k, dIncl]
      rw [CategoryBar.simplicialReplacement_map_δ]
      change quillenATargetFiberRetractionFromRaw F y n
          alphaFace rFace hGFace =
        CategoryBar.barδ q.castSucc.succ
          (quillenATargetFiberRetractionFromRaw F y (n + 1)
            dIncl.1.2 rTop hGTop)
      calc
        _ = quillenATargetFiberRetractionFromRaw F y n
            alphaFace rExpected hGExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ q.castSucc.succ
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTopExpected hGTopExpected) := by
          exact quillenATargetFiberRetractionFromRaw_delta_inner_of
            F y n q dIncl.1.2 p x hGTopExpected hGExpected
        _ = CategoryBar.barδ q.castSucc.succ
            (quillenATargetFiberRetractionFromRaw F y (n + 1)
              dIncl.1.2 rTop hGTop) := by
          exact congrArg (CategoryBar.barδ
            (R := CategoryBar.replUnit C)
            (L := CategoryBar.commaCoeffL F (y.obj 0))
              q.castSucc.succ) hTopReplace.symm
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y (n + 1) d) :=
      congrArg ((CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k)
        (congrArg (quillenATargetFiberRetractionDecoded F y (n + 1)) hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRetractionAppRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (i : Fin (n + 1))
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    quillenATargetFiberRetractionAppRaw F y (n + 1)
        ((SSet.leftFiber (quillenATarget F) y).map
          (SimplexCategory.σ i).op z) =
      (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map
          (SimplexCategory.σ i).op
          (quillenATargetFiberRetractionAppRaw F y n z) := by
  let k := (SimplexCategory.σ i).op
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌) z
  let d1 := SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n + 1⦌)
    ((SSet.leftFiber (quillenATarget F) y).map k z)
  have hd : quillenATargetFiberDecodedMap F y k d = d1 :=
    quillenATargetFiberDecodedMap_objEquiv F y k z
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  let p := r.1
  let x := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F n).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {a : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
        (quillenATarget F).app (op ⦋n⦌) a.1 =
          (nerve D).map a.2.op y} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) x, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenATargetFiberRetractionDecoded F y (n + 1) d1 =
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).map k
        (quillenATargetFiberRetractionDecoded F y n d)
  calc
    _ = quillenATargetFiberRetractionDecoded F y (n + 1)
        (quillenATargetFiberDecodedMap F y k d) :=
      congrArg (quillenATargetFiberRetractionDecoded F y (n + 1)) hd.symm
    _ = quillenATargetFiberRetractionDecoded F y (n + 1)
        (quillenATargetFiberDecodedMap F y k dIncl) :=
      congrArg (fun e ↦ quillenATargetFiberRetractionDecoded F y (n + 1)
        (quillenATargetFiberDecodedMap F y k e)) hD
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y n dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_σ_of F n i p x
      change quillenAMappingCarrierRawEquiv F (n + 1)
          ((quillenAMappingCarrier F).map (SimplexCategory.σ i).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                n p).app (op ⦋n⦌) x)) = _ at hRaw
      let e := quillenATargetFiberDecodedMap F y k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F (n + 1) e.1.1
      let alphaFace := e.1.2
      have hGFace : CategoryBar.barChain rFace.2 =
          (nerve D).map alphaFace.op y :=
        (quillenATarget_eq_raw_chain F (n + 1) e.1.1).symm.trans e.2
      let rExpected : Σ s : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj s.1.left).obj (op ⦋n + 1⦌) :=
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i p,
          quillenAMappingCarrierDegInnerOf F n i p x⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F (n + 1)
          ((quillenAMappingCarrier F).map (SimplexCategory.σ i).op
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                n p).app (op ⦋n⦌) x)) = rExpected
        exact hRaw
      have hGExpected : CategoryBar.barChain rExpected.2 =
          (nerve D).map alphaFace.op y := by
        rw [← hRawE]
        exact hGFace
      have hReplace := quillenATargetFiberRetractionFromRaw_congr
        F y (n + 1) (rfl : alphaFace = alphaFace)
          hRawE hGFace hGExpected
      let rTop := quillenAMappingCarrierRawEquiv F n dIncl.1.1
      let rTopExpected : Σ s : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj s.1.left).obj (op ⦋n⦌) :=
        ⟨p, x⟩
      have hTopRaw : rTop = rTopExpected := by
        exact quillenAMappingCarrierRawEquiv_wbarIncl F n p x
      have hGTop : CategoryBar.barChain rTop.2 =
          (nerve D).map dIncl.1.2.op y :=
        (quillenATarget_eq_raw_chain F n dIncl.1.1).symm.trans dIncl.2
      have hGTopExpected : CategoryBar.barChain rTopExpected.2 =
          (nerve D).map dIncl.1.2.op y := by
        rw [← hTopRaw]
        exact hGTop
      have hTopReplace := quillenATargetFiberRetractionFromRaw_congr
        F y n (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hGTop hGTopExpected
      unfold quillenATargetFiberRetractionDecoded
      unfold quillenATargetFiberDecodedMap
      dsimp only [k, dIncl]
      rw [CategoryBar.simplicialReplacement_map_σ]
      change quillenATargetFiberRetractionFromRaw F y (n + 1)
          alphaFace rFace hGFace =
        CategoryBar.barσ i
          (quillenATargetFiberRetractionFromRaw F y n
            dIncl.1.2 rTop hGTop)
      calc
        _ = quillenATargetFiberRetractionFromRaw F y (n + 1)
            alphaFace rExpected hGExpected := by
          simpa only using hReplace
        _ = CategoryBar.barσ i
            (quillenATargetFiberRetractionFromRaw F y n
              dIncl.1.2 rTopExpected hGTopExpected) := by
          exact quillenATargetFiberRetractionFromRaw_sigma_of
            F y n i dIncl.1.2 p x hGTopExpected hGExpected
        _ = CategoryBar.barσ i
            (quillenATargetFiberRetractionFromRaw F y n
              dIncl.1.2 rTop hGTop) := by
          exact congrArg (CategoryBar.barσ
            (R := CategoryBar.replUnit C)
            (L := CategoryBar.commaCoeffL F (y.obj 0)) i)
              hTopReplace.symm
    _ = (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k
          (quillenATargetFiberRetractionDecoded F y n d) :=
      congrArg ((CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).map k)
        (congrArg (quillenATargetFiberRetractionDecoded F y n) hD.symm)

private noncomputable def quillenATargetFiberRetractionAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    (a : SimplexCategoryᵒᵖ) :
    (SSet.leftFiber (quillenATarget F) y).obj a ⟶
      (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenATargetFiberRetractionAppRaw F y n)

@[simp]
private theorem quillenATargetFiberRetractionAppNat_mk
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) :
    quillenATargetFiberRetractionAppNat F y (op ⦋n⦌) =
      ↾(quillenATargetFiberRetractionAppRaw F y n) := by
  rfl

private noncomputable def quillenATargetFiberRetraction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    SSet.leftFiber (quillenATarget F) y ⟶
      CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0)) where
  app a := quillenATargetFiberRetractionAppNat F y a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      (SSet.leftFiber (quillenATarget F) y).map f.op ≫
          quillenATargetFiberRetractionAppNat F y (op A) =
        quillenATargetFiberRetractionAppNat F y (op B) ≫
          (CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberRetractionAppRaw F y n
          ((SSet.leftFiber (quillenATarget F) y).δ i z) =
        (CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).δ i
            (quillenATargetFiberRetractionAppRaw F y (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact quillenATargetFiberRetractionAppRaw_delta_zero
          F y n z
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact quillenATargetFiberRetractionAppRaw_delta_last
            F y n z
        · exact quillenATargetFiberRetractionAppRaw_delta_inner
            F y n q z
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberRetractionAppRaw F y (n + 1)
          ((SSet.leftFiber (quillenATarget F) y).σ i z) =
        (CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).σ i
            (quillenATargetFiberRetractionAppRaw F y n z)
      exact quillenATargetFiberRetractionAppRaw_sigma F y n i z
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

private noncomputable def quillenASourceFiberRetractionPacket
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (T : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left)
    (hT : T.1 = x.whiskerLeft alpha.toOrderHom.toFunctor) :
    CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n := by
  let R : Σ G : ComposableArrows D n,
      ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right) :=
    quillenASourceFiberRetractionFromTriple F x T alpha hT
  exact ⟨R.1, ULift.up PUnit.unit, R.2.2⟩

private noncomputable def quillenASourceFiberRetractionFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hH : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor) :
    CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n := by
  let T := quillenAMappingCarrierRawToTriple F n r
  have hT : T.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := by
    change r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor
    exact hH
  exact quillenASourceFiberRetractionPacket F x n alpha T hT

private theorem quillenASourceFiberRetractionFromRaw_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    {alpha alpha' : ⦋n⦌ ⟶ ⦋m⦌}
    {r r' : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)}
    (ha : alpha = alpha') (hr : r = r')
    (hH : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH' : r'.1.1 = x.whiskerLeft alpha'.toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x n alpha r hH =
      quillenASourceFiberRetractionFromRaw F x n alpha' r' hH' := by
  cases ha
  cases hr
  rfl

private theorem quillenASourceFiberRetractionFromRaw_eq_triple
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hH : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (T : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left)
    (hT : quillenAMappingCarrierRawToTriple F n r = T)
    (hHT : T.1 = x.whiskerLeft alpha.toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x n alpha r hH =
      quillenASourceFiberRetractionPacket F x n alpha T hHT := by
  unfold quillenASourceFiberRetractionFromRaw
  have hRaw : (quillenAMappingCarrierRawToTriple F n r).1 =
      x.whiskerLeft alpha.toOrderHom.toFunctor := by
    change r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor
    exact hH
  change quillenASourceFiberRetractionPacket F x n alpha
      (quillenAMappingCarrierRawToTriple F n r) hRaw =
    quillenASourceFiberRetractionPacket F x n alpha T hHT
  cases hT
  have hp : hRaw = hHT := Subsingleton.elim _ _
  cases hp
  rfl

private theorem quillenAMappingCarrierRawToTriple_apply_p4
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawToTriple F n ⟨p, z⟩ =
      ⟨p.1, CategoryBar.barChain z, CategoryBar.barCoeffR z⟩ := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceLastTripleOf_p4
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawToTriple F n
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceLastInnerOf F n p z⟩ =
      ⟨SrepBridge.srepDropLast p.1,
        SrepBridge.srepDropLast (CategoryBar.barChain z),
        (CategoryBar.barChain z).map' n (n + 1) ≫
          CategoryBar.barCoeffR z⟩ := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  unfold quillenAMappingCarrierRawToTriple
  change (⟨(StrictOrdinaryWeightedBar.wFaceLastIdx
      (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩).1,
    CategoryBar.barChain
      (quillenAMappingCarrierFaceLastInner F n H G theta),
    CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceLastInner F n H G theta)⟩ :
      Σ H : ComposableArrows C n,
        Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left) =
    ⟨SrepBridge.srepDropLast H, SrepBridge.srepDropLast G,
      G.map' n (n + 1) ≫ theta⟩
  refine Sigma.ext ?_ ?_
  · change (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩).1 =
      SrepBridge.srepDropLast H
    rfl
  apply heq_of_eq
  apply Sigma.ext
  · change CategoryBar.barChain
        (quillenAMappingCarrierFaceLastInner F n H G theta) =
      SrepBridge.srepDropLast G
    have hchain := quillenAMappingCarrierFaceLastInner_chain F n H G theta
    have hidx := quillenAMappingCarrierFaceLastIndex_chain
      (C := D) n ⟨G, PUnit.unit⟩
    have hdef : (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit D) n ⟨G, PUnit.unit⟩).1 =
      SrepBridge.srepDropLast G := rfl
    exact hchain.trans (hidx.symm.trans hdef)
  · exact quillenAMappingCarrierFaceLastInner_theta F n H G theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceInnerTripleOf_p4
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawToTriple F n
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) p,
          quillenAMappingCarrierFaceInnerInnerOf F n q p z⟩ =
      ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj p.1,
        (StrictOmitDup.omitAt q.castSucc.succ).obj
          (CategoryBar.barChain z),
        eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain z)) ≫
          CategoryBar.barCoeffR z ≫
          F.map (eqToHom
            (quillenABridgeFaceInnerLeftObj n q p.1))⟩ := by
  rcases p with ⟨H, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  unfold quillenAMappingCarrierRawToTriple
  change (⟨(StrictOrdinaryWeightedBar.wFaceInnerIdx
      (CategoryBar.replUnit C) n q.castSucc.succ
        (quillenACastSucc_succ_ne_last q) ⟨H, PUnit.unit⟩).1,
    CategoryBar.barChain
      (quillenAMappingCarrierFaceInnerInner F n q H G theta),
    CategoryBar.barCoeffR
      (quillenAMappingCarrierFaceInnerInner F n q H G theta)⟩ :
      Σ H : ComposableArrows C n,
        Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left) =
    ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj H,
      (StrictOmitDup.omitAt q.castSucc.succ).obj G,
      eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
        F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))⟩
  refine Sigma.ext
    (quillenAMappingCarrierFaceInnerIndex_chain
      n q ⟨H, PUnit.unit⟩) ?_
  apply heq_of_eq
  apply Sigma.ext
  · exact quillenAMappingCarrierFaceInnerInner_chain F n q H G theta
  · exact (quillenAMappingCarrierFaceInnerInner_theta
      F n q H G theta).trans
        (quillenABridgeFaceInnerThetaHEq F n q H G theta).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierDegTripleOf_p4
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n)
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawToTriple F (n + 1)
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i p,
          quillenAMappingCarrierDegInnerOf F n i p z⟩ =
      ⟨(StrictOmitDup.dupAt i).obj p.1,
        (StrictOmitDup.dupAt i).obj (CategoryBar.barChain z),
        eqToHom (quillenASourceFiberDegRightObj i
            (CategoryBar.barChain z)) ≫
          CategoryBar.barCoeffR z ≫
          F.map (eqToHom (quillenASourceFiberDegLeftObj i p.1))⟩ := by
  rcases p with ⟨H, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  unfold quillenAMappingCarrierRawToTriple
  change (⟨(StrictOrdinaryWeightedBar.wDegInnerIdx
      (CategoryBar.replUnit C) n i ⟨H, PUnit.unit⟩).1,
    CategoryBar.barChain
      (quillenAMappingCarrierDegInner F n i H G theta),
    CategoryBar.barCoeffR
      (quillenAMappingCarrierDegInner F n i H G theta)⟩ :
      Σ H : ComposableArrows C (n + 1),
        Σ G : ComposableArrows D (n + 1), G.right ⟶ F.obj H.left) =
    ⟨(StrictOmitDup.dupAt i).obj H,
      (StrictOmitDup.dupAt i).obj G,
      eqToHom (quillenASourceFiberDegRightObj i G) ≫ theta ≫
        F.map (eqToHom (quillenASourceFiberDegLeftObj i H))⟩
  refine Sigma.ext
    (quillenAMappingCarrierDegIndex_chain n i ⟨H, PUnit.unit⟩) ?_
  apply heq_of_eq
  apply Sigma.ext
  · exact quillenAMappingCarrierDegInner_chain F n i H G theta
  · exact (quillenAMappingCarrierDegInner_theta F n i H G theta).trans
      (quillenABridgeDegInnerThetaHEq F n i H G theta).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromRaw_delta_zero_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hH : p.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH0 : (StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n p).1 =
      x.whiskerLeft
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x n
        ((SimplexCategory.δ (0 : Fin (n + 2))) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceZeroInnerOf F n p z⟩ hH0 =
      CategoryBar.barδ 0
        (quillenASourceFiberRetractionFromRaw F x (n + 1)
          alpha ⟨p, z⟩ hH) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let TFace : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨SrepBridge.srepDropFirst H, SrepBridge.srepDropFirst G,
      theta ≫ F.map (H.map' 0 1)⟩
  let TTop : Σ H : ComposableArrows C (n + 1),
      Σ G : ComposableArrows D (n + 1), G.right ⟶ F.obj H.left :=
    ⟨H, G, theta⟩
  have hTFace : quillenAMappingCarrierRawToTriple F n
      ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceZeroInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TFace :=
    quillenAMappingCarrierFaceZeroTripleOf F n
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hTTop : quillenAMappingCarrierRawToTriple F (n + 1)
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TTop :=
    quillenAMappingCarrierRawToTriple_apply_p4 F (n + 1)
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hHFace : TFace.1 = x.whiskerLeft
      (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).toOrderHom.toFunctor :=
    (quillenAMappingCarrierFaceZeroIndex_chain
      n ⟨H, PUnit.unit⟩).symm.trans hH0
  have hHTop : TTop.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hFaceEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha)
      ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceZeroInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hH0 TFace hTFace hHFace
  have hTopEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x (n + 1) alpha
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hH TTop hTTop hHTop
  calc
    _ = quillenASourceFiberRetractionPacket F x n
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha)
          TFace hHFace := hFaceEq
    _ = CategoryBar.barδ 0
        (quillenASourceFiberRetractionPacket F x (n + 1)
          alpha TTop hHTop) := by
      dsimp only [TFace, TTop]
      unfold quillenASourceFiberRetractionPacket
      let RTop : Σ G : ComposableArrows D (n + 1),
          ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right) :=
        quillenASourceFiberRetractionFromTriple F x
          ⟨H, G, theta⟩ alpha hHTop
      have hgen : quillenASourceFiberRetractionFromTriple F x
          ⟨SrepBridge.srepDropFirst H, SrepBridge.srepDropFirst G,
            theta ≫ F.map (H.map' 0 1)⟩
          (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha) hHFace =
        (⟨SrepBridge.srepDropFirst G,
          ULift.up (PUnit.unit : PUnit.{1}),
          RTop.2.2⟩ :
          Σ G : ComposableArrows D n,
            ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right)) :=
        quillenASourceFiberRetractionFromTriple_δ_zero.{u, v, 0, 1}
          F x H G theta alpha hHTop hHFace
      rw [hgen]
      rw [CategoryBar.barδ_zero_eq]
      refine Sigma.ext rfl ?_
      apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) _
        exact heq_of_eq (Subsingleton.elim _ _)
      · exact (cast_heq _ _).symm
    _ = _ := congrArg (CategoryBar.barδ
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (L := CategoryBar.unitCoeffL D) (0 : Fin (n + 2))) hTopEq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromRaw_delta_last_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hH : p.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHl : (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n p).1 =
      x.whiskerLeft
        ((SimplexCategory.δ (Fin.last (n + 1))) ≫ alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x n
        ((SimplexCategory.δ (Fin.last (n + 1))) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceLastInnerOf F n p z⟩ hHl =
      CategoryBar.barδ (Fin.last (n + 1))
        (quillenASourceFiberRetractionFromRaw F x (n + 1)
          alpha ⟨p, z⟩ hH) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let TFace : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨SrepBridge.srepDropLast H, SrepBridge.srepDropLast G,
      G.map' n (n + 1) ≫ theta⟩
  let TTop : Σ H : ComposableArrows C (n + 1),
      Σ G : ComposableArrows D (n + 1), G.right ⟶ F.obj H.left :=
    ⟨H, G, theta⟩
  have hTFace : quillenAMappingCarrierRawToTriple F n
      ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceLastInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TFace :=
    quillenAMappingCarrierFaceLastTripleOf_p4 F n
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hTTop : quillenAMappingCarrierRawToTriple F (n + 1)
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TTop :=
    quillenAMappingCarrierRawToTriple_apply_p4 F (n + 1)
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hHFace : TFace.1 = x.whiskerLeft
      (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).toOrderHom.toFunctor := by
    dsimp only [TFace]
    exact hHl
  have hHTop : TTop.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hFaceEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
      ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceLastInnerOf F n
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hHl TFace hTFace hHFace
  have hTopEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x (n + 1) alpha
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hH TTop hTTop hHTop
  calc
    _ = quillenASourceFiberRetractionPacket F x n
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
          TFace hHFace := hFaceEq
    _ = CategoryBar.barδ (Fin.last (n + 1))
        (quillenASourceFiberRetractionPacket F x (n + 1)
          alpha TTop hHTop) := by
      dsimp only [TFace, TTop]
      unfold quillenASourceFiberRetractionPacket
      let RTop : Σ G : ComposableArrows D (n + 1),
          ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right) :=
        quillenASourceFiberRetractionFromTriple F x
          ⟨H, G, theta⟩ alpha hHTop
      have hgen : quillenASourceFiberRetractionFromTriple F x
          ⟨SrepBridge.srepDropLast H, SrepBridge.srepDropLast G,
            G.map' n (n + 1) ≫ theta⟩
          (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha) hHFace =
        (⟨SrepBridge.srepDropLast G,
          ULift.up (PUnit.unit : PUnit.{1}),
          G.map' n (n + 1) ≫
            RTop.2.2⟩ :
          Σ G : ComposableArrows D n,
            ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right)) :=
        quillenASourceFiberRetractionFromTriple_δ_last.{u, v, 0, 1}
          F x H G theta alpha hHTop hHFace
      rw [hgen]
      rw [CategoryBar.barδ_last_eq]
      refine Sigma.ext ?_ ?_
      · have hidx := quillenAMappingCarrierFaceLastIndex_chain
          (C := D) n ⟨G, PUnit.unit⟩
        have hdef : (StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit D) n ⟨G, PUnit.unit⟩).1 =
          SrepBridge.srepDropLast G := rfl
        exact hdef.symm.trans hidx
      apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) _
        exact heq_of_eq (Subsingleton.elim _ _)
      · exact (cast_heq _ _).symm
    _ = _ := congrArg (CategoryBar.barδ
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (L := CategoryBar.unitCoeffL D) (Fin.last (n + 1))) hTopEq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromRaw_delta_inner_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (q : Fin n) (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (hH : p.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHi : (StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q) p).1 =
      x.whiskerLeft
        ((SimplexCategory.δ q.castSucc.succ) ≫ alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x n
        ((SimplexCategory.δ q.castSucc.succ) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) p,
          quillenAMappingCarrierFaceInnerInnerOf F n q p z⟩ hHi =
      CategoryBar.barδ q.castSucc.succ
        (quillenASourceFiberRetractionFromRaw F x (n + 1)
          alpha ⟨p, z⟩ hH) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let TFace : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj H,
      (StrictOmitDup.omitAt q.castSucc.succ).obj G,
      eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
        F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))⟩
  let TTop : Σ H : ComposableArrows C (n + 1),
      Σ G : ComposableArrows D (n + 1), G.right ⟶ F.obj H.left :=
    ⟨H, G, theta⟩
  have hTFace : quillenAMappingCarrierRawToTriple F n
      ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q) ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceInnerInnerOf F n q
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TFace :=
    quillenAMappingCarrierFaceInnerTripleOf_p4 F n q
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hTTop : quillenAMappingCarrierRawToTriple F (n + 1)
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TTop :=
    quillenAMappingCarrierRawToTriple_apply_p4 F (n + 1)
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hHFace : TFace.1 = x.whiskerLeft
      (SimplexCategory.δ q.castSucc.succ ≫ alpha).toOrderHom.toFunctor :=
    (quillenAMappingCarrierFaceInnerIndex_chain
      n q ⟨H, PUnit.unit⟩).symm.trans hHi
  have hHTop : TTop.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hFaceEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n (SimplexCategory.δ q.castSucc.succ ≫ alpha)
      ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q) ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierFaceInnerInnerOf F n q
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hHi TFace hTFace hHFace
  have hTopEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x (n + 1) alpha
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hH TTop hTTop hHTop
  calc
    _ = quillenASourceFiberRetractionPacket F x n
        (SimplexCategory.δ q.castSucc.succ ≫ alpha)
          TFace hHFace := hFaceEq
    _ = CategoryBar.barδ q.castSucc.succ
        (quillenASourceFiberRetractionPacket F x (n + 1)
          alpha TTop hHTop) := by
      dsimp only [TFace, TTop]
      unfold quillenASourceFiberRetractionPacket
      let RTop : Σ G : ComposableArrows D (n + 1),
          ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right) :=
        quillenASourceFiberRetractionFromTriple F x
          ⟨H, G, theta⟩ alpha hHTop
      have hgen : quillenASourceFiberRetractionFromTriple F x
          ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj H,
            (StrictOmitDup.omitAt q.castSucc.succ).obj G,
            eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
              F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))⟩
          (SimplexCategory.δ q.castSucc.succ ≫ alpha) hHFace =
        (⟨(StrictOmitDup.omitAt q.castSucc.succ).obj G,
          ULift.up (PUnit.unit : PUnit.{1}),
          eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫
            RTop.2.2⟩ :
          Σ G : ComposableArrows D n,
            ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right)) :=
        quillenASourceFiberRetractionFromTriple_δ_inner.{u, v, 0, 1}
          F x q H G theta alpha hHTop hHFace
      rw [hgen]
      rw [CategoryBar.barδ_castSucc_succ_eq]
      refine Sigma.ext rfl ?_
      apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) _
        exact heq_of_eq (Subsingleton.elim _ _)
      · let rtop := RTop.2.2
        exact (CategoryTheory.eqToHom_comp_heq rtop
          (quillenABridgeFaceInnerRightObj n q G)).trans
            (cast_heq _ rtop).symm
    _ = _ := congrArg (CategoryBar.barδ
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (L := CategoryBar.unitCoeffL D) q.castSucc.succ) hTopEq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionFromRaw_sigma_of
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m n : ℕ} (x : ComposableArrows C m)
    (i : Fin (n + 1)) (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (z : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hH : p.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHs : (StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i p).1 =
      x.whiskerLeft
        ((SimplexCategory.σ i) ≫ alpha).toOrderHom.toFunctor) :
    quillenASourceFiberRetractionFromRaw F x (n + 1)
        ((SimplexCategory.σ i) ≫ alpha)
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i p,
          quillenAMappingCarrierDegInnerOf F n i p z⟩ hHs =
      CategoryBar.barσ i
        (quillenASourceFiberRetractionFromRaw F x n
          alpha ⟨p, z⟩ hH) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at z
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let TDeg : Σ H : ComposableArrows C (n + 1),
      Σ G : ComposableArrows D (n + 1), G.right ⟶ F.obj H.left :=
    ⟨(StrictOmitDup.dupAt i).obj H,
      (StrictOmitDup.dupAt i).obj G,
      eqToHom (quillenASourceFiberDegRightObj i G) ≫ theta ≫
        F.map (eqToHom (quillenASourceFiberDegLeftObj i H))⟩
  let TTop : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨H, G, theta⟩
  have hTDeg : quillenAMappingCarrierRawToTriple F (n + 1)
      ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierDegInnerOf F n i
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TDeg :=
    quillenAMappingCarrierDegTripleOf_p4 F n i
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hTTop : quillenAMappingCarrierRawToTriple F n
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩ = TTop :=
    quillenAMappingCarrierRawToTriple_apply_p4 F n
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hHDeg : TDeg.1 = x.whiskerLeft
      (SimplexCategory.σ i ≫ alpha).toOrderHom.toFunctor :=
    (quillenAMappingCarrierDegIndex_chain
      n i ⟨H, PUnit.unit⟩).symm.trans hHs
  have hHTop : TTop.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hDegEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x (n + 1) (SimplexCategory.σ i ≫ alpha)
      ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i ⟨H, PUnit.unit⟩,
        quillenAMappingCarrierDegInnerOf F n i
          ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hHs TDeg hTDeg hHDeg
  have hTopEq := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n alpha
      ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
      hH TTop hTTop hHTop
  calc
    _ = quillenASourceFiberRetractionPacket F x (n + 1)
        (SimplexCategory.σ i ≫ alpha) TDeg hHDeg := hDegEq
    _ = CategoryBar.barσ i
        (quillenASourceFiberRetractionPacket F x n
          alpha TTop hHTop) := by
      dsimp only [TDeg, TTop]
      unfold quillenASourceFiberRetractionPacket
      let RTop : Σ G : ComposableArrows D n,
          ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right) :=
        quillenASourceFiberRetractionFromTriple F x
          ⟨H, G, theta⟩ alpha hHTop
      have hgen : quillenASourceFiberRetractionFromTriple F x
          ⟨(StrictOmitDup.dupAt i).obj H,
            (StrictOmitDup.dupAt i).obj G,
            eqToHom (quillenASourceFiberDegRightObj i G) ≫ theta ≫
              F.map (eqToHom (quillenASourceFiberDegLeftObj i H))⟩
          (SimplexCategory.σ i ≫ alpha) hHDeg =
        (⟨(StrictOmitDup.dupAt i).obj G,
          ULift.up (PUnit.unit : PUnit.{1}),
          eqToHom (quillenASourceFiberDegRightObj i G) ≫
            RTop.2.2⟩ :
          Σ G : ComposableArrows D (n + 1),
            ULift.{0} PUnit.{1} × (G.right ⟶ F.obj x.right)) :=
        quillenASourceFiberRetractionFromTriple_σ.{u, v, 0, 1}
          F x i H G theta alpha hHTop hHDeg
      rw [hgen]
      unfold CategoryBar.barσ
      refine Sigma.ext rfl ?_
      apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) _
        exact heq_of_eq (Subsingleton.elim _ _)
      · let rtop := RTop.2.2
        exact (CategoryTheory.eqToHom_comp_heq rtop
          (quillenASourceFiberDegRightObj i G)).trans
            (cast_heq _ rtop).symm
    _ = _ := congrArg (CategoryBar.barσ
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (L := CategoryBar.unitCoeffL D) i) hTopEq.symm

private noncomputable def quillenASourceFiberRetractionDecodedRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (⦋n⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)}) :
    CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n := by
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  have hSource : (quillenASource F).app (op ⦋n⦌) d.1.1 = r.1.1 :=
    quillenASource_eq_raw_chain F n d.1.1
  have hH : r.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have h := hSource.symm.trans d.2
    change r.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  exact quillenASourceFiberRetractionFromRaw F x n d.1.2 r hH

private noncomputable def quillenASourceFiberRetractionAppRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌)) :
    CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n :=
  quillenASourceFiberRetractionDecodedRaw F x n
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌) z)

private noncomputable def quillenASourceFiberDecodedMapRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m)
    {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (d : {p : (quillenAMappingCarrier F).obj a × (a.unop ⟶ ⦋m⦌) //
      (quillenASource F).app a p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)}) :
    {p : (quillenAMappingCarrier F).obj b × (b.unop ⟶ ⦋m⦌) //
      (quillenASource F).app b p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)} :=
  ⟨⟨(quillenAMappingCarrier F).map k d.1.1, k.unop ≫ d.1.2⟩, by
    calc
      (quillenASource F).app b
          ((quillenAMappingCarrier F).map k d.1.1) =
          (nerve C).map k ((quillenASource F).app a d.1.1) :=
        ConcreteCategory.congr_hom ((quillenASource F).naturality k) d.1.1
      _ = (nerve C).map k
          ((nerve C).map d.1.2.op (quillenAChainAsNerve C x)) := by
        rw [d.2]
      _ = (nerve C).map (k.unop ≫ d.1.2).op
          (quillenAChainAsNerve C x) := by
        have h := ConcreteCategory.congr_hom
          ((nerve C).map_comp d.1.2.op k) (quillenAChainAsNerve C x)
        exact h.symm⟩

private theorem quillenASourceFiberDecodedMapRaw_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m)
    {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj a) :
    quillenASourceFiberDecodedMapRaw F x k
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) a z) =
      SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) b
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map k z) := by
  rw [SSet.leftFiber.objEquiv_map]
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionAppRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRetractionAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).δ 0 z) =
      CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) 0
        (quillenASourceFiberRetractionAppRaw F x (n + 1) z) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌) z
  let d0 := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)
      ((SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).map k z)
  have hd : quillenASourceFiberDecodedMapRaw F x k d = d0 :=
    quillenASourceFiberDecodedMapRaw_objEquiv F x k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let y := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {q : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (⦋n + 1⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n + 1⦌) q.1 =
      (nerve C).map q.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenASourceFiberRetractionDecodedRaw F x n d0 =
    CategoryBar.barδ 0
      (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d)
  calc
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k d) :=
      congrArg (quillenASourceFiberRetractionDecodedRaw F x n) hd.symm
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k dIncl) :=
      congrArg (fun e ↦ quillenASourceFiberRetractionDecodedRaw
        F x n (quillenASourceFiberDecodedMapRaw F x k e)) hD
    _ = CategoryBar.barδ 0
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_zero_of F n p y
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = _ at hRaw
      let e := quillenASourceFiberDecodedMapRaw F x k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hHFace : rFace.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F n e.1.1
        have h := hs.symm.trans e.2
        change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
        exact h
      let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceZeroInnerOf F n p y⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = rExpected
        exact hRaw
      have hHExpected : rExpected.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        rw [← hRawE]
        exact hHFace
      have hReplace := quillenASourceFiberRetractionFromRaw_congr
        F x n (rfl : alphaFace = alphaFace)
          hRawE hHFace hHExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, y⟩
      have hTopRaw : rTop = rTopExpected :=
        quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p y
      have hHTop : rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F (n + 1) dIncl.1.1
        have h := hs.symm.trans dIncl.2
        change rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor at h
        exact h
      have hHTopExpected : rTopExpected.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        rw [← hTopRaw]
        exact hHTop
      have hTopReplace := quillenASourceFiberRetractionFromRaw_congr
        F x (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hHTop hHTopExpected
      unfold quillenASourceFiberRetractionDecodedRaw
      unfold quillenASourceFiberDecodedMapRaw
      dsimp only [k, dIncl]
      change quillenASourceFiberRetractionFromRaw F x n
          alphaFace rFace hHFace =
        CategoryBar.barδ 0
          (quillenASourceFiberRetractionFromRaw F x (n + 1)
            dIncl.1.2 rTop hHTop)
      calc
        _ = quillenASourceFiberRetractionFromRaw F x n
            alphaFace rExpected hHExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ 0
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTopExpected hHTopExpected) := by
          exact quillenASourceFiberRetractionFromRaw_delta_zero_of
            F x dIncl.1.2 p y hHTopExpected hHExpected
        _ = CategoryBar.barδ 0
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTop hHTop) :=
          congrArg (CategoryBar.barδ
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D) (0 : Fin (n + 2)))
              hTopReplace.symm
    _ = CategoryBar.barδ 0
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d) :=
      congrArg (CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) (0 : Fin (n + 2)))
          (congrArg
            (quillenASourceFiberRetractionDecodedRaw F x (n + 1))
            hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionAppRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRetractionAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).δ (Fin.last (n + 1)) z) =
      CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) (Fin.last (n + 1))
        (quillenASourceFiberRetractionAppRaw F x (n + 1) z) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌) z
  let dl := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)
      ((SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).map k z)
  have hd : quillenASourceFiberDecodedMapRaw F x k d = dl :=
    quillenASourceFiberDecodedMapRaw_objEquiv F x k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let y := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {q : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (⦋n + 1⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n + 1⦌) q.1 =
      (nerve C).map q.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenASourceFiberRetractionDecodedRaw F x n dl =
    CategoryBar.barδ (Fin.last (n + 1))
      (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d)
  calc
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k d) :=
      congrArg (quillenASourceFiberRetractionDecodedRaw F x n) hd.symm
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k dIncl) :=
      congrArg (fun e ↦ quillenASourceFiberRetractionDecodedRaw
        F x n (quillenASourceFiberDecodedMapRaw F x k e)) hD
    _ = CategoryBar.barδ (Fin.last (n + 1))
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_last_of F n p y
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = _ at hRaw
      let e := quillenASourceFiberDecodedMapRaw F x k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hHFace : rFace.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F n e.1.1
        have h := hs.symm.trans e.2
        change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
        exact h
      let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit C) n p,
          quillenAMappingCarrierFaceLastInnerOf F n p y⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = rExpected
        exact hRaw
      have hHExpected : rExpected.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        rw [← hRawE]
        exact hHFace
      have hReplace := quillenASourceFiberRetractionFromRaw_congr
        F x n (rfl : alphaFace = alphaFace)
          hRawE hHFace hHExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, y⟩
      have hTopRaw : rTop = rTopExpected :=
        quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p y
      have hHTop : rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F (n + 1) dIncl.1.1
        have h := hs.symm.trans dIncl.2
        change rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor at h
        exact h
      have hHTopExpected : rTopExpected.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        rw [← hTopRaw]
        exact hHTop
      have hTopReplace := quillenASourceFiberRetractionFromRaw_congr
        F x (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hHTop hHTopExpected
      unfold quillenASourceFiberRetractionDecodedRaw
      unfold quillenASourceFiberDecodedMapRaw
      dsimp only [k, dIncl]
      change quillenASourceFiberRetractionFromRaw F x n
          alphaFace rFace hHFace =
        CategoryBar.barδ (Fin.last (n + 1))
          (quillenASourceFiberRetractionFromRaw F x (n + 1)
            dIncl.1.2 rTop hHTop)
      calc
        _ = quillenASourceFiberRetractionFromRaw F x n
            alphaFace rExpected hHExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ (Fin.last (n + 1))
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTopExpected hHTopExpected) := by
          exact quillenASourceFiberRetractionFromRaw_delta_last_of
            F x dIncl.1.2 p y hHTopExpected hHExpected
        _ = CategoryBar.barδ (Fin.last (n + 1))
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTop hHTop) :=
          congrArg (CategoryBar.barδ
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D) (Fin.last (n + 1)))
              hTopReplace.symm
    _ = CategoryBar.barδ (Fin.last (n + 1))
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d) :=
      congrArg (CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) (Fin.last (n + 1)))
          (congrArg
            (quillenASourceFiberRetractionDecodedRaw F x (n + 1))
            hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionAppRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (q : Fin n)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRetractionAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).δ q.castSucc.succ z) =
      CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) q.castSucc.succ
        (quillenASourceFiberRetractionAppRaw F x (n + 1) z) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌) z
  let di := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)
      ((SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).map k z)
  have hd : quillenASourceFiberDecodedMapRaw F x k d = di :=
    quillenASourceFiberDecodedMapRaw_objEquiv F x k z
  let r := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  let p := r.1
  let y := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {w : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
      (⦋n + 1⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n + 1⦌) w.1 =
      (nerve C).map w.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) y, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenASourceFiberRetractionDecodedRaw F x n di =
    CategoryBar.barδ q.castSucc.succ
      (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d)
  calc
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k d) :=
      congrArg (quillenASourceFiberRetractionDecodedRaw F x n) hd.symm
    _ = quillenASourceFiberRetractionDecodedRaw F x n
        (quillenASourceFiberDecodedMapRaw F x k dIncl) :=
      congrArg (fun e ↦ quillenASourceFiberRetractionDecodedRaw
        F x n (quillenASourceFiberDecodedMapRaw F x k e)) hD
    _ = CategoryBar.barδ q.castSucc.succ
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_δ_inner_of F n q p y
      change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = _ at hRaw
      let e := quillenASourceFiberDecodedMapRaw F x k dIncl
      let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
      let alphaFace := e.1.2
      have hHFace : rFace.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F n e.1.1
        have h := hs.symm.trans e.2
        change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
        exact h
      let rExpected : Σ w : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj w.1.left).obj (op ⦋n⦌) :=
        ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit C) n q.castSucc.succ
              (quillenACastSucc_succ_ne_last q) p,
          quillenAMappingCarrierFaceInnerInnerOf F n q p y⟩
      have hRawE : rFace = rExpected := by
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                (n + 1) p).app (op ⦋n + 1⦌) y)) = rExpected
        exact hRaw
      have hHExpected : rExpected.1.1 =
          x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
        rw [← hRawE]
        exact hHFace
      have hReplace := quillenASourceFiberRetractionFromRaw_congr
        F x n (rfl : alphaFace = alphaFace)
          hRawE hHFace hHExpected
      let rTop := quillenAMappingCarrierRawEquiv F (n + 1) dIncl.1.1
      let rTopExpected : Σ w : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj w.1.left).obj (op ⦋n + 1⦌) :=
        ⟨p, y⟩
      have hTopRaw : rTop = rTopExpected :=
        quillenAMappingCarrierRawEquiv_wbarIncl F (n + 1) p y
      have hHTop : rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F (n + 1) dIncl.1.1
        have h := hs.symm.trans dIncl.2
        change rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor at h
        exact h
      have hHTopExpected : rTopExpected.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        rw [← hTopRaw]
        exact hHTop
      have hTopReplace := quillenASourceFiberRetractionFromRaw_congr
        F x (n + 1) (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hHTop hHTopExpected
      unfold quillenASourceFiberRetractionDecodedRaw
      unfold quillenASourceFiberDecodedMapRaw
      dsimp only [k, dIncl]
      change quillenASourceFiberRetractionFromRaw F x n
          alphaFace rFace hHFace =
        CategoryBar.barδ q.castSucc.succ
          (quillenASourceFiberRetractionFromRaw F x (n + 1)
            dIncl.1.2 rTop hHTop)
      calc
        _ = quillenASourceFiberRetractionFromRaw F x n
            alphaFace rExpected hHExpected := by
          simpa only using hReplace
        _ = CategoryBar.barδ q.castSucc.succ
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTopExpected hHTopExpected) := by
          exact quillenASourceFiberRetractionFromRaw_delta_inner_of
            F x q dIncl.1.2 p y hHTopExpected hHExpected
        _ = CategoryBar.barδ q.castSucc.succ
            (quillenASourceFiberRetractionFromRaw F x (n + 1)
              dIncl.1.2 rTop hHTop) :=
          congrArg (CategoryBar.barδ
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D) q.castSucc.succ)
              hTopReplace.symm
    _ = CategoryBar.barδ q.castSucc.succ
        (quillenASourceFiberRetractionDecodedRaw F x (n + 1) d) :=
      congrArg (CategoryBar.barδ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) q.castSucc.succ)
          (congrArg
            (quillenASourceFiberRetractionDecodedRaw F x (n + 1))
            hD.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetractionAppRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (i : Fin (n + 1))
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌)) :
    quillenASourceFiberRetractionAppRaw F x (n + 1)
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).σ i z) =
      CategoryBar.barσ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) i
        (quillenASourceFiberRetractionAppRaw F x n z) := by
  let k := (SimplexCategory.σ i).op
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌) z
  let ds := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌)
      ((SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).map k z)
  have hd : quillenASourceFiberDecodedMapRaw F x k d = ds :=
    quillenASourceFiberDecodedMapRaw_objEquiv F x k z
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  let p := r.1
  let y := r.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) y := by
    apply (quillenAMappingCarrierRawEquiv F n).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  let dIncl : {w : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n⦌) w.1 =
      (nerve C).map w.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨(StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) y, d.1.2⟩, by
      rw [← hCarrier]
      exact d.2⟩
  have hD : d = dIncl := by
    apply Subtype.ext
    exact Prod.ext hCarrier rfl
  change quillenASourceFiberRetractionDecodedRaw F x (n + 1) ds =
    CategoryBar.barσ i
      (quillenASourceFiberRetractionDecodedRaw F x n d)
  calc
    _ = quillenASourceFiberRetractionDecodedRaw F x (n + 1)
        (quillenASourceFiberDecodedMapRaw F x k d) :=
      congrArg (quillenASourceFiberRetractionDecodedRaw F x (n + 1))
        hd.symm
    _ = quillenASourceFiberRetractionDecodedRaw F x (n + 1)
        (quillenASourceFiberDecodedMapRaw F x k dIncl) :=
      congrArg (fun e ↦ quillenASourceFiberRetractionDecodedRaw
        F x (n + 1) (quillenASourceFiberDecodedMapRaw F x k e)) hD
    _ = CategoryBar.barσ i
        (quillenASourceFiberRetractionDecodedRaw F x n dIncl) := by
      have hRaw := quillenAMappingCarrierRawEquiv_σ_of F n i p y
      change quillenAMappingCarrierRawEquiv F (n + 1)
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                n p).app (op ⦋n⦌) y)) = _ at hRaw
      let e := quillenASourceFiberDecodedMapRaw F x k dIncl
      let rDeg := quillenAMappingCarrierRawEquiv F (n + 1) e.1.1
      let alphaDeg := e.1.2
      have hHDeg : rDeg.1.1 =
          x.whiskerLeft alphaDeg.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F (n + 1) e.1.1
        have h := hs.symm.trans e.2
        change rDeg.1.1 = x.whiskerLeft alphaDeg.toOrderHom.toFunctor at h
        exact h
      let rExpected : Σ w : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) (n + 1),
          ((quillenAMappingDiagram F).obj w.1.left).obj (op ⦋n + 1⦌) :=
        ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
            (CategoryBar.replUnit C) n i p,
          quillenAMappingCarrierDegInnerOf F n i p y⟩
      have hRawE : rDeg = rExpected := by
        change quillenAMappingCarrierRawEquiv F (n + 1)
          ((quillenAMappingCarrier F).map k
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit C) (quillenAMappingDiagram F)
                n p).app (op ⦋n⦌) y)) = rExpected
        exact hRaw
      have hHExpected : rExpected.1.1 =
          x.whiskerLeft alphaDeg.toOrderHom.toFunctor := by
        rw [← hRawE]
        exact hHDeg
      have hReplace := quillenASourceFiberRetractionFromRaw_congr
        F x (n + 1) (rfl : alphaDeg = alphaDeg)
          hRawE hHDeg hHExpected
      let rTop := quillenAMappingCarrierRawEquiv F n dIncl.1.1
      let rTopExpected : Σ w : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj w.1.left).obj (op ⦋n⦌) :=
        ⟨p, y⟩
      have hTopRaw : rTop = rTopExpected :=
        quillenAMappingCarrierRawEquiv_wbarIncl F n p y
      have hHTop : rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        have hs := quillenASource_eq_raw_chain F n dIncl.1.1
        have h := hs.symm.trans dIncl.2
        change rTop.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor at h
        exact h
      have hHTopExpected : rTopExpected.1.1 =
          x.whiskerLeft dIncl.1.2.toOrderHom.toFunctor := by
        rw [← hTopRaw]
        exact hHTop
      have hTopReplace := quillenASourceFiberRetractionFromRaw_congr
        F x n (rfl : dIncl.1.2 = dIncl.1.2)
          hTopRaw hHTop hHTopExpected
      unfold quillenASourceFiberRetractionDecodedRaw
      unfold quillenASourceFiberDecodedMapRaw
      dsimp only [k, dIncl]
      change quillenASourceFiberRetractionFromRaw F x (n + 1)
          alphaDeg rDeg hHDeg =
        CategoryBar.barσ i
          (quillenASourceFiberRetractionFromRaw F x n
            dIncl.1.2 rTop hHTop)
      calc
        _ = quillenASourceFiberRetractionFromRaw F x (n + 1)
            alphaDeg rExpected hHExpected := by
          simpa only using hReplace
        _ = CategoryBar.barσ i
            (quillenASourceFiberRetractionFromRaw F x n
              dIncl.1.2 rTopExpected hHTopExpected) := by
          exact quillenASourceFiberRetractionFromRaw_sigma_of
            F x i dIncl.1.2 p y hHTopExpected hHExpected
        _ = CategoryBar.barσ i
            (quillenASourceFiberRetractionFromRaw F x n
              dIncl.1.2 rTop hHTop) :=
          congrArg (CategoryBar.barσ
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D) i) hTopReplace.symm
    _ = CategoryBar.barσ i
        (quillenASourceFiberRetractionDecodedRaw F x n d) :=
      congrArg (CategoryBar.barσ
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) i)
          (congrArg
            (quillenASourceFiberRetractionDecodedRaw F x n) hD.symm)

private noncomputable def quillenASourceFiberRetractionAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m)
    (a : SimplexCategoryᵒᵖ) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj a ⟶
      (CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D)).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenASourceFiberRetractionAppRaw F x n)

@[simp]
private theorem quillenASourceFiberRetractionAppNat_mk
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ) :
    quillenASourceFiberRetractionAppNat F x (op ⦋n⦌) =
      ↾(quillenASourceFiberRetractionAppRaw F x n) := by
  rfl

private noncomputable def quillenASourceFiberRetraction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    SSet.leftFiber (quillenASource F) (quillenAChainAsNerve C x) ⟶
      CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) where
  app a := quillenASourceFiberRetractionAppNat F x a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map f.op ≫
          quillenASourceFiberRetractionAppNat F x (op A) =
        quillenASourceFiberRetractionAppNat F x (op B) ≫
          (CategoryBar.categoryBar
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D)).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberRetractionAppNat F x (op ⦋n⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map
              (SimplexCategory.δ i).op z) =
        (CategoryBar.categoryBar
          (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
          (L := CategoryBar.unitCoeffL D)).map
            (SimplexCategory.δ i).op
              (quillenASourceFiberRetractionAppNat F x
                (op ⦋n + 1⦌) z)
      rw [CategoryBar.categoryBar_map_δ]
      change quillenASourceFiberRetractionAppRaw F x n
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).δ i z) =
        CategoryBar.barδ i
          (quillenASourceFiberRetractionAppRaw F x (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact quillenASourceFiberRetractionAppRaw_delta_zero
          F x n z
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact quillenASourceFiberRetractionAppRaw_delta_last
            F x n z
        · exact quillenASourceFiberRetractionAppRaw_delta_inner
            F x n q z
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberRetractionAppNat F x (op ⦋n + 1⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map
              (SimplexCategory.σ i).op z) =
        (CategoryBar.categoryBar
          (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
          (L := CategoryBar.unitCoeffL D)).map
            (SimplexCategory.σ i).op
              (quillenASourceFiberRetractionAppNat F x (op ⦋n⦌) z)
      rw [CategoryBar.categoryBar_map_σ]
      change quillenASourceFiberRetractionAppRaw F x (n + 1)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).σ i z) =
        CategoryBar.barσ i
          (quillenASourceFiberRetractionAppRaw F x n z)
      exact quillenASourceFiberRetractionAppRaw_sigma F x n i z
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

private noncomputable def quillenATargetFiberSectionDecoded
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌)) :
    {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y} := by
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) n at z
  let H := z.1
  let phi := z.2.1
  let alpha := quillenATargetFiberFirstVertexMap m n
  let G : ComposableArrows D n := (nerve D).map alpha.op y
  have hRight : G.right = y.obj 0 := rfl
  let theta : G.right ⟶ F.obj H.left := eqToHom hRight ≫ phi
  exact ⟨⟨quillenAMappingCarrierIncl F n H G theta, alpha⟩, by
    change (quillenATarget F).app (op ⦋n⦌)
      (quillenAMappingCarrierIncl F n H G theta) =
        (nerve D).map alpha.op y
    rw [quillenATarget_carrierIncl]⟩

private theorem quillenATargetFiberSectionApp_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌)) :
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n z) =
      quillenATargetFiberSectionDecoded F y n z := by
  change (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n⦌)).symm
          (quillenATargetFiberSectionDecoded F y n z)) = _
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberSectionApp_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberSectionApp F y n
        ((CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).δ 0 z) =
      (SSet.leftFiber (quillenATarget F) y).δ 0
        (quillenATargetFiberSectionApp F y (n + 1) z) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).δ 0 z)) =
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        ((SSet.leftFiber (quillenATarget F) y).map k
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).map
              (SimplexCategory.δ (0 : Fin (n + 2))).op z)) =
    quillenATargetFiberDecodedMap F y k
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n + 1⦌))
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [CategoryBar.simplicialReplacement_map_δ]
  rw [quillenATargetFiberSectionApp_objEquiv,
    quillenATargetFiberSectionApp_objEquiv]
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) (n + 1) at z
  rcases z with ⟨H, phi, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  unfold quillenATargetFiberDecodedMap
    quillenATargetFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop := quillenATargetFiberFirstVertexMap m (n + 1)
    let GTop : ComposableArrows D (n + 1) :=
      (nerve D).map alphaTop.op y
    have hRightTop : GTop.right = y.obj 0 := rfl
    let thetaTop : GTop.right ⟶ F.obj H.left :=
      eqToHom hRightTop ≫ phi
    have hRaw := quillenAMappingCarrierRawEquiv_δ_zero
      F n H GTop thetaTop
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map
        (SimplexCategory.δ (0 : Fin (n + 2))).op
          (quillenAMappingCarrierIncl F (n + 1) H GTop thetaTop)) = _
        at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    rw [quillenAMappingCarrierFaceZeroInner_eq_canonical]
    simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rw [CategoryBar.barδ_zero_eq]
    dsimp only [GTop, thetaTop,
      quillenATargetFiberFirstVertexMap,
      quillenAMappingCarrierInner,
      quillenAMappingIndex,
      StrictOrdinaryWeightedBar.wFaceZeroIdx, id]
    congr! 1
    refine Sigma.ext ?_ ?_
    · dsimp only
      have hConst :
          SimplexCategory.δ (0 : Fin (n + 2)) ≫ alphaTop =
            quillenATargetFiberFirstVertexMap m n := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext j
        rfl
      calc
        _ = (nerve D).map
            ((SimplexCategory.δ (0 : Fin (n + 2)) ≫ alphaTop).op) y := by
          rw [hConst]
          unfold quillenATargetFiberFirstVertexMap
          rfl
        _ = (nerve D).δ 0 ((nerve D).map alphaTop.op y) := by
          exact ConcreteCategory.congr_hom
            ((nerve D).map_comp alphaTop.op
              (SimplexCategory.δ (0 : Fin (n + 2))).op) y
    · apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
        exact heq_of_eq (Subsingleton.elim _ _)
      · simp only [CategoryBar.commaCoeffL_map]
        simp
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberSectionApp_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberSectionApp F y n
        ((CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).δ (Fin.last (n + 1)) z) =
      (SSet.leftFiber (quillenATarget F) y).δ (Fin.last (n + 1))
        (quillenATargetFiberSectionApp F y (n + 1) z) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).δ
              (Fin.last (n + 1)) z)) =
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        ((SSet.leftFiber (quillenATarget F) y).map k
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).map
              (SimplexCategory.δ (Fin.last (n + 1))).op z)) =
    quillenATargetFiberDecodedMap F y k
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n + 1⦌))
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [CategoryBar.simplicialReplacement_map_δ]
  rw [quillenATargetFiberSectionApp_objEquiv,
    quillenATargetFiberSectionApp_objEquiv]
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) (n + 1) at z
  rcases z with ⟨H, phi, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  unfold quillenATargetFiberDecodedMap
    quillenATargetFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop := quillenATargetFiberFirstVertexMap m (n + 1)
    let GTop : ComposableArrows D (n + 1) :=
      (nerve D).map alphaTop.op y
    have hRightTop : GTop.right = y.obj 0 := rfl
    let thetaTop : GTop.right ⟶ F.obj H.left :=
      eqToHom hRightTop ≫ phi
    have hRaw := quillenAMappingCarrierRawEquiv_δ_last
      F n H GTop thetaTop
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map
        (SimplexCategory.δ (Fin.last (n + 1))).op
          (quillenAMappingCarrierIncl F (n + 1) H GTop thetaTop)) = _
        at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    rw [quillenAMappingCarrierFaceLastInner_eq_canonical]
    simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rw [CategoryBar.barδ_last_eq]
    dsimp only [GTop, thetaTop,
      quillenATargetFiberFirstVertexMap,
      quillenAMappingCarrierInner,
      quillenAMappingIndex,
      StrictOrdinaryWeightedBar.wFaceLastIdx, id]
    have hp : (⟨(nerve C).δ (Fin.last (n + 1)) H,
          PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n) =
        StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n
            (quillenAMappingIndex (n + 1) H) := by
      refine Sigma.ext
        (quillenAMappingCarrierFaceLastIndex_chain n
          (quillenAMappingIndex (n + 1) H)).symm ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    apply heq_of_eq
    refine Sigma.ext ?_ ?_
    · have hConst :
          SimplexCategory.δ (Fin.last (n + 1)) ≫ alphaTop =
            quillenATargetFiberFirstVertexMap m n := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext j
        rfl
      calc
        _ = (nerve D).map
            ((SimplexCategory.δ (Fin.last (n + 1)) ≫ alphaTop).op) y := by
          rw [hConst]
          unfold quillenATargetFiberFirstVertexMap
          rfl
        _ = (nerve D).δ (Fin.last (n + 1))
            ((nerve D).map alphaTop.op y) := by
          exact ConcreteCategory.congr_hom
            ((nerve D).map_comp alphaTop.op
              (SimplexCategory.δ (Fin.last (n + 1))).op) y
    · apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
        exact heq_of_eq (Subsingleton.elim _ _)
      · have hEdge :
            ((nerve D).map alphaTop.op y).map' n (n + 1) = 𝟙 _ := by
          change y.map _ = 𝟙 _
          rw [← y.map_id]
          apply congrArg y.map
          apply Subsingleton.elim
        rw [hEdge]
        simp
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberSectionApp_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberSectionApp F y n
        ((CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).δ q.castSucc.succ z) =
      (SSet.leftFiber (quillenATarget F) y).δ q.castSucc.succ
        (quillenATargetFiberSectionApp F y (n + 1) z) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).δ
              q.castSucc.succ z)) =
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        ((SSet.leftFiber (quillenATarget F) y).map k
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).map
              (SimplexCategory.δ q.castSucc.succ).op z)) =
    quillenATargetFiberDecodedMap F y k
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n + 1⦌))
          (quillenATargetFiberSectionApp F y (n + 1) z))
  rw [CategoryBar.simplicialReplacement_map_δ]
  rw [quillenATargetFiberSectionApp_objEquiv,
    quillenATargetFiberSectionApp_objEquiv]
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) (n + 1) at z
  rcases z with ⟨H, phi, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  unfold quillenATargetFiberDecodedMap
    quillenATargetFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop := quillenATargetFiberFirstVertexMap m (n + 1)
    let GTop : ComposableArrows D (n + 1) :=
      (nerve D).map alphaTop.op y
    have hRightTop : GTop.right = y.obj 0 := rfl
    let thetaTop : GTop.right ⟶ F.obj H.left :=
      eqToHom hRightTop ≫ phi
    have hRaw := quillenAMappingCarrierRawEquiv_δ_inner
      F n q H GTop thetaTop
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map
        (SimplexCategory.δ q.castSucc.succ).op
          (quillenAMappingCarrierIncl F (n + 1) H GTop thetaTop)) = _
        at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    rw [quillenAMappingCarrierFaceInnerInner_eq_canonical]
    simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rw [CategoryBar.barδ_castSucc_succ_eq]
    dsimp only [GTop, thetaTop,
      quillenATargetFiberFirstVertexMap,
      quillenAMappingCarrierInner,
      quillenAMappingIndex,
      StrictOrdinaryWeightedBar.wFaceInnerIdx, id]
    have hp : (⟨(nerve C).δ q.castSucc.succ H,
          PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n) =
        StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n q.castSucc.succ
            (quillenACastSucc_succ_ne_last q)
            (quillenAMappingIndex (n + 1) H) := by
      refine Sigma.ext
        (quillenAMappingCarrierFaceInnerIndex_chain n q
          (quillenAMappingIndex (n + 1) H)).symm ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    apply heq_of_eq
    refine Sigma.ext ?_ ?_
    · have hConst :
          SimplexCategory.δ q.castSucc.succ ≫ alphaTop =
            quillenATargetFiberFirstVertexMap m n := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext j
        rfl
      calc
        _ = (nerve D).map
            ((SimplexCategory.δ q.castSucc.succ ≫ alphaTop).op) y := by
          rw [hConst]
          unfold quillenATargetFiberFirstVertexMap
          rfl
        _ = (nerve D).δ q.castSucc.succ
            ((nerve D).map alphaTop.op y) := by
          exact ConcreteCategory.congr_hom
            ((nerve D).map_comp alphaTop.op
              (SimplexCategory.δ q.castSucc.succ).op) y
    · apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
        exact heq_of_eq (Subsingleton.elim _ _)
      · simp
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberSectionApp_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (i : Fin (n + 1))
    (z : (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj (op ⦋n⦌)) :
    quillenATargetFiberSectionApp F y (n + 1)
        ((CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).σ i z) =
      (SSet.leftFiber (quillenATarget F) y).σ i
        (quillenATargetFiberSectionApp F y n z) := by
  let k := (SimplexCategory.σ i).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n + 1⦌)).injective
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌))
        (quillenATargetFiberSectionApp F y (n + 1)
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).σ i z)) =
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌))
        ((SSet.leftFiber (quillenATarget F) y).map k
          (quillenATargetFiberSectionApp F y n z))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌))
        (quillenATargetFiberSectionApp F y (n + 1)
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).map
              (SimplexCategory.σ i).op z)) =
    quillenATargetFiberDecodedMap F y k
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n⦌))
          (quillenATargetFiberSectionApp F y n z))
  rw [CategoryBar.simplicialReplacement_map_σ]
  rw [quillenATargetFiberSectionApp_objEquiv,
    quillenATargetFiberSectionApp_objEquiv]
  change CategoryBar.barObj C (CategoryBar.replUnit C)
    (CategoryBar.commaCoeffL F (y.obj 0)) n at z
  rcases z with ⟨H, phi, w⟩
  change PUnit at w
  obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
  unfold quillenATargetFiberDecodedMap
    quillenATargetFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    let alphaTop := quillenATargetFiberFirstVertexMap m n
    let GTop : ComposableArrows D n := (nerve D).map alphaTop.op y
    have hRightTop : GTop.right = y.obj 0 := rfl
    let thetaTop : GTop.right ⟶ F.obj H.left :=
      eqToHom hRightTop ≫ phi
    have hRaw := quillenAMappingCarrierRawEquiv_σ
      F n i H GTop thetaTop
    change quillenAMappingCarrierRawEquiv F (n + 1)
      ((quillenAMappingCarrier F).map (SimplexCategory.σ i).op
        (quillenAMappingCarrierIncl F n H GTop thetaTop)) = _ at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    rw [quillenAMappingCarrierDegInner_eq_canonical]
    simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    unfold CategoryBar.barσ
    dsimp only [GTop, thetaTop,
      quillenATargetFiberFirstVertexMap,
      quillenAMappingCarrierInner,
      quillenAMappingIndex,
      StrictOrdinaryWeightedBar.wDegInnerIdx, id]
    have hp : (⟨(nerve C).σ i H,
          PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) (n + 1)) =
        StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit C) n i
            (quillenAMappingIndex n H) := by
      refine Sigma.ext
        (quillenAMappingCarrierDegIndex_chain n i
          (quillenAMappingIndex n H)).symm ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    apply heq_of_eq
    refine Sigma.ext ?_ ?_
    · have hConst : SimplexCategory.σ i ≫ alphaTop =
            quillenATargetFiberFirstVertexMap m (n + 1) := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext j
        rfl
      calc
        _ = (nerve D).map
            ((SimplexCategory.σ i ≫ alphaTop).op) y := by
          rw [hConst]
          unfold quillenATargetFiberFirstVertexMap
          rfl
        _ = (nerve D).σ i ((nerve D).map alphaTop.op y) := by
          exact ConcreteCategory.congr_hom
            ((nerve D).map_comp alphaTop.op
              (SimplexCategory.σ i).op) y
    · apply quillenAProd_heq
      · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
        exact heq_of_eq (Subsingleton.elim _ _)
      · simp
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

private noncomputable def quillenATargetFiberSectionAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    (a : SimplexCategoryᵒᵖ) :
    (CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F (y.obj 0))).obj a ⟶
        (SSet.leftFiber (quillenATarget F) y).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenATargetFiberSectionApp F y n)

private noncomputable def quillenATargetFiberSection
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0)) ⟶
      SSet.leftFiber (quillenATarget F) y where
  app a := quillenATargetFiberSectionAppNat F y a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      (CategoryBar.simplicialReplacement
          (CategoryBar.commaCoeffL F (y.obj 0))).map f.op ≫
          quillenATargetFiberSectionAppNat F y (op A) =
        quillenATargetFiberSectionAppNat F y (op B) ≫
          (SSet.leftFiber (quillenATarget F) y).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberSectionApp F y n
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).δ i z) =
        (SSet.leftFiber (quillenATarget F) y).δ i
          (quillenATargetFiberSectionApp F y (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact quillenATargetFiberSectionApp_delta_zero F y n z
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact quillenATargetFiberSectionApp_delta_last F y n z
        · exact quillenATargetFiberSectionApp_delta_inner
            F y n q z
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberSectionApp F y (n + 1)
          ((CategoryBar.simplicialReplacement
            (CategoryBar.commaCoeffL F (y.obj 0))).σ i z) =
        (SSet.leftFiber (quillenATarget F) y).σ i
          (quillenATargetFiberSectionApp F y n z)
      exact quillenATargetFiberSectionApp_sigma F y n i z
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberSection_comp_retraction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    quillenATargetFiberSection F y ≫
        quillenATargetFiberRetraction F y =
      𝟙 (CategoryBar.simplicialReplacement
        (CategoryBar.commaCoeffL F (y.obj 0))) := by
  ext a z
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      change quillenATargetFiberRetractionAppRaw F y n
          (quillenATargetFiberSectionApp F y n z) = z
      change CategoryBar.barObj C (CategoryBar.replUnit C)
        (CategoryBar.commaCoeffL F (y.obj 0)) n at z
      rcases z with ⟨H, phi, w⟩
      change PUnit at w
      obtain rfl : w = PUnit.unit := Subsingleton.elim _ _
      unfold quillenATargetFiberRetractionAppRaw
      rw [quillenATargetFiberSectionApp_objEquiv]
      let d := quillenATargetFiberSectionDecoded F y n
        (⟨H, phi, PUnit.unit⟩ : CategoryBar.barObj C
          (CategoryBar.replUnit C)
          (CategoryBar.commaCoeffL F (y.obj 0)) n)
      let r := quillenAMappingCarrierRawEquiv F n d.1.1
      have hG : CategoryBar.barChain r.2 = (nerve D).map d.1.2.op y :=
        (quillenATarget_eq_raw_chain F n d.1.1).symm.trans d.2
      unfold quillenATargetFiberRetractionDecoded
      change quillenATargetFiberRetractionFromRaw F y n d.1.2 r hG =
        (⟨H, phi, PUnit.unit⟩ : CategoryBar.barObj C
          (CategoryBar.replUnit C)
          (CategoryBar.commaCoeffL F (y.obj 0)) n)
      let alpha := quillenATargetFiberFirstVertexMap m n
      let G : ComposableArrows D n := (nerve D).map alpha.op y
      have hRight : G.right = y.obj 0 := rfl
      let theta : G.right ⟶ F.obj H.left := eqToHom hRight ≫ phi
      let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
        ⟨quillenAMappingIndex n H,
          quillenAMappingCarrierInner F n H G theta⟩
      have hRaw : r = rExpected := by
        unfold r d quillenATargetFiberSectionDecoded
        dsimp only [id]
        exact quillenAMappingCarrierRawEquiv_incl F n H G theta
      have hGExpected : CategoryBar.barChain rExpected.2 =
          (nerve D).map d.1.2.op y := by
        rw [← hRaw]
        exact hG
      have hReplace := quillenATargetFiberRetractionFromRaw_congr
        F y n (rfl : d.1.2 = d.1.2) hRaw hG hGExpected
      calc
        _ = quillenATargetFiberRetractionFromRaw F y n
            d.1.2 rExpected hGExpected := hReplace
        _ = (⟨H, phi, PUnit.unit⟩ : CategoryBar.barObj C
            (CategoryBar.replUnit C)
            (CategoryBar.commaCoeffL F (y.obj 0)) n) := by
          unfold quillenATargetFiberRetractionFromRaw
            rExpected d quillenATargetFiberSectionDecoded
          dsimp only [alpha, G, theta,
            quillenATargetFiberFirstVertexMap,
            quillenAMappingCarrierInner,
            quillenAMappingIndex,
            CategoryBar.barChain, CategoryBar.barCoeffR, id]
          congr! 1
          simp

private noncomputable def quillenASourceFiberSectionDecoded
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n) :
    {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (⦋n⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)} := by
  rcases z with ⟨G, l, theta⟩
  let alpha : ⦋n⦌ ⟶ ⦋m⦌ :=
    SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
  let H : ComposableArrows C n :=
    x.whiskerLeft alpha.toOrderHom.toFunctor
  let hleft : H.left = x.right :=
    quillenAConstLast_whisker_left x n
  let theta' : G.right ⟶ F.obj H.left :=
    theta ≫ F.map (eqToHom hleft.symm)
  exact ⟨⟨quillenAMappingCarrierIncl F n H G theta', alpha⟩, by
    rw [quillenASource_carrierIncl]
    rfl⟩

private noncomputable def quillenASourceFiberSectionAppRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌) :=
  (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).symm
      (quillenASourceFiberSectionDecoded F x n z)

private theorem quillenASourceFiberSectionAppRaw_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n) :
    SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n⦌)
        (quillenASourceFiberSectionAppRaw F x n z) =
      quillenASourceFiberSectionDecoded F x n z := by
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRetraction_section_app
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n) :
    quillenASourceFiberRetractionAppRaw F x n
      (quillenASourceFiberSectionAppRaw F x n z) = z := by
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let alpha : ⦋n⦌ ⟶ ⦋m⦌ :=
    SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
  let H : ComposableArrows C n :=
    x.whiskerLeft alpha.toOrderHom.toFunctor
  let hleft : H.left = x.right :=
    quillenAConstLast_whisker_left x n
  let theta' : G.right ⟶ F.obj H.left :=
    theta ≫ F.map (eqToHom hleft.symm)
  let d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n⦌) p.1 =
      (nerve C).map p.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨quillenAMappingCarrierIncl F n H G theta', alpha⟩, by
      rw [quillenASource_carrierIncl]
      rfl⟩
  have hsection : SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌)
        (quillenASourceFiberSectionAppRaw F x n
          ⟨G, ULift.up PUnit.unit, theta⟩) = d := by
    exact (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌)).apply_symm_apply d
  unfold quillenASourceFiberRetractionAppRaw
  rw [hsection]
  unfold quillenASourceFiberRetractionDecodedRaw
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨⟨H, PUnit.unit⟩,
      ⟨G, ULift.up PUnit.unit, theta'⟩⟩
  have hRaw : r = rExpected := by
    exact quillenAMappingCarrierRawEquiv_incl F n H G theta'
  have hHActual : r.1.1 =
      x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n d.1.1
    have h := hs.symm.trans d.2
    change r.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    rw [← hRaw]
    exact hHActual
  have hReplace := quillenASourceFiberRetractionFromRaw_congr
    F x n (rfl : d.1.2 = d.1.2) hRaw hHActual hHExpected
  let TTop : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨H, G, theta'⟩
  have hTTop : quillenAMappingCarrierRawToTriple F n rExpected = TTop :=
    quillenAMappingCarrierRawToTriple_apply_p4 F n
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta'⟩
  have hHTop : TTop.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    dsimp only [TTop, d, alpha, H]
  have hTriple := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n d.1.2 rExpected hHExpected TTop hTTop hHTop
  change quillenASourceFiberRetractionFromRaw F x n
      d.1.2 r hHActual = ⟨G, ULift.up PUnit.unit, theta⟩
  calc
    _ = quillenASourceFiberRetractionFromRaw F x n
        d.1.2 rExpected hHExpected := hReplace
    _ = quillenASourceFiberRetractionPacket F x n
        d.1.2 TTop hHTop := hTriple
    _ = _ := by
      dsimp only [d, alpha, TTop, H, theta', hleft] at hHTop ⊢
      unfold quillenASourceFiberRetractionPacket
      rw [quillenASourceFiberRetractionFromTriple_constLast F x G theta]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberSectionAppRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) (n + 1)) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).δ 0
        (quillenASourceFiberSectionAppRaw F x (n + 1) z) =
      quillenASourceFiberSectionAppRaw F x n
        (CategoryBar.barδ 0 z) := by
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberSectionAppRaw F x (n + 1)
              ⟨G, ULift.up PUnit.unit, theta⟩)) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        (quillenASourceFiberSectionAppRaw F x n
          (CategoryBar.barδ 0 ⟨G, ULift.up PUnit.unit, theta⟩))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberSectionAppRaw_objEquiv,
    quillenASourceFiberSectionAppRaw_objEquiv]
  rw [CategoryBar.barδ_zero_eq]
  unfold quillenASourceFiberDecodedMapRaw
    quillenASourceFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n + 1⦌ ⦋m⦌ (Fin.last m)
    let HTop : ComposableArrows C (n + 1) :=
      x.whiskerLeft alphaTop.toOrderHom.toFunctor
    let hleftTop : HTop.left = x.right :=
      quillenAConstLast_whisker_left x (n + 1)
    let thetaTop : G.right ⟶ F.obj HTop.left :=
      theta ≫ F.map (eqToHom hleftTop.symm)
    have hRaw := quillenAMappingCarrierRawEquiv_δ_zero_of F n
      (⟨HTop, PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) (n + 1))
      (⟨G, ULift.up PUnit.unit, thetaTop⟩ :
        CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) (F.obj HTop.left))
          (CategoryBar.unitCoeffL D) (n + 1))
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        (quillenAMappingCarrierIncl F (n + 1) HTop G thetaTop)) = _ at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    apply (quillenAMappingCarrierRawToTriple F n).injective
    rw [quillenAMappingCarrierFaceZeroTripleOf]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    dsimp only [alphaTop, HTop, hleftTop, thetaTop,
      id]
    let alphaFace : ⦋n⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
    let HFace : ComposableArrows C n :=
      x.whiskerLeft alphaFace.toOrderHom.toFunctor
    have hConst : SimplexCategory.δ (0 : Fin (n + 2)) ≫ alphaTop =
        alphaFace := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext j
      rfl
    have hHConst : SrepBridge.srepDropFirst
        (x.whiskerLeft alphaTop.toOrderHom.toFunctor) = HFace := by
      change x.whiskerLeft
          (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alphaTop).toOrderHom.toFunctor =
        x.whiskerLeft alphaFace.toOrderHom.toFunctor
      rw [hConst]
    refine Sigma.ext hHConst ?_
    apply heq_of_eq
    refine Sigma.ext rfl ?_
    dsimp only [CategoryBar.barCoeffR]
    have e0 : alphaTop.toOrderHom.toFunctor.obj 0 = Fin.last m :=
      SimplexCategory.const_apply ⦋n + 1⦌ ⦋m⦌ (Fin.last m) 0
    have e1 : alphaTop.toOrderHom.toFunctor.obj 1 = Fin.last m :=
      SimplexCategory.const_apply ⦋n + 1⦌ ⦋m⦌ (Fin.last m) 1
    have hEdgeTop : HTop.map' 0 1 =
        eqToHom (congrArg x.obj (e0.trans e1.symm)) := by
      dsimp only [HTop, ComposableArrows.map']
      rw [← eqToHom_map x (e0.trans e1.symm)]
      apply congrArg x.map
      apply Subsingleton.elim
    change HEq ((theta ≫ F.map (eqToHom hleftTop.symm)) ≫
      F.map (HTop.map' 0 1)) _
    rw [hEdgeTop, Category.assoc, ← F.map_comp, eqToHom_trans]
    rw [eqToHom_map]
    exact (CategoryTheory.comp_eqToHom_heq theta _).trans
      ((CategoryTheory.comp_eqToHom_heq _ _).trans
        (cast_heq _ theta)).symm
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberSectionAppRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) (n + 1)) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).δ (Fin.last (n + 1))
        (quillenASourceFiberSectionAppRaw F x (n + 1) z) =
      quillenASourceFiberSectionAppRaw F x n
        (CategoryBar.barδ (Fin.last (n + 1)) z) := by
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberSectionAppRaw F x (n + 1)
              ⟨G, ULift.up PUnit.unit, theta⟩)) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        (quillenASourceFiberSectionAppRaw F x n
          (CategoryBar.barδ (Fin.last (n + 1))
            ⟨G, ULift.up PUnit.unit, theta⟩))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberSectionAppRaw_objEquiv,
    quillenASourceFiberSectionAppRaw_objEquiv]
  rw [CategoryBar.barδ_last_eq]
  unfold quillenASourceFiberDecodedMapRaw
    quillenASourceFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n + 1⦌ ⦋m⦌ (Fin.last m)
    let HTop : ComposableArrows C (n + 1) :=
      x.whiskerLeft alphaTop.toOrderHom.toFunctor
    let hleftTop : HTop.left = x.right :=
      quillenAConstLast_whisker_left x (n + 1)
    let thetaTop : G.right ⟶ F.obj HTop.left :=
      theta ≫ F.map (eqToHom hleftTop.symm)
    have hRaw := quillenAMappingCarrierRawEquiv_δ_last_of F n
      (⟨HTop, PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) (n + 1))
      (⟨G, ULift.up PUnit.unit, thetaTop⟩ :
        CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) (F.obj HTop.left))
          (CategoryBar.unitCoeffL D) (n + 1))
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        (quillenAMappingCarrierIncl F (n + 1) HTop G thetaTop)) = _ at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    apply (quillenAMappingCarrierRawToTriple F n).injective
    rw [quillenAMappingCarrierFaceLastTripleOf_p4]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    dsimp only [alphaTop, HTop, hleftTop, thetaTop, id]
    let alphaFace : ⦋n⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
    let HFace : ComposableArrows C n :=
      x.whiskerLeft alphaFace.toOrderHom.toFunctor
    have hConst : SimplexCategory.δ (Fin.last (n + 1)) ≫ alphaTop =
        alphaFace := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext j
      rfl
    have hHConst : SrepBridge.srepDropLast
        (x.whiskerLeft alphaTop.toOrderHom.toFunctor) = HFace := by
      change x.whiskerLeft
          (SimplexCategory.δ (Fin.last (n + 1)) ≫
            alphaTop).toOrderHom.toFunctor =
        x.whiskerLeft alphaFace.toOrderHom.toFunctor
      rw [hConst]
    refine Sigma.ext hHConst ?_
    apply heq_of_eq
    have hidx := quillenAMappingCarrierFaceLastIndex_chain
      (C := D) n ⟨G, PUnit.unit⟩
    have hdef : (StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit D) n ⟨G, PUnit.unit⟩).1 =
      SrepBridge.srepDropLast G := rfl
    have hGConst : SrepBridge.srepDropLast G = (nerve D).δ
        (Fin.last (n + 1)) G := hdef.symm.trans hidx
    refine Sigma.ext hGConst ?_
    dsimp only [CategoryBar.barChain, CategoryBar.barCoeffR]
    let gtheta := G.map' n (n + 1) ≫ theta
    change HEq (G.map' n (n + 1) ≫
      (theta ≫ F.map (eqToHom hleftTop.symm))) _
    rw [eqToHom_map]
    have hTheta := CategoryTheory.comp_eqToHom_heq theta
      (congrArg F.obj hleftTop.symm)
    have hLeft : HEq (G.map' n (n + 1) ≫
        (theta ≫ eqToHom (congrArg F.obj hleftTop.symm))) gtheta :=
      CategoryTheory.heq_comp rfl rfl rfl HEq.rfl hTheta
    exact hLeft.trans
      ((CategoryTheory.comp_eqToHom_heq _ _).trans
        (cast_heq _ gtheta)).symm
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberSectionAppRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (q : Fin n)
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) (n + 1)) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).δ q.castSucc.succ
        (quillenASourceFiberSectionAppRaw F x (n + 1) z) =
      quillenASourceFiberSectionAppRaw F x n
        (CategoryBar.barδ q.castSucc.succ z) := by
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let k := (SimplexCategory.δ q.castSucc.succ).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  change (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberSectionAppRaw F x (n + 1)
              ⟨G, ULift.up PUnit.unit, theta⟩)) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        (quillenASourceFiberSectionAppRaw F x n
          (CategoryBar.barδ q.castSucc.succ
            ⟨G, ULift.up PUnit.unit, theta⟩))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberSectionAppRaw_objEquiv,
    quillenASourceFiberSectionAppRaw_objEquiv]
  rw [CategoryBar.barδ_castSucc_succ_eq]
  unfold quillenASourceFiberDecodedMapRaw
    quillenASourceFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F n).injective
    let alphaTop : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n + 1⦌ ⦋m⦌ (Fin.last m)
    let HTop : ComposableArrows C (n + 1) :=
      x.whiskerLeft alphaTop.toOrderHom.toFunctor
    let hleftTop : HTop.left = x.right :=
      quillenAConstLast_whisker_left x (n + 1)
    let thetaTop : G.right ⟶ F.obj HTop.left :=
      theta ≫ F.map (eqToHom hleftTop.symm)
    have hRaw := quillenAMappingCarrierRawEquiv_δ_inner_of F n q
      (⟨HTop, PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) (n + 1))
      (⟨G, ULift.up PUnit.unit, thetaTop⟩ :
        CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) (F.obj HTop.left))
          (CategoryBar.unitCoeffL D) (n + 1))
    change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        (quillenAMappingCarrierIncl F (n + 1) HTop G thetaTop)) = _ at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    apply (quillenAMappingCarrierRawToTriple F n).injective
    rw [quillenAMappingCarrierFaceInnerTripleOf_p4]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    dsimp only [alphaTop, HTop, hleftTop, thetaTop, id]
    let alphaFace : ⦋n⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
    let HFace : ComposableArrows C n :=
      x.whiskerLeft alphaFace.toOrderHom.toFunctor
    have hConst : SimplexCategory.δ q.castSucc.succ ≫ alphaTop =
        alphaFace := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext j
      rfl
    have hHConst : (StrictOmitDup.omitAt q.castSucc.succ).obj
        (x.whiskerLeft alphaTop.toOrderHom.toFunctor) = HFace := by
      change x.whiskerLeft
          (SimplexCategory.δ q.castSucc.succ ≫
            alphaTop).toOrderHom.toFunctor =
        x.whiskerLeft alphaFace.toOrderHom.toFunctor
      rw [hConst]
    refine Sigma.ext hHConst ?_
    apply heq_of_eq
    have hidx := quillenAMappingCarrierFaceInnerIndex_chain
      (C := D) n q ⟨G, PUnit.unit⟩
    have hdef : (StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit D) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q) ⟨G, PUnit.unit⟩).1 =
      (StrictOmitDup.omitAt q.castSucc.succ).obj G := rfl
    have hGConst : (StrictOmitDup.omitAt q.castSucc.succ).obj G =
        (nerve D).δ q.castSucc.succ G := hdef.symm.trans hidx
    refine Sigma.ext hGConst ?_
    dsimp only [CategoryBar.barChain, CategoryBar.barCoeffR]
    have hBridge := quillenABridgeFaceInnerThetaHEq
      F n q
        (x.whiskerLeft alphaTop.toOrderHom.toFunctor) G
        (theta ≫ F.map (eqToHom hleftTop.symm))
    have hTop : HEq (theta ≫ F.map (eqToHom hleftTop.symm)) theta := by
      rw [eqToHom_map]
      exact CategoryTheory.comp_eqToHom_heq theta
        (congrArg F.obj hleftTop.symm)
    have hLeft := hBridge.trans hTop
    refine hLeft.trans ?_
    symm
    rw [eqToHom_map]
    exact (CategoryTheory.comp_eqToHom_heq _ _).trans (cast_heq _ theta)
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberSectionAppRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (i : Fin (n + 1))
    (z : CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (CategoryBar.unitCoeffL D) n) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).σ i
        (quillenASourceFiberSectionAppRaw F x n z) =
      quillenASourceFiberSectionAppRaw F x (n + 1)
        (CategoryBar.barσ i z) := by
  rcases z with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  let k := (SimplexCategory.σ i).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌)).injective
  change (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberSectionAppRaw F x n
              ⟨G, ULift.up PUnit.unit, theta⟩)) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌))
        (quillenASourceFiberSectionAppRaw F x (n + 1)
          (CategoryBar.barσ i ⟨G, ULift.up PUnit.unit, theta⟩))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberSectionAppRaw_objEquiv,
    quillenASourceFiberSectionAppRaw_objEquiv]
  unfold CategoryBar.barσ
  unfold quillenASourceFiberDecodedMapRaw
    quillenASourceFiberSectionDecoded
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    let alphaTop : ⦋n⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
    let HTop : ComposableArrows C n :=
      x.whiskerLeft alphaTop.toOrderHom.toFunctor
    let hleftTop : HTop.left = x.right :=
      quillenAConstLast_whisker_left x n
    let thetaTop : G.right ⟶ F.obj HTop.left :=
      theta ≫ F.map (eqToHom hleftTop.symm)
    have hRaw := quillenAMappingCarrierRawEquiv_σ_of F n i
      (⟨HTop, PUnit.unit⟩ : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n)
      (⟨G, ULift.up PUnit.unit, thetaTop⟩ :
        CategoryBar.barObj D
          (CategoryBar.commaCoeffR (𝟭 D) (F.obj HTop.left))
          (CategoryBar.unitCoeffL D) n)
    change quillenAMappingCarrierRawEquiv F (n + 1)
      ((quillenAMappingCarrier F).map k
        (quillenAMappingCarrierIncl F n HTop G thetaTop)) = _ at hRaw
    dsimp only [k]
    rw [quillenAMappingCarrierRawEquiv_incl, hRaw]
    apply (quillenAMappingCarrierRawToTriple F (n + 1)).injective
    rw [quillenAMappingCarrierDegTripleOf_p4]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    dsimp only [alphaTop, HTop, hleftTop, thetaTop, id]
    let alphaDeg : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
      SimplexCategory.const ⦋n + 1⦌ ⦋m⦌ (Fin.last m)
    let HDeg : ComposableArrows C (n + 1) :=
      x.whiskerLeft alphaDeg.toOrderHom.toFunctor
    have hConst : SimplexCategory.σ i ≫ alphaTop = alphaDeg := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext j
      rfl
    have hHConst : (StrictOmitDup.dupAt i).obj
        (x.whiskerLeft alphaTop.toOrderHom.toFunctor) = HDeg := by
      change x.whiskerLeft
          (SimplexCategory.σ i ≫ alphaTop).toOrderHom.toFunctor =
        x.whiskerLeft alphaDeg.toOrderHom.toFunctor
      rw [hConst]
    refine Sigma.ext hHConst ?_
    apply heq_of_eq
    have hidx := quillenAMappingCarrierDegIndex_chain
      (C := D) n i ⟨G, PUnit.unit⟩
    have hdef : (StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit D) n i ⟨G, PUnit.unit⟩).1 =
      (StrictOmitDup.dupAt i).obj G := rfl
    have hGConst : (StrictOmitDup.dupAt i).obj G =
        (nerve D).σ i G := hdef.symm.trans hidx
    refine Sigma.ext hGConst ?_
    dsimp only [CategoryBar.barChain, CategoryBar.barCoeffR]
    have hBridge := quillenABridgeDegInnerThetaHEq
      F n i (x.whiskerLeft alphaTop.toOrderHom.toFunctor) G
        (theta ≫ F.map (eqToHom hleftTop.symm))
    have hTop : HEq (theta ≫ F.map (eqToHom hleftTop.symm)) theta := by
      rw [eqToHom_map]
      exact CategoryTheory.comp_eqToHom_heq theta
        (congrArg F.obj hleftTop.symm)
    have hLeft := hBridge.trans hTop
    refine hLeft.trans ?_
    symm
    rw [eqToHom_map]
    exact (CategoryTheory.comp_eqToHom_heq _ _).trans (cast_heq _ theta)
  · apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rfl

private noncomputable def quillenASourceFiberSectionAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m)
    (a : SimplexCategoryᵒᵖ) :
    (CategoryBar.categoryBar
      (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
      (L := CategoryBar.unitCoeffL D)).obj a ⟶
      (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenASourceFiberSectionAppRaw F x n)

private noncomputable def quillenASourceFiberSection
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D) ⟶
      SSet.leftFiber (quillenASource F) (quillenAChainAsNerve C x) where
  app a := quillenASourceFiberSectionAppNat F x a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      (CategoryBar.categoryBar
          (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
          (L := CategoryBar.unitCoeffL D)).map f.op ≫
          quillenASourceFiberSectionAppNat F x (op A) =
        quillenASourceFiberSectionAppNat F x (op B) ≫
          (SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberSectionAppNat F x (op ⦋n⦌)
          ((CategoryBar.categoryBar
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D)).map
              (SimplexCategory.δ i).op z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map
            (SimplexCategory.δ i).op
              (quillenASourceFiberSectionAppNat F x
                (op ⦋n + 1⦌) z)
      rw [CategoryBar.categoryBar_map_δ]
      change quillenASourceFiberSectionAppRaw F x n
          (CategoryBar.barδ i z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).δ i
            (quillenASourceFiberSectionAppRaw F x (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact (quillenASourceFiberSectionAppRaw_delta_zero
          F x n z).symm
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact (quillenASourceFiberSectionAppRaw_delta_last
            F x n z).symm
        · exact (quillenASourceFiberSectionAppRaw_delta_inner
            F x n q z).symm
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberSectionAppNat F x (op ⦋n + 1⦌)
          ((CategoryBar.categoryBar
            (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
            (L := CategoryBar.unitCoeffL D)).map
              (SimplexCategory.σ i).op z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map
            (SimplexCategory.σ i).op
              (quillenASourceFiberSectionAppNat F x (op ⦋n⦌) z)
      rw [CategoryBar.categoryBar_map_σ]
      change quillenASourceFiberSectionAppRaw F x (n + 1)
          (CategoryBar.barσ i z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).σ i
            (quillenASourceFiberSectionAppRaw F x n z)
      exact (quillenASourceFiberSectionAppRaw_sigma F x n i z).symm
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

private theorem quillenASourceFiberSection_retraction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    quillenASourceFiberSection F x ≫
        quillenASourceFiberRetraction F x =
      𝟙 (CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D)) := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenASourceFiberRetraction_section_app F x n z

private noncomputable def quillenASourceFiberRhoIndexMap
    {m : ℕ} (a : SimplexCategoryᵒᵖ)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a) : a.unop ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => if SSet.stdSimplex.asOrderHom t i = 0 then
        alpha.toOrderHom i else Fin.last m
      monotone' := by
        intro i j hij
        change (if SSet.stdSimplex.asOrderHom t i = 0 then
            alpha.toOrderHom i else Fin.last m) ≤
          (if SSet.stdSimplex.asOrderHom t j = 0 then
            alpha.toOrderHom j else Fin.last m)
        by_cases hj : SSet.stdSimplex.asOrderHom t j = 0
        · have hi : SSet.stdSimplex.asOrderHom t i = 0 := by
            apply le_antisymm
            · exact ((SSet.stdSimplex.asOrderHom t).monotone hij).trans_eq hj
            · exact Fin.zero_le _
          rw [ite_eq_left hi, ite_eq_left hj]
          exact alpha.toOrderHom.monotone hij
        · by_cases hi : SSet.stdSimplex.asOrderHom t i = 0
          · rw [ite_eq_left hi, ite_eq_right hj]
            exact Fin.le_last _
          · rw [ite_eq_right hi, ite_eq_right hj] }

private theorem quillenASourceFiberRhoIndexMap_le
    {m : ℕ} (a : SimplexCategoryᵒᵖ)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a)
    (i : Fin (a.unop.len + 1)) :
    alpha.toOrderHom i ≤
      (quillenASourceFiberRhoIndexMap a alpha t).toOrderHom i := by
  unfold quillenASourceFiberRhoIndexMap
  change alpha.toOrderHom i ≤
    (if SSet.stdSimplex.asOrderHom t i = 0 then
      alpha.toOrderHom i else Fin.last m)
  split
  · exact le_rfl
  · exact Fin.le_last _

private theorem quillenASourceFiberRhoIndexMap_precomp
    {m : ℕ} {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a) :
    quillenASourceFiberRhoIndexMap b (k.unop ≫ alpha)
        ((Δ[1] : SSet.{w}).map k t) =
      k.unop ≫ quillenASourceFiberRhoIndexMap a alpha t := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenASourceFiberRhoIndexMap
  rw [SSet.stdSimplex.map_apply]
  rfl

private theorem quillenASourceFiberRhoIndexMap_iota_zero
    {X : SSet.{w}} {m n : ℕ}
    (z : X.obj (op ⦋n⦌)) (alpha : ⦋n⦌ ⟶ ⦋m⦌) :
    quillenASourceFiberRhoIndexMap (op ⦋n⦌) alpha
        (SSet.ι₀.app (op ⦋n⦌) z).2 = alpha := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenASourceFiberRhoIndexMap
  change (if (SSet.ι₀.app (op ⦋n⦌) z).2 i = 0 then
    alpha.toOrderHom i else Fin.last m) = alpha.toOrderHom i
  simp

private theorem quillenASourceFiberRhoIndexMap_iota_one
    {X : SSet.{w}} {m n : ℕ}
    (z : X.obj (op ⦋n⦌)) (alpha : ⦋n⦌ ⟶ ⦋m⦌) :
    quillenASourceFiberRhoIndexMap (op ⦋n⦌) alpha
        (SSet.ι₁.app (op ⦋n⦌) z).2 =
      SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenASourceFiberRhoIndexMap
  change (if (SSet.ι₁.app (op ⦋n⦌) z).2 i = 0 then
    alpha.toOrderHom i else Fin.last m) = Fin.last m
  simp

private def quillenASourceFiberConnector
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m) (alpha beta : ⦋n⦌ ⟶ ⦋m⦌)
    (hle : ∀ i, alpha.toOrderHom i ≤ beta.toOrderHom i)
    (H : ComposableArrows C n)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor) :
    H.left ⟶ (x.whiskerLeft beta.toOrderHom.toFunctor).left :=
  eqToHom (congrArg ComposableArrows.left hH) ≫
    x.map' (alpha.toOrderHom 0).val (beta.toOrderHom 0).val
      (Fin.le_iff_val_le_val.mp (hle 0))
      (Nat.le_of_lt_succ (beta.toOrderHom 0).isLt)

private theorem quillenASourceFiberConnector_congr
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m)
    {alpha alpha' beta beta' : ⦋n⦌ ⟶ ⦋m⦌}
    {H H' : ComposableArrows C n}
    (ha : alpha = alpha') (hb : beta = beta') (hChain : H = H')
    (hle : ∀ i, alpha.toOrderHom i ≤ beta.toOrderHom i)
    (hle' : ∀ i, alpha'.toOrderHom i ≤ beta'.toOrderHom i)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH' : H' = x.whiskerLeft alpha'.toOrderHom.toFunctor) :
    HEq (quillenASourceFiberConnector x alpha beta hle H hH)
      (quillenASourceFiberConnector x alpha' beta' hle' H' hH') := by
  cases ha
  cases hb
  cases hChain
  have hp : hle = hle' := Subsingleton.elim _ _
  cases hp
  have hq : hH = hH' := Subsingleton.elim _ _
  cases hq
  exact HEq.rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberConnector_delta_zero
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m)
    (alpha beta : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hle : ∀ i, alpha.toOrderHom i ≤ beta.toOrderHom i)
    (H : ComposableArrows C (n + 1))
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH0 : (nerve C).δ 0 H = x.whiskerLeft
      (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).toOrderHom.toFunctor) :
    H.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le n)) ≫
        quillenASourceFiberConnector x
          (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha)
          (SimplexCategory.δ (0 : Fin (n + 2)) ≫ beta)
          (fun i => hle ((SimplexCategory.δ
            (0 : Fin (n + 2))).toOrderHom i))
          ((nerve C).δ 0 H) hH0 =
      quillenASourceFiberConnector x alpha beta hle H hH ≫
        (x.whiskerLeft beta.toOrderHom.toFunctor).map'
          0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le n)) := by
  subst H
  unfold quillenASourceFiberConnector
  simp only [eqToHom_refl, Category.id_comp]
  dsimp only [ComposableArrows.whiskerLeft, ComposableArrows.map']
  change x.map _ ≫ x.map _ = x.map _ ≫ x.map _
  rw [← x.map_comp, ← x.map_comp]
  apply congrArg x.map
  apply Subsingleton.elim

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberConnector_delta_last
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m)
    (alpha beta : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hle : ∀ i, alpha.toOrderHom i ≤ beta.toOrderHom i)
    (H : ComposableArrows C (n + 1))
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHl : (nerve C).δ (Fin.last (n + 1)) H = x.whiskerLeft
      (SimplexCategory.δ (Fin.last (n + 1)) ≫
        alpha).toOrderHom.toFunctor) :
    quillenASourceFiberConnector x
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ beta)
        (fun i => hle ((SimplexCategory.δ
          (Fin.last (n + 1))).toOrderHom i))
        ((nerve C).δ (Fin.last (n + 1)) H) hHl =
      quillenASourceFiberConnector x alpha beta hle H hH := by
  subst H
  unfold quillenASourceFiberConnector
  simp only [eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberConnector_delta_inner
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m) (q : Fin n)
    (alpha beta : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hle : ∀ i, alpha.toOrderHom i ≤ beta.toOrderHom i)
    (H : ComposableArrows C (n + 1))
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHi : (nerve C).δ q.castSucc.succ H = x.whiskerLeft
      (SimplexCategory.δ q.castSucc.succ ≫
        alpha).toOrderHom.toFunctor) :
    eqToHom (quillenABridgeFaceInnerLeftObj n q H) ≫
        quillenASourceFiberConnector x
          (SimplexCategory.δ q.castSucc.succ ≫ alpha)
          (SimplexCategory.δ q.castSucc.succ ≫ beta)
          (fun i => hle ((SimplexCategory.δ
            q.castSucc.succ).toOrderHom i))
          ((nerve C).δ q.castSucc.succ H) hHi =
      quillenASourceFiberConnector x alpha beta hle H hH := by
  subst H
  unfold quillenASourceFiberConnector
  simp only [eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberConnector_sigma
    {C : Type u} [Category.{v} C] {m n : ℕ}
    (x : ComposableArrows C m) (i : Fin (n + 1))
    (alpha beta : ⦋n⦌ ⟶ ⦋m⦌)
    (hle : ∀ j, alpha.toOrderHom j ≤ beta.toOrderHom j)
    (H : ComposableArrows C n)
    (hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hHs : (nerve C).σ i H = x.whiskerLeft
      (SimplexCategory.σ i ≫ alpha).toOrderHom.toFunctor) :
    eqToHom (quillenASourceFiberDegLeftObj i H) ≫
        quillenASourceFiberConnector x
          (SimplexCategory.σ i ≫ alpha)
          (SimplexCategory.σ i ≫ beta)
          (fun j => hle ((SimplexCategory.σ i).toOrderHom j))
          ((nerve C).σ i H) hHs =
      quillenASourceFiberConnector x alpha beta hle H hH := by
  subst H
  unfold quillenASourceFiberConnector
  simp only [eqToHom_refl, Category.id_comp]

private noncomputable def quillenASourceFiberRhoFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hH : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (⦋n⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)} := by
  let H : ComposableArrows C n := r.1.1
  let G : ComposableArrows D n := CategoryBar.barChain r.2
  let theta := CategoryBar.barCoeffR r.2
  let beta := quillenASourceFiberRhoIndexMap (op ⦋n⦌) alpha t
  let Ht := x.whiskerLeft beta.toOrderHom.toFunctor
  let k : H.left ⟶ Ht.left :=
    quillenASourceFiberConnector x alpha beta
      (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t) H hH
  let thetaT : G.right ⟶ F.obj Ht.left := theta ≫ F.map k
  exact ⟨⟨quillenAMappingCarrierIncl F n Ht G thetaT, beta⟩, by
    change (quillenASource F).app (op ⦋n⦌)
        (quillenAMappingCarrierIncl F n Ht G thetaT) =
      (nerve C).map beta.op (quillenAChainAsNerve C x)
    rw [quillenASource_carrierIncl]
    rfl⟩

private theorem quillenASourceFiberRhoFromRaw_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    {alpha alpha' : ⦋n⦌ ⟶ ⦋m⦌}
    {r r' : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)}
    (ha : alpha = alpha') (hr : r = r')
    (hH : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor)
    (hH' : r'.1.1 = x.whiskerLeft alpha'.toOrderHom.toFunctor)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenASourceFiberRhoFromRaw F x n alpha r hH t =
      quillenASourceFiberRhoFromRaw F x n alpha' r' hH' t := by
  cases ha
  cases hr
  rfl

private noncomputable def quillenASourceFiberRhoDecoded
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (⦋n⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) := by
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  have hH : r.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n d.1.1
    have h := hs.symm.trans d.2
    change r.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  exact quillenASourceFiberRhoFromRaw F x n d.1.2 r hH t

private noncomputable def quillenASourceFiberRhoAppRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌) :=
  (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).symm
      (quillenASourceFiberRhoDecoded F x n
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n⦌) zt.1) zt.2)

private theorem quillenASourceFiberRhoAppRaw_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n⦌)
        (quillenASourceFiberRhoAppRaw F x n zt) =
      quillenASourceFiberRhoDecoded F x n
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n⦌) zt.1) zt.2 := by
  unfold quillenASourceFiberRhoAppRaw
  rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoDecoded_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (⦋n + 1⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n + 1⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoDecoded F x n
        (quillenASourceFiberDecodedMapRaw F x
          (SimplexCategory.δ (0 : Fin (n + 2))).op d)
        ((Δ[1] : SSet.{max u v}).δ 0 t) =
      quillenASourceFiberDecodedMapRaw F x
        (SimplexCategory.δ (0 : Fin (n + 2))).op
          (quillenASourceFiberRhoDecoded F x (n + 1) d t) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  let e := quillenASourceFiberDecodedMapRaw F x k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hHTop : rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F (n + 1) d.1.1
    have h := hs.symm.trans d.2
    change rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hHFace : rFace.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n e.1.1
    have h := hs.symm.trans e.2
    change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
    exact h
  let p := rTop.1
  let z := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) z := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_zero_of F n p z
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) z)) = _ at hRaw
  let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n p,
      quillenAMappingCarrierFaceZeroInnerOf F n p z⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenASourceFiberDecodedMapRaw
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hRawE]
    exact hHFace
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n ((nerve C).δ 0 p.1),
      quillenAMappingCarrierInner F n ((nerve C).δ 0 p.1)
        ((nerve D).δ 0 (CategoryBar.barChain z))
        (CategoryBar.barCoeffR z ≫ F.map (p.1.map' 0 1))⟩
  have hCanonical : rExpected = rCanonical := by
    apply (quillenAMappingCarrierRawToTriple F n).injective
    rw [quillenAMappingCarrierFaceZeroTripleOf]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    rfl
  have hHCanonical : rCanonical.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hCanonical]
    exact hHExpected
  have hReplace := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hRawE hHFace hHExpected
      ((Δ[1] : SSet.{max u v}).δ 0 t)
  have hReplaceCanonical := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hCanonical
      hHExpected hHCanonical ((Δ[1] : SSet.{max u v}).δ 0 t)
  unfold quillenASourceFiberRhoDecoded
  change quillenASourceFiberRhoFromRaw F x n
      alphaFace rFace hHFace ((Δ[1] : SSet.{max u v}).δ 0 t) =
    quillenASourceFiberDecodedMapRaw F x k
      (quillenASourceFiberRhoFromRaw F x (n + 1)
        d.1.2 rTop hHTop t)
  calc
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rExpected hHExpected
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplace
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rCanonical hHCanonical
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplaceCanonical
    _ = _ := by
      unfold quillenASourceFiberRhoFromRaw
        quillenASourceFiberDecodedMapRaw
      dsimp only
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F n).injective
        let betaTop := quillenASourceFiberRhoIndexMap
          (op ⦋n + 1⦌) d.1.2 t
        let HtTop := x.whiskerLeft betaTop.toOrderHom.toFunctor
        let kTop : rTop.1.1.left ⟶ HtTop.left :=
          quillenASourceFiberConnector x d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n + 1⦌) d.1.2 t) rTop.1.1 hHTop
        let thetaTTop : (CategoryBar.barChain rTop.2).right ⟶
            F.obj HtTop.left := CategoryBar.barCoeffR rTop.2 ≫ F.map kTop
        have hOutRaw := quillenAMappingCarrierRawEquiv_δ_zero
          F n HtTop (CategoryBar.barChain rTop.2) thetaTTop
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            (quillenAMappingCarrierIncl F (n + 1) HtTop
              (CategoryBar.barChain rTop.2) thetaTTop)) = _ at hOutRaw
        rw [quillenAMappingCarrierRawEquiv_incl, hOutRaw]
        rw [quillenAMappingCarrierFaceZeroInner_eq_canonical]
        unfold rCanonical
        dsimp only [quillenAMappingCarrierInner, id]
        let betaFace := quillenASourceFiberRhoIndexMap
          (op ⦋n⦌) alphaFace ((Δ[1] : SSet.{max u v}).δ 0 t)
        have hBeta : betaFace = k.unop ≫ betaTop :=
          quillenASourceFiberRhoIndexMap_precomp k d.1.2 t
        have hHt : x.whiskerLeft betaFace.toOrderHom.toFunctor =
            (nerve C).δ 0 HtTop := by
          rw [hBeta]
          rfl
        have hp : quillenAMappingIndex n
              (x.whiskerLeft betaFace.toOrderHom.toFunctor) =
            StrictOrdinaryWeightedBar.wFaceZeroIdx
              (CategoryBar.replUnit C) n
                (quillenAMappingIndex (n + 1) HtTop) := by
          refine Sigma.ext (hHt.trans
            (quillenAMappingCarrierFaceZeroIndex_chain n
              (quillenAMappingIndex (n + 1) HtTop)).symm) ?_
          change HEq (_ : PUnit) (_ : PUnit)
          exact heq_of_eq (Subsingleton.elim _ _)
        refine Sigma.ext hp ?_
        apply heq_of_eq
        refine Sigma.ext ?_ ?_
        · rfl
        · apply quillenAProd_heq
          · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
            exact heq_of_eq (Subsingleton.elim _ _)
          · unfold thetaTTop kTop
            simp only [CategoryBar.barCoeffR, Category.assoc]
            congr! 1
            rw [← F.map_comp, ← F.map_comp]
            apply congrArg F.map
            have hH0 : (nerve C).δ 0 rTop.1.1 = x.whiskerLeft
                (SimplexCategory.δ (0 : Fin (n + 2)) ≫
                  d.1.2).toOrderHom.toFunctor := by
              simpa only [rCanonical, alphaFace, p] using hHCanonical
            have hconn := quillenASourceFiberConnector_delta_zero
              x d.1.2 betaTop
                (quillenASourceFiberRhoIndexMap_le
                  (op ⦋n + 1⦌) d.1.2 t)
                rTop.1.1 hHTop hH0
            have hEAlpha : e.1.2 = k.unop ≫ d.1.2 := rfl
            have hEBeta : quillenASourceFiberRhoIndexMap (op ⦋n⦌)
                e.1.2 ((Δ[1] : SSet.{max u v}).δ 0 t) =
              k.unop ≫ betaTop := by
              calc
                _ = quillenASourceFiberRhoIndexMap (op ⦋n⦌)
                    (k.unop ≫ d.1.2)
                    ((Δ[1] : SSet.{max u v}).δ 0 t) :=
                  congrArg (fun a ↦ quillenASourceFiberRhoIndexMap
                    (op ⦋n⦌) a ((Δ[1] : SSet.{max u v}).δ 0 t)) hEAlpha
                _ = _ := quillenASourceFiberRhoIndexMap_precomp
                  k d.1.2 t
            have hChain : rCanonical.1.1 = (nerve C).δ 0 rTop.1.1 := rfl
            have hConn := quillenASourceFiberConnector_congr x
              hEAlpha hEBeta hChain
              (quillenASourceFiberRhoIndexMap_le
                (op ⦋n⦌) e.1.2 ((Δ[1] : SSet.{max u v}).δ 0 t))
              (fun i => quillenASourceFiberRhoIndexMap_le
                (op ⦋n + 1⦌) d.1.2 t
                  ((SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom i))
              hHCanonical hH0
            dsimp only [alphaFace]
            have hk : k.unop =
                SimplexCategory.δ (0 : Fin (n + 2)) := rfl
            cases hk
            have hMid := congrArg ComposableArrows.left hChain
            have hTarget := congrArg
              (fun b ↦ (x.whiskerLeft b.toOrderHom.toFunctor).left) hEBeta
            have hComp := CategoryTheory.heq_comp rfl hMid hTarget
              (HEq.rfl : HEq (rTop.1.1.map' 0 1) (rTop.1.1.map' 0 1)) hConn
            exact eq_of_heq (hComp.trans (heq_of_eq hconn))
      · exact quillenASourceFiberRhoIndexMap_precomp k d.1.2 t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x) ⊗
          (Δ[1] : SSet.{max u v})).δ 0 zt) =
      (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).δ 0
          (quillenASourceFiberRhoAppRaw F x (n + 1) zt) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  change quillenASourceFiberRhoDecoded F x n
      (SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  change quillenASourceFiberRhoDecoded F x n
      (quillenASourceFiberDecodedMapRaw F x k
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberRhoAppRaw F x (n + 1) zt))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  exact quillenASourceFiberRhoDecoded_delta_zero F x n
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1) zt.2

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoDecoded_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (⦋n + 1⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n + 1⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoDecoded F x n
        (quillenASourceFiberDecodedMapRaw F x
          (SimplexCategory.δ (Fin.last (n + 1))).op d)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) =
      quillenASourceFiberDecodedMapRaw F x
        (SimplexCategory.δ (Fin.last (n + 1))).op
          (quillenASourceFiberRhoDecoded F x (n + 1) d t) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  let e := quillenASourceFiberDecodedMapRaw F x k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hHTop : rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F (n + 1) d.1.1
    have h := hs.symm.trans d.2
    change rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hHFace : rFace.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n e.1.1
    have h := hs.symm.trans e.2
    change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
    exact h
  let p := rTop.1
  let z := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) z := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_last_of F n p z
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) z)) = _ at hRaw
  let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n p,
      quillenAMappingCarrierFaceLastInnerOf F n p z⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenASourceFiberDecodedMapRaw
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hRawE]
    exact hHFace
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n ((nerve C).δ (Fin.last (n + 1)) p.1),
      quillenAMappingCarrierInner F n
        ((nerve C).δ (Fin.last (n + 1)) p.1)
        ((nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain z))
        (eqToHom (quillenABridgeFaceLastRight n
            (CategoryBar.barChain z)) ≫
          (CategoryBar.barChain z).map' n (n + 1) ≫
          CategoryBar.barCoeffR z)⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      refine Sigma.ext
        (quillenAMappingCarrierFaceLastIndex_chain n p) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    apply heq_of_eq
    rcases rTop with ⟨⟨H, q⟩, z0⟩
    dsimp only [p, z] at *
    change PUnit at q
    obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
    change CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (CategoryBar.unitCoeffL D) (n + 1) at z0
    rcases z0 with ⟨G, l, theta⟩
    change ULift PUnit at l
    obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
    exact quillenAMappingCarrierFaceLastInner_eq_canonical F n H G theta
  have hHCanonical : rCanonical.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hCanonical]
    exact hHExpected
  have hReplace := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hRawE hHFace hHExpected
      ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  have hReplaceCanonical := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hCanonical
      hHExpected hHCanonical ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  unfold quillenASourceFiberRhoDecoded
  change quillenASourceFiberRhoFromRaw F x n
      alphaFace rFace hHFace ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) =
    quillenASourceFiberDecodedMapRaw F x k
      (quillenASourceFiberRhoFromRaw F x (n + 1)
        d.1.2 rTop hHTop t)
  calc
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rExpected hHExpected
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := hReplace
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rCanonical hHCanonical
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := hReplaceCanonical
    _ = _ := by
      unfold quillenASourceFiberRhoFromRaw
        quillenASourceFiberDecodedMapRaw
      dsimp only
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F n).injective
        let betaTop := quillenASourceFiberRhoIndexMap
          (op ⦋n + 1⦌) d.1.2 t
        let HtTop := x.whiskerLeft betaTop.toOrderHom.toFunctor
        let kTop : rTop.1.1.left ⟶ HtTop.left :=
          quillenASourceFiberConnector x d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n + 1⦌) d.1.2 t) rTop.1.1 hHTop
        let thetaTTop : (CategoryBar.barChain rTop.2).right ⟶
            F.obj HtTop.left := CategoryBar.barCoeffR rTop.2 ≫ F.map kTop
        have hOutRaw := quillenAMappingCarrierRawEquiv_δ_last
          F n HtTop (CategoryBar.barChain rTop.2) thetaTTop
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            (quillenAMappingCarrierIncl F (n + 1) HtTop
              (CategoryBar.barChain rTop.2) thetaTTop)) = _ at hOutRaw
        rw [quillenAMappingCarrierRawEquiv_incl, hOutRaw]
        rw [quillenAMappingCarrierFaceLastInner_eq_canonical]
        unfold rCanonical
        dsimp only [quillenAMappingCarrierInner, id]
        let betaFace := quillenASourceFiberRhoIndexMap
          (op ⦋n⦌) alphaFace ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
        have hBeta : betaFace = k.unop ≫ betaTop :=
          quillenASourceFiberRhoIndexMap_precomp k d.1.2 t
        have hHt : x.whiskerLeft betaFace.toOrderHom.toFunctor =
            (nerve C).δ (Fin.last (n + 1)) HtTop := by
          rw [hBeta]
          rfl
        have hp : quillenAMappingIndex n
              (x.whiskerLeft betaFace.toOrderHom.toFunctor) =
            StrictOrdinaryWeightedBar.wFaceLastIdx
              (CategoryBar.replUnit C) n
                (quillenAMappingIndex (n + 1) HtTop) := by
          refine Sigma.ext (hHt.trans
            (quillenAMappingCarrierFaceLastIndex_chain n
              (quillenAMappingIndex (n + 1) HtTop)).symm) ?_
          change HEq (_ : PUnit) (_ : PUnit)
          exact heq_of_eq (Subsingleton.elim _ _)
        refine Sigma.ext hp ?_
        apply heq_of_eq
        refine Sigma.ext ?_ ?_
        · rfl
        · apply quillenAProd_heq
          · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
            exact heq_of_eq (Subsingleton.elim _ _)
          · unfold thetaTTop kTop
            simp only [CategoryBar.barCoeffR, Category.assoc]
            congr! 1
      · exact quillenASourceFiberRhoIndexMap_precomp k d.1.2 t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x) ⊗
          (Δ[1] : SSet.{max u v})).δ (Fin.last (n + 1)) zt) =
      (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).δ (Fin.last (n + 1))
          (quillenASourceFiberRhoAppRaw F x (n + 1) zt) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  change quillenASourceFiberRhoDecoded F x n
      (SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  change quillenASourceFiberRhoDecoded F x n
      (quillenASourceFiberDecodedMapRaw F x k
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberRhoAppRaw F x (n + 1) zt))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  exact quillenASourceFiberRhoDecoded_delta_last F x n
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1) zt.2

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoDecoded_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (i : Fin (n + 1))
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (⦋n⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenASourceFiberRhoDecoded F x (n + 1)
        (quillenASourceFiberDecodedMapRaw F x
          (SimplexCategory.σ i).op d)
        ((Δ[1] : SSet.{max u v}).σ i t) =
      quillenASourceFiberDecodedMapRaw F x
        (SimplexCategory.σ i).op
          (quillenASourceFiberRhoDecoded F x n d t) := by
  let k := (SimplexCategory.σ i).op
  let e := quillenASourceFiberDecodedMapRaw F x k d
  let rTop := quillenAMappingCarrierRawEquiv F n d.1.1
  have hHTop : rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n d.1.1
    have h := hs.symm.trans d.2
    change rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  let rDeg := quillenAMappingCarrierRawEquiv F (n + 1) e.1.1
  let alphaDeg := e.1.2
  have hHDeg : rDeg.1.1 =
      x.whiskerLeft alphaDeg.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F (n + 1) e.1.1
    have h := hs.symm.trans e.2
    change rDeg.1.1 = x.whiskerLeft alphaDeg.toOrderHom.toFunctor at h
    exact h
  let p := rTop.1
  let z := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) z := by
    apply (quillenAMappingCarrierRawEquiv F n).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_σ_of F n i p z
  change quillenAMappingCarrierRawEquiv F (n + 1)
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            n p).app (op ⦋n⦌) z)) = _ at hRaw
  let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
    ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i p,
      quillenAMappingCarrierDegInnerOf F n i p z⟩
  have hRawE : rDeg = rExpected := by
    unfold rDeg e quillenASourceFiberDecodedMapRaw
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alphaDeg.toOrderHom.toFunctor := by
    rw [← hRawE]
    exact hHDeg
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n + 1⦌) :=
    ⟨quillenAMappingIndex (n + 1) ((nerve C).σ i p.1),
      quillenAMappingCarrierInner F (n + 1) ((nerve C).σ i p.1)
        ((nerve D).σ i (CategoryBar.barChain z))
        (eqToHom (quillenASourceFiberDegRightObj i
            (CategoryBar.barChain z)) ≫
          CategoryBar.barCoeffR z ≫
          F.map (eqToHom (quillenASourceFiberDegLeftObj i p.1)))⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      refine Sigma.ext (quillenAMappingCarrierDegIndex_chain n i p) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    apply heq_of_eq
    rcases rTop with ⟨⟨H, q⟩, z0⟩
    dsimp only [p, z] at *
    change PUnit at q
    obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
    change CategoryBar.barObj D
      (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
      (CategoryBar.unitCoeffL D) n at z0
    rcases z0 with ⟨G, l, theta⟩
    change ULift PUnit at l
    obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
    exact quillenAMappingCarrierDegInner_eq_canonical F n i H G theta
  have hHCanonical : rCanonical.1.1 =
      x.whiskerLeft alphaDeg.toOrderHom.toFunctor := by
    rw [← hCanonical]
    exact hHExpected
  have hReplace := quillenASourceFiberRhoFromRaw_congr
    F x (n + 1) (rfl : alphaDeg = alphaDeg) hRawE hHDeg hHExpected
      ((Δ[1] : SSet.{max u v}).σ i t)
  have hReplaceCanonical := quillenASourceFiberRhoFromRaw_congr
    F x (n + 1) (rfl : alphaDeg = alphaDeg) hCanonical
      hHExpected hHCanonical ((Δ[1] : SSet.{max u v}).σ i t)
  unfold quillenASourceFiberRhoDecoded
  change quillenASourceFiberRhoFromRaw F x (n + 1)
      alphaDeg rDeg hHDeg ((Δ[1] : SSet.{max u v}).σ i t) =
    quillenASourceFiberDecodedMapRaw F x k
      (quillenASourceFiberRhoFromRaw F x n d.1.2 rTop hHTop t)
  calc
    _ = quillenASourceFiberRhoFromRaw F x (n + 1)
        alphaDeg rExpected hHExpected
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplace
    _ = quillenASourceFiberRhoFromRaw F x (n + 1)
        alphaDeg rCanonical hHCanonical
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplaceCanonical
    _ = _ := by
      unfold quillenASourceFiberRhoFromRaw
        quillenASourceFiberDecodedMapRaw
      dsimp only
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
        let betaTop := quillenASourceFiberRhoIndexMap
          (op ⦋n⦌) d.1.2 t
        let HtTop := x.whiskerLeft betaTop.toOrderHom.toFunctor
        let kTop : rTop.1.1.left ⟶ HtTop.left :=
          quillenASourceFiberConnector x d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n⦌) d.1.2 t) rTop.1.1 hHTop
        let thetaTTop : (CategoryBar.barChain rTop.2).right ⟶
            F.obj HtTop.left := CategoryBar.barCoeffR rTop.2 ≫ F.map kTop
        have hOutRaw := quillenAMappingCarrierRawEquiv_σ
          F n i HtTop (CategoryBar.barChain rTop.2) thetaTTop
        change quillenAMappingCarrierRawEquiv F (n + 1)
          ((quillenAMappingCarrier F).map k
            (quillenAMappingCarrierIncl F n HtTop
              (CategoryBar.barChain rTop.2) thetaTTop)) = _ at hOutRaw
        rw [quillenAMappingCarrierRawEquiv_incl, hOutRaw]
        rw [quillenAMappingCarrierDegInner_eq_canonical]
        unfold rCanonical
        dsimp only [quillenAMappingCarrierInner, id]
        let betaDeg := quillenASourceFiberRhoIndexMap
          (op ⦋n + 1⦌) alphaDeg ((Δ[1] : SSet.{max u v}).σ i t)
        have hBeta : betaDeg = k.unop ≫ betaTop :=
          quillenASourceFiberRhoIndexMap_precomp k d.1.2 t
        have hHt : x.whiskerLeft betaDeg.toOrderHom.toFunctor =
            (nerve C).σ i HtTop := by
          rw [hBeta]
          rfl
        have hp : quillenAMappingIndex (n + 1)
              (x.whiskerLeft betaDeg.toOrderHom.toFunctor) =
            StrictOrdinaryWeightedBar.wDegInnerIdx
              (CategoryBar.replUnit C) n i
                (quillenAMappingIndex n HtTop) := by
          refine Sigma.ext (hHt.trans
            (quillenAMappingCarrierDegIndex_chain n i
              (quillenAMappingIndex n HtTop)).symm) ?_
          change HEq (_ : PUnit) (_ : PUnit)
          exact heq_of_eq (Subsingleton.elim _ _)
        refine Sigma.ext hp ?_
        apply heq_of_eq
        refine Sigma.ext ?_ ?_
        · rfl
        · apply quillenAProd_heq
          · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
            exact heq_of_eq (Subsingleton.elim _ _)
          · unfold thetaTTop kTop
            have hHs : (nerve C).σ i rTop.1.1 = x.whiskerLeft
                (SimplexCategory.σ i ≫ d.1.2).toOrderHom.toFunctor := by
              simpa only [rCanonical, alphaDeg, p] using hHCanonical
            have hconn := quillenASourceFiberConnector_sigma
              x i d.1.2 betaTop
                (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) d.1.2 t)
                rTop.1.1 hHTop hHs
            have hEAlpha : e.1.2 = k.unop ≫ d.1.2 := rfl
            have hEBeta : quillenASourceFiberRhoIndexMap (op ⦋n + 1⦌)
                e.1.2 ((Δ[1] : SSet.{max u v}).σ i t) =
              k.unop ≫ betaTop := by
              calc
                _ = quillenASourceFiberRhoIndexMap (op ⦋n + 1⦌)
                    (k.unop ≫ d.1.2) ((Δ[1] : SSet.{max u v}).σ i t) :=
                  congrArg (fun a ↦ quillenASourceFiberRhoIndexMap
                    (op ⦋n + 1⦌) a ((Δ[1] : SSet.{max u v}).σ i t)) hEAlpha
                _ = _ := quillenASourceFiberRhoIndexMap_precomp k d.1.2 t
            have hChain : rCanonical.1.1 = (nerve C).σ i rTop.1.1 := rfl
            have hConn := quillenASourceFiberConnector_congr x
              hEAlpha hEBeta hChain
              (quillenASourceFiberRhoIndexMap_le
                (op ⦋n + 1⦌) e.1.2 ((Δ[1] : SSet.{max u v}).σ i t))
              (fun j ↦ quillenASourceFiberRhoIndexMap_le
                (op ⦋n⦌) d.1.2 t
                  ((SimplexCategory.σ i).toOrderHom j))
              hHCanonical hHs
            dsimp only [alphaDeg]
            have hk : k.unop = SimplexCategory.σ i := rfl
            cases hk
            simp only [CategoryBar.barCoeffR, Category.assoc]
            congr 2
            rw [← F.map_comp, ← F.map_comp]
            apply congrArg F.map
            change eqToHom (quillenASourceFiberDegLeftObj i rTop.1.1) ≫
                quillenASourceFiberConnector x e.1.2
                  (quillenASourceFiberRhoIndexMap (op ⦋n + 1⦌)
                    e.1.2 ((Δ[1] : SSet.{max u v}).σ i t))
                  (quillenASourceFiberRhoIndexMap_le
                    (op ⦋n + 1⦌) e.1.2
                      ((Δ[1] : SSet.{max u v}).σ i t))
                  rCanonical.1.1 hHCanonical =
              kTop ≫ eqToHom (quillenASourceFiberDegLeftObj i HtTop)
            have hop : k.unop = SimplexCategory.σ i := rfl
            have hAlphaOp : k.unop ≫ d.1.2 =
                SimplexCategory.σ i ≫ d.1.2 :=
              congrArg (fun q ↦ q ≫ d.1.2) hop
            have hBetaOp : k.unop ≫ betaTop =
                SimplexCategory.σ i ≫ betaTop :=
              congrArg (fun q ↦ q ≫ betaTop) hop
            have hOpConn := quillenASourceFiberConnector_congr x
              hAlphaOp hBetaOp rfl
              (fun j ↦ quillenASourceFiberRhoIndexMap_le
                (op ⦋n⦌) d.1.2 t
                  ((SimplexCategory.σ i).toOrderHom j))
              (fun j ↦ quillenASourceFiberRhoIndexMap_le
                (op ⦋n⦌) d.1.2 t
                  ((SimplexCategory.σ i).toOrderHom j))
              hHs hHs
            have hConnEq := eq_of_heq (hConn.trans hOpConn)
            rw [hConnEq, hconn]
            exact eq_of_heq
              (CategoryTheory.comp_eqToHom_heq kTop
                (quillenABridgeDegInnerLeftObj n i HtTop)).symm
      · exact quillenASourceFiberRhoIndexMap_precomp k d.1.2 t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (i : Fin (n + 1))
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenASourceFiberRhoAppRaw F x (n + 1)
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x) ⊗
          (Δ[1] : SSet.{max u v})).σ i zt) =
      (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).σ i
          (quillenASourceFiberRhoAppRaw F x n zt) := by
  let k := (SimplexCategory.σ i).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n + 1⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  change quillenASourceFiberRhoDecoded F x (n + 1)
      (SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n + 1⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  change quillenASourceFiberRhoDecoded F x (n + 1)
      (quillenASourceFiberDecodedMapRaw F x k
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberRhoAppRaw F x n zt))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  exact quillenASourceFiberRhoDecoded_sigma F x n i
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌) zt.1) zt.2

private theorem quillenASourceFiberRhoDecoded_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (q : Fin n)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (⦋n + 1⦌ ⟶ ⦋m⦌) //
      (quillenASource F).app (op ⦋n + 1⦌) p.1 =
        (nerve C).map p.2.op (quillenAChainAsNerve C x)})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoDecoded F x n
        (quillenASourceFiberDecodedMapRaw F x
          (SimplexCategory.δ q.castSucc.succ).op d)
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
      quillenASourceFiberDecodedMapRaw F x
        (SimplexCategory.δ q.castSucc.succ).op
          (quillenASourceFiberRhoDecoded F x (n + 1) d t) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  let e := quillenASourceFiberDecodedMapRaw F x k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hHTop : rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F (n + 1) d.1.1
    have h := hs.symm.trans d.2
    change rTop.1.1 = x.whiskerLeft d.1.2.toOrderHom.toFunctor at h
    exact h
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hHFace : rFace.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n e.1.1
    have h := hs.symm.trans e.2
    change rFace.1.1 = x.whiskerLeft alphaFace.toOrderHom.toFunctor at h
    exact h
  let p := rTop.1
  let z := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) z := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_inner_of F n q p z
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) z)) = _ at hRaw
  let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q) p,
      quillenAMappingCarrierFaceInnerInnerOf F n q p z⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenASourceFiberDecodedMapRaw
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hRawE]
    exact hHFace
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n ((nerve C).δ q.castSucc.succ p.1),
      quillenAMappingCarrierInner F n ((nerve C).δ q.castSucc.succ p.1)
        ((nerve D).δ q.castSucc.succ (CategoryBar.barChain z))
        (eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain z)) ≫ CategoryBar.barCoeffR z ≫
          F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q p.1)))⟩
  have hCanonical : rExpected = rCanonical := by
    apply (quillenAMappingCarrierRawToTriple F n).injective
    rw [quillenAMappingCarrierFaceInnerTripleOf_p4]
    rw [quillenAMappingCarrierRawToTriple_apply_p4]
    rfl
  have hHCanonical : rCanonical.1.1 =
      x.whiskerLeft alphaFace.toOrderHom.toFunctor := by
    rw [← hCanonical]
    exact hHExpected
  have hReplace := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hRawE hHFace hHExpected
      ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  have hReplaceCanonical := quillenASourceFiberRhoFromRaw_congr
    F x n (rfl : alphaFace = alphaFace) hCanonical
      hHExpected hHCanonical ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  unfold quillenASourceFiberRhoDecoded
  change quillenASourceFiberRhoFromRaw F x n
      alphaFace rFace hHFace ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
    quillenASourceFiberDecodedMapRaw F x k
      (quillenASourceFiberRhoFromRaw F x (n + 1)
        d.1.2 rTop hHTop t)
  calc
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rExpected hHExpected
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := hReplace
    _ = quillenASourceFiberRhoFromRaw F x n
        alphaFace rCanonical hHCanonical
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := hReplaceCanonical
    _ = _ := by
      unfold quillenASourceFiberRhoFromRaw
        quillenASourceFiberDecodedMapRaw
      dsimp only
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F n).injective
        let betaTop := quillenASourceFiberRhoIndexMap
          (op ⦋n + 1⦌) d.1.2 t
        let HtTop := x.whiskerLeft betaTop.toOrderHom.toFunctor
        let kTop : rTop.1.1.left ⟶ HtTop.left :=
          quillenASourceFiberConnector x d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n + 1⦌) d.1.2 t) rTop.1.1 hHTop
        let thetaTTop : (CategoryBar.barChain rTop.2).right ⟶
            F.obj HtTop.left := CategoryBar.barCoeffR rTop.2 ≫ F.map kTop
        let betaFace := quillenASourceFiberRhoIndexMap
          (op ⦋n⦌) alphaFace ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
        let HtFace := x.whiskerLeft betaFace.toOrderHom.toFunctor
        let kFace : rCanonical.1.1.left ⟶ HtFace.left :=
          quillenASourceFiberConnector x alphaFace betaFace
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n⦌) alphaFace
                ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t))
            rCanonical.1.1 hHCanonical
        let GFace : ComposableArrows D n :=
          (nerve D).δ q.castSucc.succ (CategoryBar.barChain z)
        let thetaFaceBase : GFace.right ⟶ F.obj rCanonical.1.1.left :=
          eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain z)) ≫ CategoryBar.barCoeffR z ≫
              F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q p.1))
        let thetaTFace : GFace.right ⟶ F.obj HtFace.left :=
          thetaFaceBase ≫ F.map kFace
        change quillenAMappingCarrierRawEquiv F n
            (quillenAMappingCarrierIncl F n HtFace GFace thetaTFace) =
          quillenAMappingCarrierRawEquiv F n
            ((quillenAMappingCarrier F).map k
              (quillenAMappingCarrierIncl F (n + 1) HtTop
                (CategoryBar.barChain rTop.2) thetaTTop))
        have hOutRaw := quillenAMappingCarrierRawEquiv_δ_inner
          F n q HtTop (CategoryBar.barChain rTop.2) thetaTTop
        change quillenAMappingCarrierRawEquiv F n
          ((quillenAMappingCarrier F).map k
            (quillenAMappingCarrierIncl F (n + 1) HtTop
              (CategoryBar.barChain rTop.2) thetaTTop)) = _ at hOutRaw
        rw [quillenAMappingCarrierRawEquiv_incl, hOutRaw]
        apply (quillenAMappingCarrierRawToTriple F n).injective
        have hTriple : quillenAMappingCarrierRawToTriple F n
            ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
                (CategoryBar.replUnit C) n q.castSucc.succ
                  (quillenACastSucc_succ_ne_last q)
                  (quillenAMappingIndex (n + 1) HtTop),
              quillenAMappingCarrierFaceInnerInner F n q HtTop
                (CategoryBar.barChain rTop.2) thetaTTop⟩ =
            ⟨(StrictOmitDup.omitAt q.castSucc.succ).obj HtTop,
              (StrictOmitDup.omitAt q.castSucc.succ).obj
                (CategoryBar.barChain rTop.2),
              eqToHom (quillenABridgeFaceInnerRightObj n q
                  (CategoryBar.barChain rTop.2)) ≫ thetaTTop ≫
                F.map (eqToHom
                  (quillenABridgeFaceInnerLeftObj n q HtTop))⟩ := by
          unfold quillenAMappingCarrierFaceInnerInner
          dsimp only [id]
          simpa only [quillenAMappingCarrierInner,
            CategoryBar.barChain, CategoryBar.barCoeffR, id] using
            quillenAMappingCarrierFaceInnerTripleOf_p4 F n q
              (quillenAMappingIndex (n + 1) HtTop)
              (quillenAMappingCarrierInner F (n + 1) HtTop
                (CategoryBar.barChain rTop.2) thetaTTop)
        rw [hTriple]
        rw [quillenAMappingCarrierRawToTriple_apply_p4]
        have hBeta : betaFace = k.unop ≫ betaTop :=
          quillenASourceFiberRhoIndexMap_precomp k d.1.2 t
        have hHt : x.whiskerLeft betaFace.toOrderHom.toFunctor =
            (nerve C).δ q.castSucc.succ HtTop := by
          rw [hBeta]
          rfl
        refine Sigma.ext hHt ?_
        apply quillenASigma_heq HEq.rfl
        have hH0 : (nerve C).δ q.castSucc.succ rTop.1.1 = x.whiskerLeft
            (SimplexCategory.δ q.castSucc.succ ≫
              d.1.2).toOrderHom.toFunctor := by
          calc
            _ = rCanonical.1.1 := rfl
            _ = x.whiskerLeft alphaFace.toOrderHom.toFunctor := hHCanonical
            _ = _ := by rfl
        have hconn := quillenASourceFiberConnector_delta_inner
          x q d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n + 1⦌) d.1.2 t)
            rTop.1.1 hHTop hH0
        have hEAlpha : e.1.2 = k.unop ≫ d.1.2 := rfl
        have hEBeta : quillenASourceFiberRhoIndexMap (op ⦋n⦌)
            e.1.2 ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
          k.unop ≫ betaTop := by
          calc
            _ = quillenASourceFiberRhoIndexMap (op ⦋n⦌)
                (k.unop ≫ d.1.2)
                ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) :=
              congrArg (fun a ↦ quillenASourceFiberRhoIndexMap
                (op ⦋n⦌) a ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)) hEAlpha
            _ = _ := quillenASourceFiberRhoIndexMap_precomp
              k d.1.2 t
        have hChain : rCanonical.1.1 = (nerve C).δ q.castSucc.succ rTop.1.1 := rfl
        have hConn := quillenASourceFiberConnector_congr x
          hEAlpha hEBeta hChain
          (quillenASourceFiberRhoIndexMap_le
            (op ⦋n⦌) e.1.2 ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t))
          (fun i => quillenASourceFiberRhoIndexMap_le
            (op ⦋n + 1⦌) d.1.2 t
              ((SimplexCategory.δ q.castSucc.succ).toOrderHom i))
          hHCanonical hH0
        dsimp only [alphaFace]
        have hk : k.unop =
            SimplexCategory.δ q.castSucc.succ := rfl
        cases hk
        have hMid := congrArg ComposableArrows.left hChain
        have hTarget := congrArg
          (fun b ↦ (x.whiskerLeft b.toOrderHom.toFunctor).left) hEBeta
        have hComp := CategoryTheory.heq_comp rfl hMid hTarget
          (HEq.rfl : HEq
            (eqToHom (quillenABridgeFaceInnerLeftObj n q rTop.1.1))
            (eqToHom (quillenABridgeFaceInnerLeftObj n q rTop.1.1))) hConn
        have hRight := CategoryTheory.comp_eqToHom_heq
          (quillenASourceFiberConnector x d.1.2 betaTop
            (quillenASourceFiberRhoIndexMap_le
              (op ⦋n + 1⦌) d.1.2 t) rTop.1.1 hHTop)
          (quillenABridgeFaceInnerLeftObj n q HtTop)
        have hCore := (hComp.trans (heq_of_eq hconn)).trans hRight.symm
        have hMap : HEq
            (F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q rTop.1.1) ≫ kFace))
            (F.map (kTop ≫ eqToHom
              (quillenABridgeFaceInnerLeftObj n q HtTop))) := by
          have hTargetFull : HtFace.left =
              ((nerve C).δ q.castSucc.succ HtTop).left :=
            congrArg ComposableArrows.left hHt
          cases hTargetFull
          have hCoreEq := eq_of_heq hCore
          exact heq_of_eq (congrArg F.map hCoreEq)
        have hMapExpanded : HEq
            (F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q rTop.1.1)) ≫
              F.map kFace)
            (F.map kTop ≫ F.map (eqToHom
              (quillenABridgeFaceInnerLeftObj n q HtTop))) :=
          (heq_of_eq (F.map_comp _ _).symm).trans
            (hMap.trans (heq_of_eq (F.map_comp _ _)))
        simp only [CategoryBar.barCoeffR]
        dsimp only [thetaTFace, thetaFaceBase, GFace,
          kFace, thetaTTop, kTop, quillenAMappingCarrierInner, id]
        have hPrefix : HEq
            (eqToHom (quillenABridgeFaceInnerRightObj n q
              (CategoryBar.barChain z)) ≫ CategoryBar.barCoeffR z)
            (eqToHom (quillenABridgeFaceInnerRightObj n q
              (CategoryBar.barChain rTop.2)) ≫
                CategoryBar.barCoeffR rTop.2) := HEq.rfl
        have hFull := CategoryTheory.heq_comp rfl rfl rfl hPrefix hMapExpanded
        have hAssocLeft : HEq
            ((eqToHom (quillenABridgeFaceInnerRightObj n q
                (CategoryBar.barChain z)) ≫ CategoryBar.barCoeffR z ≫
              F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q rTop.1.1))) ≫
                F.map kFace)
            ((eqToHom (quillenABridgeFaceInnerRightObj n q
                (CategoryBar.barChain z)) ≫ CategoryBar.barCoeffR z) ≫
              (F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q rTop.1.1)) ≫
                  F.map kFace)) := by
          let aL := eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain z))
          let bL := CategoryBar.barCoeffR z
          let cL := F.map (eqToHom
            (quillenABridgeFaceInnerLeftObj n q rTop.1.1))
          let dL := F.map kFace
          change HEq ((aL ≫ (bL ≫ cL)) ≫ dL)
            ((aL ≫ bL) ≫ (cL ≫ dL))
          apply heq_of_eq
          calc
            _ = aL ≫ ((bL ≫ cL) ≫ dL) := Category.assoc _ _ _
            _ = aL ≫ (bL ≫ (cL ≫ dL)) :=
              congrArg (fun r ↦ aL ≫ r) (Category.assoc _ _ _)
            _ = (aL ≫ bL) ≫ (cL ≫ dL) :=
              (Category.assoc _ _ _).symm
        have hAssocRight : HEq
            (eqToHom (quillenABridgeFaceInnerRightObj n q
                (CategoryBar.barChain rTop.2)) ≫
              (CategoryBar.barCoeffR rTop.2 ≫ F.map kTop) ≫
                F.map (eqToHom
                  (quillenABridgeFaceInnerLeftObj n q HtTop)))
            ((eqToHom (quillenABridgeFaceInnerRightObj n q
                (CategoryBar.barChain rTop.2)) ≫
                  CategoryBar.barCoeffR rTop.2) ≫
              (F.map kTop ≫ F.map (eqToHom
                (quillenABridgeFaceInnerLeftObj n q HtTop)))) := by
          let aR := eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain rTop.2))
          let bR := CategoryBar.barCoeffR rTop.2
          let cR := F.map kTop
          let dR := F.map (eqToHom
            (quillenABridgeFaceInnerLeftObj n q HtTop))
          change HEq (aR ≫ ((bR ≫ cR) ≫ dR))
            ((aR ≫ bR) ≫ (cR ≫ dR))
          apply heq_of_eq
          calc
            _ = aR ≫ (bR ≫ (cR ≫ dR)) :=
              congrArg (fun r ↦ aR ≫ r) (Category.assoc _ _ _)
            _ = (aR ≫ bR) ≫ (cR ≫ dR) :=
              (Category.assoc _ _ _).symm
        exact hAssocLeft.trans (hFull.trans hAssocRight.symm)
      · exact quillenASourceFiberRhoIndexMap_precomp k d.1.2 t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (q : Fin n)
    (zt : (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenASourceFiberRhoAppRaw F x n
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x) ⊗
          (Δ[1] : SSet.{max u v})).δ q.castSucc.succ zt) =
      (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)).δ q.castSucc.succ
          (quillenASourceFiberRhoAppRaw F x (n + 1) zt) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  change quillenASourceFiberRhoDecoded F x n
      (SSet.leftFiber.objEquiv (quillenASource F)
        (quillenAChainAsNerve C x) (op ⦋n⦌)
          ((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  change quillenASourceFiberRhoDecoded F x n
      (quillenASourceFiberDecodedMapRaw F x k
        (SSet.leftFiber.objEquiv (quillenASource F)
          (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n⦌))
        ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).map k
            (quillenASourceFiberRhoAppRaw F x (n + 1) zt))
  rw [← quillenASourceFiberDecodedMapRaw_objEquiv F x k]
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  exact quillenASourceFiberRhoDecoded_delta_inner F x n q
    (SSet.leftFiber.objEquiv (quillenASource F)
      (quillenAChainAsNerve C x) (op ⦋n + 1⦌) zt.1) zt.2


private noncomputable def quillenASourceFiberRhoAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m)
    (a : SimplexCategoryᵒᵖ) :
    ((SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)) ⊗
      (Δ[1] : SSet.{max u v})).obj a ⟶
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenASourceFiberRhoAppRaw F x n)

private noncomputable def quillenASourceFiberRhoMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)) ⊗
        (Δ[1] : SSet.{max u v}) ⟶
      SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x) where
  app a := quillenASourceFiberRhoAppNat F x a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      ((SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)) ⊗
          (Δ[1] : SSet.{max u v})).map f.op ≫
          quillenASourceFiberRhoAppNat F x (op A) =
        quillenASourceFiberRhoAppNat F x (op B) ≫
          (SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberRhoAppRaw F x n
          (((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)) ⊗
            (Δ[1] : SSet.{max u v})).δ i z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).δ i
            (quillenASourceFiberRhoAppRaw F x (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact quillenASourceFiberRhoAppRaw_delta_zero F x n z
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact quillenASourceFiberRhoAppRaw_delta_last F x n z
        · exact quillenASourceFiberRhoAppRaw_delta_inner F x n q z
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenASourceFiberRhoAppRaw F x (n + 1)
          (((SSet.leftFiber (quillenASource F)
            (quillenAChainAsNerve C x)) ⊗
            (Δ[1] : SSet.{max u v})).σ i z) =
        (SSet.leftFiber (quillenASource F)
          (quillenAChainAsNerve C x)).σ i
            (quillenASourceFiberRhoAppRaw F x n z)
      exact quillenASourceFiberRhoAppRaw_sigma F x n i z
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_iota_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌)) :
    quillenASourceFiberRhoAppRaw F x n
        (SSet.ι₀.app (op ⦋n⦌) z) = z := by
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv]
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌) z
  change quillenASourceFiberRhoDecoded F x n d
      (SSet.ι₀.app (op ⦋n⦌) z).2 = d
  rcases d with ⟨⟨c, alpha⟩, hd⟩
  rcases hc : quillenAMappingCarrierObjEquiv F n c with ⟨H, G, theta⟩
  have hc' : c = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [hc, quillenAMappingCarrierObjEquiv_incl]
  subst c
  have hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor := by
    rw [quillenASource_carrierIncl] at hd
    exact hd
  let t0 : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌) :=
    (SSet.ι₀.app (op ⦋n⦌) z).2
  have hBeta := quillenASourceFiberRhoIndexMap_iota_zero z alpha
  let d0 : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n⦌) p.1 =
      (nerve C).map p.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨quillenAMappingCarrierIncl F n H G theta, alpha⟩, hd⟩
  unfold quillenASourceFiberRhoDecoded
  let r := quillenAMappingCarrierRawEquiv F n d0.1.1
  let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
  have hRaw : r = rExpected :=
    quillenAMappingCarrierRawEquiv_incl F n H G theta
  have hHActual : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n d0.1.1
    exact hs.symm.trans hd
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hReplace := quillenASourceFiberRhoFromRaw_congr F x n
    (rfl : alpha = alpha) hRaw hHActual hHExpected t0
  change quillenASourceFiberRhoFromRaw F x n alpha r hHActual t0 = d0
  calc
    _ = quillenASourceFiberRhoFromRaw F x n
        alpha rExpected hHExpected t0 := hReplace
    _ = d0 := by
      unfold quillenASourceFiberRhoFromRaw
      dsimp only [id]
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierObjEquiv F n).injective
        rw [quillenAMappingCarrierObjEquiv_incl,
          quillenAMappingCarrierObjEquiv_incl]
        let beta := quillenASourceFiberRhoIndexMap (op ⦋n⦌) alpha t0
        have hChain : x.whiskerLeft beta.toOrderHom.toFunctor = H :=
          (congrArg (fun a ↦ x.whiskerLeft a.toOrderHom.toFunctor) hBeta).trans hH.symm
        have hConn := quillenASourceFiberConnector_congr x
          (rfl : alpha = alpha) hBeta hH
          (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t0)
          (fun _ => le_rfl) hH rfl
        have hCanonical : quillenASourceFiberConnector x alpha alpha
            (fun _ => le_rfl) (x.whiskerLeft alpha.toOrderHom.toFunctor) rfl =
            𝟙 (x.whiskerLeft alpha.toOrderHom.toFunctor).left := by
          unfold quillenASourceFiberConnector
          rw [x.map'_self (alpha.toOrderHom 0).val
            (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt)]
          simp only [eqToHom_refl, Category.id_comp]
          change 𝟙 (x.obj (alpha.toOrderHom 0)) =
            𝟙 (x.obj (alpha.toOrderHom.toFunctor.obj 0))
          rfl
        have hIdH : HEq
            (𝟙 (x.whiskerLeft alpha.toOrderHom.toFunctor).left)
            (𝟙 H.left) := by
          cases hH
          rfl
        have hConnId : HEq
            (quillenASourceFiberConnector x alpha beta
              (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t0) H hH)
            (𝟙 H.left) := hConn.trans
              ((heq_of_eq hCanonical).trans hIdH)
        have hLeftObj := congrArg ComposableArrows.left hChain
        let eCast : H.left ⟶
            (x.whiskerLeft beta.toOrderHom.toFunctor).left :=
          eqToHom hLeftObj.symm
        have hIdCast : HEq (𝟙 H.left) eCast := by
          have h := CategoryTheory.comp_eqToHom_heq
            (𝟙 H.left) hLeftObj.symm
          have hIdComp : HEq ((𝟙 H.left) ≫ eCast) eCast :=
            heq_of_eq (Category.id_comp eCast)
          exact h.symm.trans hIdComp
        have hConnCast : HEq
            (quillenASourceFiberConnector x alpha beta
              (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t0) H hH)
            eCast := hConnId.trans hIdCast
        have hConnEq := eq_of_heq hConnCast
        have hTheta : HEq
            (theta ≫ F.map (quillenASourceFiberConnector x alpha beta
              (quillenASourceFiberRhoIndexMap_le
                (op ⦋n⦌) alpha t0) H hH)) theta := by
          rw [hConnEq]
          unfold eCast
          rw [eqToHom_map]
          exact CategoryTheory.comp_eqToHom_heq theta
            (congrArg F.obj hLeftObj.symm)
        refine Sigma.ext hChain ?_
        cases hChain
        dsimp only [rExpected, quillenAMappingCarrierInner,
          CategoryBar.barChain, CategoryBar.barCoeffR, id]
        exact quillenASigma_heq HEq.rfl hTheta
      · exact hBeta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenASourceFiberRhoAppRaw_iota_one
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) (n : ℕ)
    (z : (SSet.leftFiber (quillenASource F)
      (quillenAChainAsNerve C x)).obj (op ⦋n⦌)) :
    quillenASourceFiberRhoAppRaw F x n
        (SSet.ι₁.app (op ⦋n⦌) z) =
      quillenASourceFiberSectionAppRaw F x n
        (quillenASourceFiberRetractionAppRaw F x n z) := by
  apply (SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌)).injective
  rw [quillenASourceFiberRhoAppRaw_objEquiv,
    quillenASourceFiberSectionAppRaw_objEquiv]
  let d := SSet.leftFiber.objEquiv (quillenASource F)
    (quillenAChainAsNerve C x) (op ⦋n⦌) z
  change quillenASourceFiberRhoDecoded F x n d
      (SSet.ι₁.app (op ⦋n⦌) z).2 =
    quillenASourceFiberSectionDecoded F x n
      (quillenASourceFiberRetractionDecodedRaw F x n d)
  rcases d with ⟨⟨c, alpha⟩, hd⟩
  rcases hc : quillenAMappingCarrierObjEquiv F n c with ⟨H, G, theta⟩
  have hc' : c = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [hc, quillenAMappingCarrierObjEquiv_incl]
  subst c
  have hH : H = x.whiskerLeft alpha.toOrderHom.toFunctor := by
    rw [quillenASource_carrierIncl] at hd
    exact hd
  let t1 : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌) :=
    (SSet.ι₁.app (op ⦋n⦌) z).2
  have hBeta := quillenASourceFiberRhoIndexMap_iota_one z alpha
  let d0 : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenASource F).app (op ⦋n⦌) p.1 =
      (nerve C).map p.2.op (quillenAChainAsNerve C x)} :=
    ⟨⟨quillenAMappingCarrierIncl F n H G theta, alpha⟩, hd⟩
  unfold quillenASourceFiberRhoDecoded
    quillenASourceFiberRetractionDecodedRaw
  let r := quillenAMappingCarrierRawEquiv F n d0.1.1
  let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨⟨H, PUnit.unit⟩, ⟨G, ULift.up PUnit.unit, theta⟩⟩
  have hRaw : r = rExpected :=
    quillenAMappingCarrierRawEquiv_incl F n H G theta
  have hHActual : r.1.1 = x.whiskerLeft alpha.toOrderHom.toFunctor := by
    have hs := quillenASource_eq_raw_chain F n d0.1.1
    exact hs.symm.trans hd
  have hHExpected : rExpected.1.1 =
      x.whiskerLeft alpha.toOrderHom.toFunctor := hH
  have hRhoReplace := quillenASourceFiberRhoFromRaw_congr F x n
    (rfl : alpha = alpha) hRaw hHActual hHExpected t1
  have hRetReplace := quillenASourceFiberRetractionFromRaw_congr F x n
    (rfl : alpha = alpha) hRaw hHActual hHExpected
  let T : Σ H : ComposableArrows C n,
      Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left :=
    ⟨H, G, theta⟩
  have hT : quillenAMappingCarrierRawToTriple F n rExpected = T :=
    quillenAMappingCarrierRawToTriple_apply_p4 F n
      ⟨H, PUnit.unit⟩ ⟨G, ULift.up PUnit.unit, theta⟩
  have hRetTriple := quillenASourceFiberRetractionFromRaw_eq_triple
    F x n alpha rExpected hHExpected T hT hH
  change quillenASourceFiberRhoFromRaw F x n alpha r hHActual t1 =
    quillenASourceFiberSectionDecoded F x n
      (quillenASourceFiberRetractionFromRaw F x n alpha r hHActual)
  calc
    _ = quillenASourceFiberRhoFromRaw F x n
        alpha rExpected hHExpected t1 := hRhoReplace
    _ = quillenASourceFiberSectionDecoded F x n
        (quillenASourceFiberRetractionPacket F x n alpha T hH) := by
      unfold quillenASourceFiberRhoFromRaw
        quillenASourceFiberRetractionPacket
        quillenASourceFiberRetractionFromTriple
        quillenASourceFiberSectionDecoded
      dsimp only [id]
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierObjEquiv F n).injective
        rw [quillenAMappingCarrierObjEquiv_incl,
          quillenAMappingCarrierObjEquiv_incl]
        let beta := quillenASourceFiberRhoIndexMap (op ⦋n⦌) alpha t1
        let alphaLast : ⦋n⦌ ⟶ ⦋m⦌ :=
          SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)
        let HLast : ComposableArrows C n :=
          x.whiskerLeft alphaLast.toOrderHom.toFunctor
        let hleft : HLast.left = x.right :=
          quillenAConstLast_whisker_left x n
        let kRet : H.left ⟶ x.right :=
          eqToHom (congrArg ComposableArrows.left hH) ≫
            x.map' (alpha.toOrderHom 0).val m
              (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
        let kRho : H.left ⟶
            (x.whiskerLeft beta.toOrderHom.toFunctor).left :=
          quillenASourceFiberConnector x alpha beta
            (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t1) H hH
        have hChain : x.whiskerLeft beta.toOrderHom.toFunctor = HLast :=
          congrArg (fun a ↦ x.whiskerLeft a.toOrderHom.toFunctor) hBeta
        have hConn := quillenASourceFiberConnector_congr x
          (rfl : alpha = alpha) hBeta rfl
          (quillenASourceFiberRhoIndexMap_le (op ⦋n⦌) alpha t1)
          (fun _ ↦ Fin.le_last _)
          hH hH
        have hCanonical : HEq
            (quillenASourceFiberConnector x alpha alphaLast
              (fun _ ↦ Fin.le_last _) H hH)
            (kRet ≫ eqToHom hleft.symm) := by
          unfold quillenASourceFiberConnector kRet
          let fConst := x.map' (alpha.toOrderHom 0).val
            (alphaLast.toOrderHom 0).val
              (Fin.le_iff_val_le_val.mp (Fin.le_last _))
              (Nat.le_of_lt_succ (alphaLast.toOrderHom 0).isLt)
          let fM := x.map' (alpha.toOrderHom 0).val m
            (Nat.le_of_lt_succ (alpha.toOrderHom 0).isLt) le_rfl
          have hMapConst : HEq fConst fM := by
            unfold fConst fM
            dsimp only [alphaLast]
            simp only [SimplexCategory.const_apply, Fin.val_last]
            exact HEq.rfl
          have hRight := CategoryTheory.comp_eqToHom_heq fM hleft.symm
          have hSuffix : HEq fConst (fM ≫ eqToHom hleft.symm) :=
            hMapConst.trans hRight.symm
          let eH := eqToHom (congrArg ComposableArrows.left hH)
          have hComp := CategoryTheory.heq_comp rfl rfl rfl
            (HEq.rfl : HEq eH eH) hSuffix
          have hAssoc := heq_of_eq
            (Category.assoc eH fM (eqToHom hleft.symm)).symm
          simpa only [eH] using hComp.trans hAssoc
        have hCore : HEq kRho (kRet ≫ eqToHom hleft.symm) :=
          hConn.trans hCanonical
        have hMap : HEq (F.map kRho)
            (F.map (kRet ≫ eqToHom hleft.symm)) := by
          have hTarget := congrArg ComposableArrows.left hChain
          cases hTarget
          exact heq_of_eq (congrArg F.map (eq_of_heq hCore))
        have hMapExpanded : HEq (F.map kRho)
            (F.map kRet ≫ F.map (eqToHom hleft.symm)) :=
          hMap.trans (heq_of_eq (F.map_comp _ _))
        have hTheta : HEq (theta ≫ F.map kRho)
            ((theta ≫ F.map kRet) ≫
              F.map (eqToHom hleft.symm)) := by
          have hComp := CategoryTheory.heq_comp rfl rfl rfl
            (HEq.rfl : HEq theta theta) hMapExpanded
          have hAssoc := heq_of_eq
            (Category.assoc theta (F.map kRet)
              (F.map (eqToHom hleft.symm))).symm
          exact hComp.trans hAssoc
        refine Sigma.ext hChain ?_
        cases hChain
        dsimp only [rExpected, T, alphaLast, HLast, hleft,
          kRet, quillenAMappingCarrierInner,
          CategoryBar.barChain, CategoryBar.barCoeffR, id]
        apply heq_of_eq
        refine Sigma.ext rfl ?_
        exact hTheta
      · exact hBeta
    _ = quillenASourceFiberSectionDecoded F x n
        (quillenASourceFiberRetractionFromRaw F x n
          alpha rExpected hHExpected) :=
      congrArg (quillenASourceFiberSectionDecoded F x n) hRetTriple.symm
    _ = _ := congrArg (quillenASourceFiberSectionDecoded F x n)
      hRetReplace.symm

private theorem quillenASourceFiberRhoMap_h0
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    SSet.ι₀ ≫ quillenASourceFiberRhoMap F x =
      𝟙 (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)) := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenASourceFiberRhoAppRaw_iota_zero F x n z

private theorem quillenASourceFiberRhoMap_h1
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    SSet.ι₁ ≫ quillenASourceFiberRhoMap F x =
      quillenASourceFiberRetraction F x ≫
        quillenASourceFiberSection F x := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenASourceFiberRhoAppRaw_iota_one F x n z

private noncomputable def quillenASourceFiberRhoHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    SSet.Homotopy
      (𝟙 (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)))
      (quillenASourceFiberRetraction F x ≫
        quillenASourceFiberSection F x) where
  h := quillenASourceFiberRhoMap F x
  h₀ := quillenASourceFiberRhoMap_h0 F x
  h₁ := quillenASourceFiberRhoMap_h1 F x
  rel := by
    ext a z
    exact z.1.2.elim

private theorem quillenARetraction_mem_realizationWeakEquivalences
    {A B : SSet.{w}} (r : A ⟶ B) (s : B ⟶ A)
    (hsr : s ≫ r = 𝟙 B)
    (H : SSet.Homotopy (𝟙 A) (r ≫ s)) :
    SSet.realizationWeakEquivalences r := by
  have hStrict : SSet.Homotopy (s ≫ r) (𝟙 B) := by
    rw [hsr]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 B))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 B))
    exact SSet.RelativeMorphism.Homotopy.refl _
  let e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj A) (SSet.toTop.obj B) :=
    { toFun := (SSet.toTop.map r).hom
      invFun := (SSet.toTop.map s).hom
      left_inv := by
        have h := SSet.realizeHomotopy _ _ (𝟙 A) (r ≫ s) H
        have h' : ContinuousMap.Homotopy
            ((SSet.toTop.map s).hom.comp (SSet.toTop.map r).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id] using h.symm
        exact ⟨h'⟩
      right_inv := by
        have h := SSet.realizeHomotopy _ _ (s ≫ r) (𝟙 B) hStrict
        have h' : ContinuousMap.Homotopy
            ((SSet.toTop.map r).hom.comp (SSet.toTop.map s).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id] using h
        exact ⟨h'⟩ }
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map r)
  exact TopCat.mem_of_eq_toFun e rfl

private theorem quillenARightCommaBar_to_terminal_mem
    {D : Type u} [Category.{v} D] (d : D) :
    SSet.realizationWeakEquivalences
      (terminal.from
        (CategoryBar.categoryBar
          (R := CategoryBar.commaCoeffR (𝟭 D) d)
          (L := CategoryBar.unitCoeffL D) : SSet.{max u v})) := by
  let i := CategoryBar.barRightCommaSimplicialIso (𝟭 D) d
  have hi : SSet.realizationWeakEquivalences i.hom :=
    MorphismProperty.of_isIso SSet.realizationWeakEquivalences i.hom
  have ht : SSet.realizationWeakEquivalences
      (terminal.from
        (nerve (CostructuredArrow (𝟭 D) d) : SSet.{max u v})) :=
    NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
      (CostructuredArrow.mkIdTerminal (S := 𝟭 D) (Y := d))
  have hc := SSet.realizationWeakEquivalences.comp_mem i.hom
    (terminal.from
      (nerve (CostructuredArrow (𝟭 D) d) : SSet.{max u v})) hi ht
  have heq : i.hom ≫ terminal.from
      (nerve (CostructuredArrow (𝟭 D) d) : SSet.{max u v}) =
      terminal.from
        (CategoryBar.categoryBar
          (R := CategoryBar.commaCoeffR (𝟭 D) d)
          (L := CategoryBar.unitCoeffL D) : SSet.{max u v}) :=
    Subsingleton.elim _ _
  rw [heq] at hc
  exact hc

private theorem quillenASourceFiber_to_terminal_mem
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ} (x : ComposableArrows C m) :
    SSet.realizationWeakEquivalences
      (terminal.from (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x))) := by
  have hr := quillenARetraction_mem_realizationWeakEquivalences
    (quillenASourceFiberRetraction F x)
    (quillenASourceFiberSection F x)
    (quillenASourceFiberSection_retraction F x)
    (quillenASourceFiberRhoHomotopy F x)
  have hb := quillenARightCommaBar_to_terminal_mem (F.obj x.right)
  have hc := SSet.realizationWeakEquivalences.comp_mem
    (quillenASourceFiberRetraction F x)
    (terminal.from
      (CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D))) hr hb
  have heq : quillenASourceFiberRetraction F x ≫ terminal.from
      (CategoryBar.categoryBar
        (R := CategoryBar.commaCoeffR (𝟭 D) (F.obj x.right))
        (L := CategoryBar.unitCoeffL D)) =
      terminal.from (SSet.leftFiber (quillenASource F)
        (quillenAChainAsNerve C x)) := Subsingleton.elim _ _
  rw [heq] at hc
  exact hc

private noncomputable def quillenATargetFiberRhoIndexMap
    {m : ℕ} (a : SimplexCategoryᵒᵖ)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a) : a.unop ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => if SSet.stdSimplex.asOrderHom t i = 0 then
        0 else alpha.toOrderHom i
      monotone' := by
        intro i j hij
        by_cases hi : SSet.stdSimplex.asOrderHom t i = 0
        · simp [hi]
        · have hj : SSet.stdSimplex.asOrderHom t j ≠ 0 := by
            intro hj
            apply hi
            apply le_antisymm
            · simpa only [hj] using
                (SSet.stdSimplex.asOrderHom t).monotone hij
            · exact Fin.zero_le _
          change (if SSet.stdSimplex.asOrderHom t i = 0 then 0 else
              alpha.toOrderHom i) ≤
            (if SSet.stdSimplex.asOrderHom t j = 0 then 0 else
              alpha.toOrderHom j)
          simp only [hi, hj]
          exact alpha.toOrderHom.monotone hij }

private theorem quillenATargetFiberRhoIndexMap_le
    {m : ℕ} (a : SimplexCategoryᵒᵖ)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a)
    (i : Fin (a.unop.len + 1)) :
    (quillenATargetFiberRhoIndexMap a alpha t).toOrderHom i ≤
      alpha.toOrderHom i := by
  unfold quillenATargetFiberRhoIndexMap
  change (if SSet.stdSimplex.asOrderHom t i = 0 then 0 else
    alpha.toOrderHom i) ≤ alpha.toOrderHom i
  split
  · exact Fin.zero_le _
  · exact le_rfl

private theorem quillenATargetFiberRhoIndexMap_precomp
    {m : ℕ} {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b)
    (alpha : a.unop ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj a) :
    quillenATargetFiberRhoIndexMap b (k.unop ≫ alpha)
        ((Δ[1] : SSet.{w}).map k t) =
      k.unop ≫ quillenATargetFiberRhoIndexMap a alpha t := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenATargetFiberRhoIndexMap
  rw [SSet.stdSimplex.map_apply]
  rfl

private noncomputable def quillenATargetFiberRhoBetaTop
    {m n : ℕ} (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
  quillenATargetFiberRhoIndexMap (op ⦋n + 1⦌) alpha t

private noncomputable def quillenATargetFiberRhoBetaFaceZero
    {m n : ℕ} (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  quillenATargetFiberRhoIndexMap (op ⦋n⦌)
    (SimplexCategory.δ 0 ≫ alpha) ((Δ[1] : SSet.{w}).δ 0 t)

private theorem quillenATargetFiberRhoIndexMap_delta_zero
    {m n : ℕ} (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoBetaFaceZero alpha t =
      SimplexCategory.δ (0 : Fin (n + 2)) ≫
        quillenATargetFiberRhoBetaTop alpha t := by
  unfold quillenATargetFiberRhoBetaFaceZero
    quillenATargetFiberRhoBetaTop
  exact quillenATargetFiberRhoIndexMap_precomp
    (SimplexCategory.δ (0 : Fin (n + 2))).op alpha t

private theorem quillenATargetFiberRhoChain_delta_zero
    {D : Type u} [Category.{v} D] {m n : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).map (quillenATargetFiberRhoBetaFaceZero alpha t).op y =
      (nerve D).δ 0
        ((nerve D).map (quillenATargetFiberRhoBetaTop alpha t).op y) := by
  have hBeta := quillenATargetFiberRhoIndexMap_delta_zero alpha t
  rw [hBeta]
  exact ConcreteCategory.congr_hom
    ((nerve D).map_comp
      (quillenATargetFiberRhoBetaTop alpha t).op
      (SimplexCategory.δ (0 : Fin (n + 2))).op) y

private noncomputable def quillenATargetFiberRhoBetaFaceLast
    {m n : ℕ} (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  quillenATargetFiberRhoIndexMap (op ⦋n⦌)
    (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
      ((Δ[1] : SSet.{w}).δ (Fin.last (n + 1)) t)

private theorem quillenATargetFiberRhoIndexMap_delta_last
    {m n : ℕ} (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoBetaFaceLast alpha t =
      SimplexCategory.δ (Fin.last (n + 1)) ≫
        quillenATargetFiberRhoBetaTop alpha t := by
  unfold quillenATargetFiberRhoBetaFaceLast
    quillenATargetFiberRhoBetaTop
  exact quillenATargetFiberRhoIndexMap_precomp
    (SimplexCategory.δ (Fin.last (n + 1))).op alpha t

private theorem quillenATargetFiberRhoChain_delta_last
    {D : Type u} [Category.{v} D] {m n : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).map (quillenATargetFiberRhoBetaFaceLast alpha t).op y =
      (nerve D).δ (Fin.last (n + 1))
        ((nerve D).map (quillenATargetFiberRhoBetaTop alpha t).op y) := by
  have hBeta := quillenATargetFiberRhoIndexMap_delta_last alpha t
  rw [hBeta]
  exact ConcreteCategory.congr_hom
    ((nerve D).map_comp
      (quillenATargetFiberRhoBetaTop alpha t).op
      (SimplexCategory.δ (Fin.last (n + 1))).op) y

private noncomputable def quillenATargetFiberRhoBetaFaceInner
    {m n : ℕ} (q : Fin n) (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  quillenATargetFiberRhoIndexMap (op ⦋n⦌)
    (SimplexCategory.δ q.castSucc.succ ≫ alpha)
      ((Δ[1] : SSet.{w}).δ q.castSucc.succ t)

private theorem quillenATargetFiberRhoIndexMap_delta_inner
    {m n : ℕ} (q : Fin n) (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoBetaFaceInner q alpha t =
      SimplexCategory.δ q.castSucc.succ ≫
        quillenATargetFiberRhoBetaTop alpha t := by
  unfold quillenATargetFiberRhoBetaFaceInner
    quillenATargetFiberRhoBetaTop
  exact quillenATargetFiberRhoIndexMap_precomp
    (SimplexCategory.δ q.castSucc.succ).op alpha t

private theorem quillenATargetFiberRhoChain_delta_inner
    {D : Type u} [Category.{v} D] {m n : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (q : Fin n)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (nerve D).map (quillenATargetFiberRhoBetaFaceInner q alpha t).op y =
      (nerve D).δ q.castSucc.succ
        ((nerve D).map (quillenATargetFiberRhoBetaTop alpha t).op y) := by
  have hBeta := quillenATargetFiberRhoIndexMap_delta_inner q alpha t
  rw [hBeta]
  exact ConcreteCategory.congr_hom
    ((nerve D).map_comp
      (quillenATargetFiberRhoBetaTop alpha t).op
      (SimplexCategory.δ q.castSucc.succ).op) y

private noncomputable def quillenATargetFiberRhoBetaDeg
    {m n : ℕ} (i : Fin (n + 1)) (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n⦌)) : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
  quillenATargetFiberRhoIndexMap (op ⦋n + 1⦌)
    (SimplexCategory.σ i ≫ alpha) ((Δ[1] : SSet.{w}).σ i t)

private theorem quillenATargetFiberRhoIndexMap_sigma
    {m n : ℕ} (i : Fin (n + 1)) (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{w}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoBetaDeg i alpha t =
      SimplexCategory.σ i ≫
        quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t := by
  unfold quillenATargetFiberRhoBetaDeg
  exact quillenATargetFiberRhoIndexMap_precomp
    (SimplexCategory.σ i).op alpha t

private theorem quillenATargetFiberRhoChain_sigma
    {D : Type u} [Category.{v} D] {m n : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (i : Fin (n + 1))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (nerve D).map (quillenATargetFiberRhoBetaDeg i alpha t).op y =
      (nerve D).σ i
        ((nerve D).map
          (quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t).op y) := by
  have hBeta := quillenATargetFiberRhoIndexMap_sigma i alpha t
  rw [hBeta]
  exact ConcreteCategory.congr_hom
    ((nerve D).map_comp
      (quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t).op
      (SimplexCategory.σ i).op) y

private theorem quillenATargetFiberRhoIndexMap_iota_zero
    {X : SSet.{w}} {m n : ℕ}
    (x : X.obj (op ⦋n⦌)) (alpha : ⦋n⦌ ⟶ ⦋m⦌) :
    quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha
        (SSet.ι₀.app (op ⦋n⦌) x).2 =
      quillenATargetFiberFirstVertexMap m n := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenATargetFiberRhoIndexMap
    quillenATargetFiberFirstVertexMap
  change (if (SSet.ι₀.app (op ⦋n⦌) x).2 i = 0 then 0 else
    alpha.toOrderHom i) = 0
  simp

private theorem quillenATargetFiberRhoIndexMap_iota_one
    {X : SSet.{w}} {m n : ℕ}
    (x : X.obj (op ⦋n⦌)) (alpha : ⦋n⦌ ⟶ ⦋m⦌) :
    quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha
        (SSet.ι₁.app (op ⦋n⦌) x).2 = alpha := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  unfold quillenATargetFiberRhoIndexMap
  change (if (SSet.ι₁.app (op ⦋n⦌) x).2 i = 0 then 0 else
    alpha.toOrderHom i) = alpha.toOrderHom i
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceZeroInnerOf_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierFaceZeroInnerOf F n p x =
      quillenAMappingCarrierInner F n ((nerve C).δ 0 p.1)
        ((nerve D).δ 0 (CategoryBar.barChain x))
        (CategoryBar.barCoeffR x ≫ F.map (p.1.map' 0 1)) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenAMappingCarrierFaceZeroInner_eq_canonical
    F n H G theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceLastInnerOf_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierFaceLastInnerOf F n p x =
      quillenAMappingCarrierInner F n
        ((nerve C).δ (Fin.last (n + 1)) p.1)
        ((nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x))
        (eqToHom (quillenABridgeFaceLastRight n
            (CategoryBar.barChain x)) ≫
          (CategoryBar.barChain x).map' n (n + 1) ≫
          CategoryBar.barCoeffR x) := by
  rcases p with ⟨H, q⟩
  change PUnit at q
  obtain rfl : q = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenAMappingCarrierFaceLastInner_eq_canonical F n H G theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierFaceInnerInnerOf_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj
      (op ⦋n + 1⦌)) :
    quillenAMappingCarrierFaceInnerInnerOf F n q p x =
      quillenAMappingCarrierInner F n
        ((nerve C).δ q.castSucc.succ p.1)
        ((nerve D).δ q.castSucc.succ (CategoryBar.barChain x))
        (eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
          F.map (eqToHom
            (quillenABridgeFaceInnerLeftObj n q p.1))) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) (n + 1) at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  refine Sigma.ext (quillenAMappingCarrierFaceInnerInner_chain
    F n q H G theta) ?_
  apply quillenAProd_heq
  · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · exact (quillenAMappingCarrierFaceInnerInner_theta
      F n q H G theta).trans
      (quillenABridgeFaceInnerThetaHEq F n q H G theta).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : G = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ 0 G =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    have hRightTop : G.right =
        y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
      (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
    have hRightFace : ((nerve D).δ 0 G).right =
        y.obj ((SimplexCategory.δ 0 ≫ alpha).toOrderHom (Fin.last n)) :=
      (congrArg (fun K : ComposableArrows D n ↦ K.right) hGFace).trans rfl
    HEq
      (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n⦌) (SimplexCategory.δ 0 ≫ alpha)
            ((Δ[1] : SSet.{max u v}).δ 0 t) (Fin.last n))) ≫
        eqToHom hRightFace.symm ≫
          (theta ≫ F.map (H.map' 0 1)))
      ((y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
        eqToHom hRightTop.symm ≫ theta) ≫
          F.map (H.map' 0 1)) := by
  dsimp only
  simp only [Category.assoc]
  congr! 1

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : G = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ q.castSucc.succ G =
      (nerve D).map
        (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    have hRightTop : G.right =
        y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
      (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
    have hRightFace : ((nerve D).δ q.castSucc.succ G).right =
        y.obj ((SimplexCategory.δ q.castSucc.succ ≫
          alpha).toOrderHom (Fin.last n)) :=
      (congrArg (fun K : ComposableArrows D n ↦ K.right) hGFace).trans rfl
    HEq
      (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n⦌) (SimplexCategory.δ q.castSucc.succ ≫ alpha)
            ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
              (Fin.last n))) ≫
        eqToHom hRightFace.symm ≫
          (eqToHom (quillenABridgeFaceInnerRightObj n q G) ≫ theta ≫
            F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))))
      (eqToHom (quillenABridgeFaceInnerRightObj n q
          ((nerve D).map
            (quillenATargetFiberRhoBetaTop alpha t).op y)) ≫
        (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
            eqToHom hRightTop.symm ≫ theta) ≫
        F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))) := by
  /-
  subst G
  let beta := quillenATargetFiberRhoBetaTop alpha t
  let betaFace := quillenATargetFiberRhoBetaFaceInner q alpha t
  have hBeta := quillenATargetFiberRhoIndexMap_delta_inner q alpha t
  have hBetaLast : betaFace.toOrderHom (Fin.last n) =
      beta.toOrderHom (Fin.last (n + 1)) := by
    calc
      _ = (SimplexCategory.δ q.castSucc.succ ≫
          beta).toOrderHom (Fin.last n) :=
        congrArg (fun gamma ↦ gamma.toOrderHom (Fin.last n)) hBeta
      _ = _ := congrArg beta.toOrderHom
        (quillenABridgeFaceInnerLast n q)
  have hAlphaLast :
      (SimplexCategory.δ q.castSucc.succ ≫
        alpha).toOrderHom (Fin.last n) =
      alpha.toOrderHom (Fin.last (n + 1)) :=
    congrArg alpha.toOrderHom (quillenABridgeFaceInnerLast n q)
  let pathFace := y.map (homOfLE
    (quillenATargetFiberRhoIndexMap_le (op ⦋n⦌)
      (SimplexCategory.δ q.castSucc.succ ≫ alpha)
      ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) (Fin.last n)))
  let pathTop := y.map (homOfLE
    (quillenATargetFiberRhoIndexMap_le (op ⦋n + 1⦌)
      alpha t (Fin.last (n + 1))))
  have hPath : HEq pathFace pathTop := by
    unfold pathFace pathTop
    cases hBetaLast
    cases hAlphaLast
    exact heq_of_eq (congrArg y.map (Subsingleton.elim _ _))
  have hTheta := quillenABridgeFaceInnerThetaHEq F n q H
    ((nerve D).map alpha.op y) theta
  let thetaTop := pathTop ≫ eqToHom hRightTop.symm ≫ theta
  have hThetaTop := quillenABridgeFaceInnerThetaHEq F n q H
    ((nerve D).map beta.op y) thetaTop
  have hLeft := CategoryTheory.heq_comp
    (congrArg y.obj hBetaLast)
    (quillenABridgeFaceInnerRightObj n q ((nerve D).map alpha.op y))
    (congrArg F.obj (quillenABridgeFaceInnerLeftObj n q H).symm)
    hPath hTheta
  exact hLeft.trans hThetaTop.symm
  -/
  subst G
  let beta := quillenATargetFiberRhoBetaTop alpha t
  let betaFace := quillenATargetFiberRhoBetaFaceInner q alpha t
  let K : Fin (n + 1) ⥤ Fin (n + 2) :=
    (SimplexCategory.δ q.castSucc.succ).toOrderHom.toFunctor
  let iN : Fin (n + 2) := K.obj (Fin.last n)
  let f : beta.toOrderHom iN ⟶ alpha.toOrderHom iN :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t iN)
  let g : alpha.toOrderHom iN ⟶
      alpha.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (alpha.toOrderHom.monotone (Fin.le_last _))
  let h : beta.toOrderHom iN ⟶
      beta.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (beta.toOrderHom.monotone (Fin.le_last _))
  let j : beta.toOrderHom (Fin.last (n + 1)) ⟶
      alpha.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))
  let fFace : betaFace.toOrderHom (Fin.last n) ⟶
      (SimplexCategory.δ q.castSucc.succ ≫
        alpha).toOrderHom (Fin.last n) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) (SimplexCategory.δ q.castSucc.succ ≫ alpha)
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) (Fin.last n))
  have hBeta := quillenATargetFiberRhoIndexMap_delta_inner q alpha t
  have hBetaIndex : betaFace.toOrderHom (Fin.last n) =
      beta.toOrderHom iN := by
    exact congrArg (fun gamma ↦ gamma.toOrderHom (Fin.last n)) hBeta
  have hAlphaIndex :
      (SimplexCategory.δ q.castSucc.succ ≫
        alpha).toOrderHom (Fin.last n) = alpha.toOrderHom iN := by
    rfl
  have hPath : y.map f ≫ y.map g = y.map h ≫ y.map j := by
    rw [← y.map_comp, ← y.map_comp]
    apply congrArg y.map
    apply Subsingleton.elim
  have hRightTop : ((nerve D).map alpha.op y).right =
      y.obj (alpha.toOrderHom (Fin.last (n + 1))) := rfl
  have hRightFace : ((nerve D).δ q.castSucc.succ
      ((nerve D).map alpha.op y)).right =
      y.obj ((SimplexCategory.δ q.castSucc.succ ≫
        alpha).toOrderHom (Fin.last n)) :=
    (congrArg (fun L : ComposableArrows D n ↦ L.right) hGFace).trans rfl
  let leftPrefix :=
    y.map fFace ≫ eqToHom hRightFace.symm ≫
      eqToHom (quillenABridgeFaceInnerRightObj n q
        ((nerve D).map alpha.op y))
  let rightPrefix :=
    eqToHom (quillenABridgeFaceInnerRightObj n q
      ((nerve D).map beta.op y)) ≫
      y.map j ≫ eqToHom hRightTop.symm
  have hLeft : HEq leftPrefix (y.map f ≫ y.map g) := by
    cases hBetaIndex
    cases hAlphaIndex
    have hf : y.map fFace = y.map f :=
      congrArg y.map (Subsingleton.elim _ _)
    have hFaceRfl : hRightFace = rfl := Subsingleton.elim _ _
    let hIdx := quillenABridgeFaceInnerLast n q
    have hAIdx : alpha.toOrderHom iN =
        alpha.toOrderHom (Fin.last (n + 1)) := by
      exact congrArg alpha.toOrderHom hIdx
    have hSuffix :
        eqToHom (quillenABridgeFaceInnerRightObj n q
          ((nerve D).map alpha.op y)) = y.map g := by
      change eqToHom (congrArg y.obj hAIdx) = y.map g
      rw [← eqToHom_map]
      · exact congrArg y.map (Subsingleton.elim _ _)
      · exact hAIdx
    unfold leftPrefix
    rw [hFaceRfl, eqToHom_refl, Category.id_comp, hSuffix, hf]
  have hRight : HEq rightPrefix (y.map h ≫ y.map j) := by
    let hIdx := quillenABridgeFaceInnerLast n q
    have hBIdx : beta.toOrderHom iN =
        beta.toOrderHom (Fin.last (n + 1)) := by
      exact congrArg beta.toOrderHom hIdx
    have hPrefix :
        eqToHom (quillenABridgeFaceInnerRightObj n q
          ((nerve D).map beta.op y)) = y.map h := by
      change eqToHom (congrArg y.obj hBIdx) = y.map h
      rw [← eqToHom_map]
      · exact congrArg y.map (Subsingleton.elim _ _)
      · exact hBIdx
    have hBetaFaceRight :
        ((nerve D).δ q.castSucc.succ
          ((nerve D).map beta.op y)).right =
            y.obj (beta.toOrderHom iN) := rfl
    have hBetaObjLast : ((nerve D).map beta.op y).right =
        y.obj (beta.toOrderHom (Fin.last (n + 1))) := rfl
    have hPrefixHEq : HEq
        (eqToHom (quillenABridgeFaceInnerRightObj n q
          ((nerve D).map beta.op y))) (y.map h) := heq_of_eq hPrefix
    have hSuffix : HEq (y.map j ≫ eqToHom hRightTop.symm)
        (y.map j) := CategoryTheory.comp_eqToHom_heq (y.map j) hRightTop.symm
    have hc := CategoryTheory.heq_comp
      hBetaFaceRight hBetaObjLast hRightTop hPrefixHEq hSuffix
    simpa only [Category.assoc] using hc
  have hBetaFaceRight :
      ((nerve D).δ q.castSucc.succ
        ((nerve D).map beta.op y)).right =
          y.obj (beta.toOrderHom iN) := rfl
  have hLeftTheta : HEq (leftPrefix ≫ theta)
      ((y.map f ≫ y.map g) ≫ theta) := by
    exact CategoryTheory.heq_comp
      (congrArg y.obj hBetaIndex) hRightTop rfl hLeft HEq.rfl
  have hRightTheta : HEq (rightPrefix ≫ theta)
      ((y.map h ≫ y.map j) ≫ theta) := by
    exact CategoryTheory.heq_comp
      hBetaFaceRight hRightTop rfl hRight HEq.rfl
  have hPathTheta : (y.map f ≫ y.map g) ≫ theta =
      (y.map h ≫ y.map j) ≫ theta :=
    congrArg (fun z ↦ z ≫ theta) hPath
  have hPrefixTheta := hLeftTheta.trans
    ((heq_of_eq hPathTheta).trans hRightTheta.symm)
  have hSource :
      y.obj (betaFace.toOrderHom (Fin.last n)) =
        ((nerve D).δ q.castSucc.succ
          ((nerve D).map beta.op y)).right :=
    (congrArg y.obj hBetaIndex).trans hBetaFaceRight.symm
  have hFinal := CategoryTheory.heq_comp hSource rfl rfl
    hPrefixTheta (HEq.rfl : HEq
      (F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H)))
      (F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q H))))
  simpa only [leftPrefix, rightPrefix, Category.assoc] using hFinal


set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C (n + 1))
    (G : ComposableArrows D (n + 1))
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : G = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ (Fin.last (n + 1)) G =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    have hRightTop : G.right =
        y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
      (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
    have hRightFace : ((nerve D).δ (Fin.last (n + 1)) G).right =
        y.obj ((SimplexCategory.δ (Fin.last (n + 1)) ≫
          alpha).toOrderHom (Fin.last n)) :=
      (congrArg (fun K : ComposableArrows D n ↦ K.right) hGFace).trans rfl
    HEq
      (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n⦌) (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
            ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
              (Fin.last n))) ≫
        eqToHom hRightFace.symm ≫
          (eqToHom (quillenABridgeFaceLastRight n G) ≫
            G.map' n (n + 1) ≫ theta))
      (eqToHom (quillenABridgeFaceLastRight n
          ((nerve D).map
            (quillenATargetFiberRhoBetaTop alpha t).op y)) ≫
        ((nerve D).map
          (quillenATargetFiberRhoBetaTop alpha t).op y).map' n (n + 1) ≫
        (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
            eqToHom hRightTop.symm ≫ theta)) := by
  subst G
  let beta := quillenATargetFiberRhoBetaTop alpha t
  let betaFace := quillenATargetFiberRhoBetaFaceLast alpha t
  let iN : Fin (n + 2) :=
    (SimplexCategory.δ
      (Fin.last (n + 1))).toOrderHom.toFunctor.obj (Fin.last n)
  let f : beta.toOrderHom iN ⟶ alpha.toOrderHom iN :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t iN)
  let g : alpha.toOrderHom iN ⟶ alpha.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (alpha.toOrderHom.monotone (Fin.le_last _))
  let h : beta.toOrderHom iN ⟶ beta.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (beta.toOrderHom.monotone (Fin.le_last _))
  let j : beta.toOrderHom (Fin.last (n + 1)) ⟶
      alpha.toOrderHom (Fin.last (n + 1)) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))
  let fFace : betaFace.toOrderHom (Fin.last n) ⟶
      (SimplexCategory.δ (Fin.last (n + 1)) ≫
        alpha).toOrderHom (Fin.last n) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
          (Fin.last n))
  have hBeta := quillenATargetFiberRhoIndexMap_delta_last alpha t
  have hBetaIndex : betaFace.toOrderHom (Fin.last n) =
      beta.toOrderHom iN := by
    exact congrArg (fun gamma ↦ gamma.toOrderHom (Fin.last n)) hBeta
  have hAlphaIndex :
      (SimplexCategory.δ (Fin.last (n + 1)) ≫
        alpha).toOrderHom (Fin.last n) = alpha.toOrderHom iN := by
    rfl
  have hPath : y.map f ≫ y.map g = y.map h ≫ y.map j := by
    rw [← y.map_comp, ← y.map_comp]
    apply congrArg y.map
    apply Subsingleton.elim
  have hRightTop : ((nerve D).map alpha.op y).right =
      y.obj (alpha.toOrderHom (Fin.last (n + 1))) := rfl
  have hRightFace : ((nerve D).δ (Fin.last (n + 1))
      ((nerve D).map alpha.op y)).right =
      y.obj ((SimplexCategory.δ (Fin.last (n + 1)) ≫
        alpha).toOrderHom (Fin.last n)) :=
    (congrArg (fun K : ComposableArrows D n ↦ K.right) hGFace).trans rfl
  let leftPrefix :=
    y.map fFace ≫ eqToHom hRightFace.symm ≫
      eqToHom (quillenABridgeFaceLastRight n
        ((nerve D).map alpha.op y)) ≫
      ((nerve D).map alpha.op y).map' n (n + 1)
  let rightPrefix :=
    eqToHom (quillenABridgeFaceLastRight n
      ((nerve D).map beta.op y)) ≫
      ((nerve D).map beta.op y).map' n (n + 1) ≫
      y.map j ≫ eqToHom hRightTop.symm
  have hLeft : HEq leftPrefix (y.map f ≫ y.map g) := by
    cases hBetaIndex
    cases hAlphaIndex
    have hf : y.map fFace = y.map f :=
      congrArg y.map (Subsingleton.elim _ _)
    have hFaceRfl : hRightFace = rfl := Subsingleton.elim _ _
    let hIdx := quillenABridgeFaceLastIndex n (Fin.last n)
    have hAIdx : alpha.toOrderHom iN =
        alpha.toOrderHom (Fin.last n).castSucc := by
      exact congrArg alpha.toOrderHom hIdx
    have hSuffix :
        eqToHom (quillenABridgeFaceLastRight n
            ((nerve D).map alpha.op y)) ≫
          ((nerve D).map alpha.op y).map' n (n + 1) =
        y.map g := by
      change eqToHom (congrArg y.obj hAIdx) ≫ y.map _ = y.map g
      rw [← eqToHom_map]
      · rw [← y.map_comp]
        exact congrArg y.map (Subsingleton.elim _ _)
      · exact hAIdx
    unfold leftPrefix
    rw [hFaceRfl, eqToHom_refl, Category.id_comp, hSuffix, hf]
  have hRight : HEq rightPrefix (y.map h ≫ y.map j) := by
    let hIdx := quillenABridgeFaceLastIndex n (Fin.last n)
    have hBIdx : beta.toOrderHom iN =
        beta.toOrderHom (Fin.last n).castSucc := by
      exact congrArg beta.toOrderHom hIdx
    have hPrefix :
        eqToHom (quillenABridgeFaceLastRight n
            ((nerve D).map beta.op y)) ≫
          ((nerve D).map beta.op y).map' n (n + 1) =
        y.map h := by
      change eqToHom (congrArg y.obj hBIdx) ≫ y.map _ = y.map h
      rw [← eqToHom_map]
      · rw [← y.map_comp]
        exact congrArg y.map (Subsingleton.elim _ _)
      · exact hBIdx
    unfold rightPrefix
    have hBetaObjN : ((nerve D).map beta.op y).obj (Fin.last n).castSucc =
        y.obj (beta.toOrderHom iN) := by
      exact congrArg (fun z ↦ y.obj (beta.toOrderHom z))
        (quillenABridgeFaceLastIndex n (Fin.last n)).symm
    have hBetaObjLast : ((nerve D).map beta.op y).right =
        y.obj (beta.toOrderHom (Fin.last (n + 1))) := rfl
    have hPrefixHEq : HEq
        (eqToHom (quillenABridgeFaceLastRight n
          ((nerve D).map beta.op y)) ≫
          ((nerve D).map beta.op y).map' n (n + 1))
        (y.map h) := heq_of_eq hPrefix
    have hSuffix : HEq (y.map j ≫ eqToHom hRightTop.symm)
        (y.map j) := CategoryTheory.comp_eqToHom_heq (y.map j) hRightTop.symm
    have hc := CategoryTheory.heq_comp
      ((quillenABridgeFaceLastRight n
        ((nerve D).map beta.op y)).trans hBetaObjN)
      hBetaObjLast hRightTop hPrefixHEq hSuffix
    simpa only [Category.assoc] using hc
  have hLeftTheta : HEq (leftPrefix ≫ theta)
      ((y.map f ≫ y.map g) ≫ theta) := by
    exact CategoryTheory.heq_comp
      (congrArg y.obj hBetaIndex) hRightTop rfl hLeft HEq.rfl
  have hRightTheta : HEq (rightPrefix ≫ theta)
      ((y.map h ≫ y.map j) ≫ theta) := by
    have hBetaObjN : ((nerve D).map beta.op y).obj (Fin.last n).castSucc =
        y.obj (beta.toOrderHom iN) := by
      exact congrArg (fun z ↦ y.obj (beta.toOrderHom z))
        (quillenABridgeFaceLastIndex n (Fin.last n)).symm
    exact CategoryTheory.heq_comp
      ((quillenABridgeFaceLastRight n
        ((nerve D).map beta.op y)).trans hBetaObjN)
      hRightTop rfl hRight HEq.rfl
  have hPathTheta : (y.map f ≫ y.map g) ≫ theta =
      (y.map h ≫ y.map j) ≫ theta := congrArg (fun q ↦ q ≫ theta) hPath
  have hFinal := hLeftTheta.trans
    ((heq_of_eq hPathTheta).trans hRightTheta.symm)
  simpa only [leftPrefix, rightPrefix, Category.assoc] using hFinal

private noncomputable def quillenATargetFiberRhoCarrierFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) := by
  let H := r.1.1
  let G := CategoryBar.barChain r.2
  let theta := CategoryBar.barCoeffR r.2
  let beta := quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t
  let Gt : ComposableArrows D n := (nerve D).map beta.op y
  have hRight : G.right =
      y.obj (alpha.toOrderHom (Fin.last n)) :=
    (congrArg (fun K : ComposableArrows D n ↦ K.right) hG).trans rfl
  let thetaT : Gt.right ⟶ F.obj H.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) alpha t (Fin.last n))) ≫
        eqToHom hRight.symm ≫ theta
  exact quillenAMappingCarrierIncl F n H Gt thetaT

private theorem quillenATargetFiberRhoCarrierFromRaw_target
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (quillenATarget F).app (op ⦋n⦌)
        (quillenATargetFiberRhoCarrierFromRaw F y n alpha r hG t) =
      (nerve D).map
        (quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t).op y := by
  let beta := quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t
  let Gt : ComposableArrows D n := (nerve D).map beta.op y
  have hRight : (CategoryBar.barChain r.2).right =
      y.obj (alpha.toOrderHom (Fin.last n)) :=
    (congrArg (fun K : ComposableArrows D n ↦ K.right) hG).trans rfl
  let thetaT : Gt.right ⟶ F.obj r.1.1.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) alpha t (Fin.last n))) ≫
        eqToHom hRight.symm ≫ CategoryBar.barCoeffR r.2
  change (quillenATarget F).app (op ⦋n⦌)
      (quillenAMappingCarrierIncl F n r.1.1 Gt thetaT) = Gt
  rw [quillenATarget_carrierIncl]

private theorem quillenATargetFiberRhoDecoded_hG
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y}) :
    CategoryBar.barChain
        (quillenAMappingCarrierRawEquiv F n d.1.1).2 =
      (nerve D).map d.1.2.op y :=
  (quillenATarget_eq_raw_chain F n d.1.1).symm.trans d.2

private noncomputable def quillenATargetFiberRhoFromRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (r : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y} :=
  ⟨⟨quillenATargetFiberRhoCarrierFromRaw
      F y n alpha r hG t,
    quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t⟩,
    quillenATargetFiberRhoCarrierFromRaw_target F y n alpha r hG t⟩

private theorem quillenATargetFiberRhoFromRaw_congr
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    {alpha alpha' : SimplexCategory.mk n ⟶ SimplexCategory.mk m}
    {r r' : Σ p : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)}
    (ha : alpha = alpha') (hr : r = r')
    (hG : CategoryBar.barChain r.2 = (nerve D).map alpha.op y)
    (hG' : CategoryBar.barChain r'.2 = (nerve D).map alpha'.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoFromRaw F y n alpha r hG t =
      quillenATargetFiberRhoFromRaw F y n alpha' r' hG' t := by
  cases ha
  cases hr
  rfl

private noncomputable def quillenATargetFiberRhoDecoded
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y} := by
  let r := quillenAMappingCarrierRawEquiv F n d.1.1
  exact quillenATargetFiberRhoFromRaw F y n d.1.2 r
    (quillenATargetFiberRhoDecoded_hG F y n d) t

private noncomputable def quillenATargetFiberRhoAppRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌) :=
  (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).symm
      (quillenATargetFiberRhoDecoded F y n
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n⦌) zt.1) zt.2)

private theorem quillenATargetFiberRhoAppRaw_objEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
        (quillenATargetFiberRhoAppRaw F y n zt) =
      quillenATargetFiberRhoDecoded F y n
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n⦌) zt.1) zt.2 := by
  change (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
      ((SSet.leftFiber.objEquiv
        (quillenATarget F) y (op ⦋n⦌)).symm
          (quillenATargetFiberRhoDecoded F y n
            (SSet.leftFiber.objEquiv
              (quillenATarget F) y (op ⦋n⦌) zt.1) zt.2)) = _
  exact Equiv.apply_symm_apply _ _

private def quillenATargetFiberRhoFaceZeroRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    Σ q : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
  ⟨quillenAMappingIndex n ((nerve C).δ 0 p.1),
    quillenAMappingCarrierInner F n ((nerve C).δ 0 p.1)
      ((nerve D).δ 0 (CategoryBar.barChain x))
      (CategoryBar.barCoeffR x ≫ F.map (p.1.map' 0 1))⟩

private noncomputable def quillenATargetFiberRhoCarrierTop
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) :=
  quillenATargetFiberRhoCarrierFromRaw F y n alpha ⟨p, x⟩ hG t

private noncomputable def quillenATargetFiberRhoCarrierFaceZero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hGFace : (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) :=
  quillenATargetFiberRhoCarrierFromRaw F y n
    (SimplexCategory.δ 0 ≫ alpha)
      (quillenATargetFiberRhoFaceZeroRaw F n p x) hGFace
      ((Δ[1] : SSet.{max u v}).δ 0 t)

private noncomputable def quillenATargetFiberRhoOutputFaceZeroRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    Σ q : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) := by
  let betaTop := quillenATargetFiberRhoIndexMap
    (op ⦋n + 1⦌) alpha t
  let GtTop : ComposableArrows D (n + 1) :=
    (nerve D).map betaTop.op y
  have hRightTop : (CategoryBar.barChain x).right =
      y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
    (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
  let thetaTTop : GtTop.right ⟶ F.obj p.1.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
        eqToHom hRightTop.symm ≫ CategoryBar.barCoeffR x
  exact ⟨quillenAMappingIndex n ((nerve C).δ 0 p.1),
    quillenAMappingCarrierInner F n ((nerve C).δ 0 p.1)
      ((nerve D).δ 0 GtTop) (thetaTTop ≫ F.map (p.1.map' 0 1))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTopRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ 0
          (quillenATargetFiberRhoCarrierTop
            F y (n + 1) p x alpha hG t)) =
      quillenATargetFiberRhoOutputFaceZeroRaw
        F y n p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierTop
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoOutputFaceZeroRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_δ_zero]
  rw [quillenAMappingCarrierFaceZeroInner_eq_canonical]
  refine Sigma.ext ?_ ?_
  · refine Sigma.ext
      (quillenAMappingCarrierFaceZeroIndex_chain n
        (quillenAMappingIndex (n + 1) p.1)) ?_
    change HEq (_ : PUnit) (_ : PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFaceRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        (quillenATargetFiberRhoCarrierFaceZero
          F y n p x alpha hGFace t) =
      quillenATargetFiberRhoOutputFaceZeroRaw
        F y n p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierFaceZero
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoFaceZeroRaw
    quillenATargetFiberRhoOutputFaceZeroRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_incl]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext ?_ ?_
  · exact quillenATargetFiberRhoChain_delta_zero y alpha t
  · apply quillenAProd_heq
    · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    · exact quillenATargetFiberRhoTheta_delta_zero
        F y n p.1 (CategoryBar.barChain x) (CategoryBar.barCoeffR x)
          alpha hG hGFace t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoCarrier_delta_zero_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoCarrierFaceZero
        F y n p x alpha hGFace t =
      (quillenAMappingCarrier F).δ 0
        (quillenATargetFiberRhoCarrierTop
          F y (n + 1) p x alpha hG t) := by
  apply (quillenAMappingCarrierRawEquiv F n).injective
  exact (quillenATargetFiberRhoFaceRaw_delta_zero
    F y n p x alpha hG hGFace t).trans
      (quillenATargetFiberRhoTopRaw_delta_zero
        F y n p x alpha hG t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFromRaw_delta_zero_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (0 : Fin (n + 2)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoFromRaw F y n
        (SimplexCategory.δ 0 ≫ alpha)
          (quillenATargetFiberRhoFaceZeroRaw F n p x) hGFace
          ((Δ[1] : SSet.{max u v}).δ 0 t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ (0 : Fin (n + 2))).op
          (quillenATargetFiberRhoFromRaw F y (n + 1)
            alpha ⟨p, x⟩ hG t) := by
  unfold quillenATargetFiberRhoFromRaw
    quillenATargetFiberDecodedMap
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · exact quillenATargetFiberRhoCarrier_delta_zero_canonical
      F y n p x alpha hG hGFace t
  · exact quillenATargetFiberRhoIndexMap_delta_zero alpha t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoDecoded_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n + 1⦌) p.1 =
        (nerve D).map p.2.op y})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoDecoded F y n
        (quillenATargetFiberDecodedMap F y
          (SimplexCategory.δ (0 : Fin (n + 2))).op d)
        ((Δ[1] : SSet.{max u v}).δ 0 t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ (0 : Fin (n + 2))).op
          (quillenATargetFiberRhoDecoded F y (n + 1) d t) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  let e := quillenATargetFiberDecodedMap F y k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hGTop : CategoryBar.barChain rTop.2 =
      (nerve D).map d.1.2.op y :=
    (quillenATarget_eq_raw_chain F (n + 1) d.1.1).symm.trans d.2
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hGFace : CategoryBar.barChain rFace.2 =
      (nerve D).map alphaFace.op y :=
    (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
  let p := rTop.1
  let x := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_zero_of F n p x
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
  let rExpected : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit C) n p,
      quillenAMappingCarrierFaceZeroInnerOf F n p x⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenATargetFiberDecodedMap
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hRawE]
    exact hGFace
  let rCanonical : Σ q : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj q.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n ((nerve C).δ 0 p.1),
      quillenAMappingCarrierInner F n ((nerve C).δ 0 p.1)
        ((nerve D).δ 0 (CategoryBar.barChain x))
        (CategoryBar.barCoeffR x ≫ F.map (p.1.map' 0 1))⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      unfold rExpected rCanonical quillenAMappingIndex
      refine Sigma.ext rfl ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceZeroInnerOf_eq_canonical F n p x)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hCanonical]
    exact hGExpected
  let alphaCanonical :=
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ d.1.2
  have hk : k.unop = SimplexCategory.δ (0 : Fin (n + 2)) := by
    rfl
  have hAlpha : alphaFace = alphaCanonical := by
    unfold alphaFace e quillenATargetFiberDecodedMap alphaCanonical
    dsimp only [k]
    rw [hk]
  have hGCanonicalExplicit : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaCanonical.op y := by
    rw [← hAlpha]
    exact hGCanonical
  have hReplace := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hRawE hGFace hGExpected
      ((Δ[1] : SSet.{max u v}).δ 0 t)
  have hReplaceCanonical := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hCanonical
      hGExpected hGCanonical ((Δ[1] : SSet.{max u v}).δ 0 t)
  have hReplaceAlpha := quillenATargetFiberRhoFromRaw_congr
    F y n hAlpha (rfl : rCanonical = rCanonical)
      hGCanonical hGCanonicalExplicit
        ((Δ[1] : SSet.{max u v}).δ 0 t)
  have hGDelta : (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y := by
    have h := hGCanonicalExplicit
    change (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y at h
    exact h
  let rFaceAlias := quillenATargetFiberRhoFaceZeroRaw F n p x
  have hFaceAlias : rCanonical = rFaceAlias := by
    rfl
  have hGFaceAlias : CategoryBar.barChain rFaceAlias.2 =
      (nerve D).map alphaCanonical.op y := by
    change (nerve D).δ 0 (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y
    exact hGDelta
  have hReplaceAlias := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaCanonical = alphaCanonical) hFaceAlias
      hGCanonicalExplicit hGFaceAlias
        ((Δ[1] : SSet.{max u v}).δ 0 t)
  unfold quillenATargetFiberRhoDecoded
  change quillenATargetFiberRhoFromRaw F y n
      alphaFace rFace hGFace ((Δ[1] : SSet.{max u v}).δ 0 t) =
    quillenATargetFiberDecodedMap F y k
      (quillenATargetFiberRhoFromRaw F y (n + 1)
        d.1.2 rTop hGTop t)
  calc
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rExpected hGExpected
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplace
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rCanonical hGCanonical
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplaceCanonical
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rCanonical hGCanonicalExplicit
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplaceAlpha
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rFaceAlias hGFaceAlias
          ((Δ[1] : SSet.{max u v}).δ 0 t) := hReplaceAlias
    _ = _ := by
      simpa only [alphaCanonical, rFaceAlias, rTop, p, x, k] using
        quillenATargetFiberRhoFromRaw_delta_zero_canonical
          F y n p x d.1.2 hGTop hGDelta t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_delta_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y ⊗
          (Δ[1] : SSet.{max u v})).δ 0 zt) =
      (SSet.leftFiber (quillenATarget F) y).δ 0
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt) := by
  let k := (SimplexCategory.δ (0 : Fin (n + 2))).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  change quillenATargetFiberRhoDecoded F y n
      (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
        ((SSet.leftFiber (quillenATarget F) y).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change quillenATargetFiberRhoDecoded F y n
      (quillenATargetFiberDecodedMap F y k
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
      ((SSet.leftFiber (quillenATarget F) y).map k
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  exact quillenATargetFiberRhoDecoded_delta_zero F y n
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌) zt.1) zt.2

private def quillenATargetFiberRhoFaceInnerRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
  ⟨quillenAMappingIndex n ((nerve C).δ q.castSucc.succ p.1),
    quillenAMappingCarrierInner F n
      ((nerve C).δ q.castSucc.succ p.1)
      ((nerve D).δ q.castSucc.succ (CategoryBar.barChain x))
      (eqToHom (quillenABridgeFaceInnerRightObj n q
          (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
        F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q p.1)))⟩

private noncomputable def quillenATargetFiberRhoCarrierFaceInner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hGFace : (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) :=
  quillenATargetFiberRhoCarrierFromRaw F y n
    (SimplexCategory.δ q.castSucc.succ ≫ alpha)
      (quillenATargetFiberRhoFaceInnerRaw F n q p x) hGFace
      ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)

private noncomputable def quillenATargetFiberRhoOutputFaceInnerRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) := by
  let betaTop := quillenATargetFiberRhoBetaTop alpha t
  let GtTop : ComposableArrows D (n + 1) := (nerve D).map betaTop.op y
  have hRightTop : (CategoryBar.barChain x).right =
      y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
    (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
  let thetaTTop : GtTop.right ⟶ F.obj p.1.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
        eqToHom hRightTop.symm ≫ CategoryBar.barCoeffR x
  exact ⟨quillenAMappingIndex n ((nerve C).δ q.castSucc.succ p.1),
    quillenAMappingCarrierInner F n
      ((nerve C).δ q.castSucc.succ p.1)
      ((nerve D).δ q.castSucc.succ GtTop)
      (eqToHom (quillenABridgeFaceInnerRightObj n q GtTop) ≫
        thetaTTop ≫
        F.map (eqToHom (quillenABridgeFaceInnerLeftObj n q p.1)))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTopRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ q.castSucc.succ
          (quillenATargetFiberRhoCarrierTop
            F y (n + 1) p x alpha hG t)) =
      quillenATargetFiberRhoOutputFaceInnerRaw
        F y n q p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierTop
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoOutputFaceInnerRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_δ_inner]
  rw [quillenAMappingCarrierFaceInnerInner_eq_canonical]
  refine Sigma.ext ?_ ?_
  · refine Sigma.ext
      (quillenAMappingCarrierFaceInnerIndex_chain n q
        (quillenAMappingIndex (n + 1) p.1)) ?_
    change HEq (_ : PUnit) (_ : PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFaceRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        (quillenATargetFiberRhoCarrierFaceInner
          F y n q p x alpha hGFace t) =
      quillenATargetFiberRhoOutputFaceInnerRaw
        F y n q p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierFaceInner
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoFaceInnerRaw
    quillenATargetFiberRhoOutputFaceInnerRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_incl]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext ?_ ?_
  · exact quillenATargetFiberRhoChain_delta_inner y q alpha t
  · apply quillenAProd_heq
    · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    · exact quillenATargetFiberRhoTheta_delta_inner
        F y n q p.1 (CategoryBar.barChain x) (CategoryBar.barCoeffR x)
          alpha hG hGFace t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoCarrier_delta_inner_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoCarrierFaceInner
        F y n q p x alpha hGFace t =
      (quillenAMappingCarrier F).δ q.castSucc.succ
        (quillenATargetFiberRhoCarrierTop
          F y (n + 1) p x alpha hG t) := by
  apply (quillenAMappingCarrierRawEquiv F n).injective
  exact (quillenATargetFiberRhoFaceRaw_delta_inner
    F y n q p x alpha hG hGFace t).trans
      (quillenATargetFiberRhoTopRaw_delta_inner
        F y n q p x alpha hG t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFromRaw_delta_inner_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ q.castSucc.succ ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoFromRaw F y n
        (SimplexCategory.δ q.castSucc.succ ≫ alpha)
          (quillenATargetFiberRhoFaceInnerRaw F n q p x) hGFace
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ q.castSucc.succ).op
          (quillenATargetFiberRhoFromRaw F y (n + 1)
            alpha ⟨p, x⟩ hG t) := by
  unfold quillenATargetFiberRhoFromRaw
    quillenATargetFiberDecodedMap
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · exact quillenATargetFiberRhoCarrier_delta_inner_canonical
      F y n q p x alpha hG hGFace t
  · exact quillenATargetFiberRhoIndexMap_delta_inner q alpha t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoDecoded_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n + 1⦌) p.1 =
        (nerve D).map p.2.op y})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoDecoded F y n
        (quillenATargetFiberDecodedMap F y
          (SimplexCategory.δ q.castSucc.succ).op d)
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ q.castSucc.succ).op
          (quillenATargetFiberRhoDecoded F y (n + 1) d t) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  let e := quillenATargetFiberDecodedMap F y k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hGTop : CategoryBar.barChain rTop.2 =
      (nerve D).map d.1.2.op y :=
    (quillenATarget_eq_raw_chain F (n + 1) d.1.1).symm.trans d.2
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hGFace : CategoryBar.barChain rFace.2 =
      (nerve D).map alphaFace.op y :=
    (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
  let p := rTop.1
  let x := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_inner_of F n q p x
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
  let rExpected : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit C) n q.castSucc.succ
          (quillenACastSucc_succ_ne_last q) p,
      quillenAMappingCarrierFaceInnerInnerOf F n q p x⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenATargetFiberDecodedMap
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hRawE]
    exact hGFace
  let rCanonical : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n ((nerve C).δ q.castSucc.succ p.1),
      quillenAMappingCarrierInner F n
        ((nerve C).δ q.castSucc.succ p.1)
        ((nerve D).δ q.castSucc.succ (CategoryBar.barChain x))
        (eqToHom (quillenABridgeFaceInnerRightObj n q
            (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
          F.map (eqToHom
            (quillenABridgeFaceInnerLeftObj n q p.1)))⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      unfold rExpected rCanonical quillenAMappingIndex
      refine Sigma.ext
        (quillenAMappingCarrierFaceInnerIndex_chain n q p) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceInnerInnerOf_eq_canonical F n q p x)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hCanonical]
    exact hGExpected
  let alphaCanonical := SimplexCategory.δ q.castSucc.succ ≫ d.1.2
  have hk : k.unop = SimplexCategory.δ q.castSucc.succ := by
    rfl
  have hAlpha : alphaFace = alphaCanonical := by
    unfold alphaFace e quillenATargetFiberDecodedMap alphaCanonical
    dsimp only [k]
    rw [hk]
  have hGCanonicalExplicit : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaCanonical.op y := by
    rw [← hAlpha]
    exact hGCanonical
  have hReplace := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hRawE hGFace hGExpected
      ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  have hReplaceCanonical := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hCanonical
      hGExpected hGCanonical
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  have hReplaceAlpha := quillenATargetFiberRhoFromRaw_congr
    F y n hAlpha (rfl : rCanonical = rCanonical)
      hGCanonical hGCanonicalExplicit
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  have hGDelta :
      (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
        (nerve D).map alphaCanonical.op y := by
    have h := hGCanonicalExplicit
    change (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y at h
    exact h
  let rFaceAlias := quillenATargetFiberRhoFaceInnerRaw F n q p x
  have hFaceAlias : rCanonical = rFaceAlias := by
    rfl
  have hGFaceAlias : CategoryBar.barChain rFaceAlias.2 =
      (nerve D).map alphaCanonical.op y := by
    change (nerve D).δ q.castSucc.succ (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y
    exact hGDelta
  have hReplaceAlias := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaCanonical = alphaCanonical) hFaceAlias
      hGCanonicalExplicit hGFaceAlias
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t)
  unfold quillenATargetFiberRhoDecoded
  change quillenATargetFiberRhoFromRaw F y n
      alphaFace rFace hGFace
        ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) =
    quillenATargetFiberDecodedMap F y k
      (quillenATargetFiberRhoFromRaw F y (n + 1)
        d.1.2 rTop hGTop t)
  calc
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rExpected hGExpected
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := hReplace
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rCanonical hGCanonical
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) :=
      hReplaceCanonical
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rCanonical hGCanonicalExplicit
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := hReplaceAlpha
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rFaceAlias hGFaceAlias
          ((Δ[1] : SSet.{max u v}).δ q.castSucc.succ t) := hReplaceAlias
    _ = _ := by
      simpa only [alphaCanonical, rFaceAlias, rTop, p, x, k] using
        quillenATargetFiberRhoFromRaw_delta_inner_canonical
          F y n q p x d.1.2 hGTop hGDelta t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_delta_inner
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (q : Fin n)
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y ⊗
          (Δ[1] : SSet.{max u v})).δ q.castSucc.succ zt) =
      (SSet.leftFiber (quillenATarget F) y).δ q.castSucc.succ
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt) := by
  let k := (SimplexCategory.δ q.castSucc.succ).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  change quillenATargetFiberRhoDecoded F y n
      (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
        ((SSet.leftFiber (quillenATarget F) y).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change quillenATargetFiberRhoDecoded F y n
      (quillenATargetFiberDecodedMap F y k
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
      ((SSet.leftFiber (quillenATarget F) y).map k
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  exact quillenATargetFiberRhoDecoded_delta_inner F y n q
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌) zt.1) zt.2

set_option backward.isDefEq.respectTransparency false in
private theorem quillenAMappingCarrierDegInnerOf_eq_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    quillenAMappingCarrierDegInnerOf F n i p x =
      quillenAMappingCarrierInner F (n + 1)
        ((nerve C).σ i p.1) ((nerve D).σ i (CategoryBar.barChain x))
        (eqToHom (quillenABridgeDegInnerRightObj n i
            (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i p.1))) := by
  rcases p with ⟨H, r⟩
  change PUnit at r
  obtain rfl : r = PUnit.unit := Subsingleton.elim _ _
  change CategoryBar.barObj D
    (CategoryBar.commaCoeffR (𝟭 D) (F.obj H.left))
    (CategoryBar.unitCoeffL D) n at x
  rcases x with ⟨G, l, theta⟩
  change ULift PUnit at l
  obtain rfl : l = ULift.up PUnit.unit := Subsingleton.elim _ _
  exact quillenAMappingCarrierDegInner_eq_canonical F n i H G theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (H : ComposableArrows C n)
    (G : ComposableArrows D n)
    (theta : G.right ⟶ F.obj H.left)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : G = (nerve D).map alpha.op y)
    (hGDeg : (nerve D).σ i G =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    have hRightTop : G.right =
        y.obj (alpha.toOrderHom (Fin.last n)) :=
      (congrArg (fun K : ComposableArrows D n ↦ K.right) hG).trans rfl
    have hRightDeg : ((nerve D).σ i G).right =
        y.obj ((SimplexCategory.σ i ≫
          alpha).toOrderHom (Fin.last (n + 1))) :=
      (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hGDeg).trans rfl
    HEq
      (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n + 1⦌) (SimplexCategory.σ i ≫ alpha)
            ((Δ[1] : SSet.{max u v}).σ i t)
              (Fin.last (n + 1)))) ≫
        eqToHom hRightDeg.symm ≫
          (eqToHom (quillenABridgeDegInnerRightObj n i G) ≫ theta ≫
            F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))))
      (eqToHom (quillenABridgeDegInnerRightObj n i
          ((nerve D).map
            (quillenATargetFiberRhoIndexMap
              (op ⦋n⦌) alpha t).op y)) ≫
        (y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
          (op ⦋n⦌) alpha t (Fin.last n))) ≫
            eqToHom hRightTop.symm ≫ theta) ≫
        F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))) := by
  subst G
  let beta := quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t
  let betaDeg := quillenATargetFiberRhoBetaDeg i alpha t
  let K : Fin (n + 2) ⥤ Fin (n + 1) :=
    (SimplexCategory.σ i).toOrderHom.toFunctor
  let iN : Fin (n + 1) := K.obj (Fin.last (n + 1))
  let f : beta.toOrderHom iN ⟶ alpha.toOrderHom iN :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) alpha t iN)
  let g : alpha.toOrderHom iN ⟶ alpha.toOrderHom (Fin.last n) :=
    homOfLE (alpha.toOrderHom.monotone (Fin.le_last _))
  let h : beta.toOrderHom iN ⟶ beta.toOrderHom (Fin.last n) :=
    homOfLE (beta.toOrderHom.monotone (Fin.le_last _))
  let j : beta.toOrderHom (Fin.last n) ⟶ alpha.toOrderHom (Fin.last n) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) alpha t (Fin.last n))
  let fDeg : betaDeg.toOrderHom (Fin.last (n + 1)) ⟶
      (SimplexCategory.σ i ≫ alpha).toOrderHom (Fin.last (n + 1)) :=
    homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) (SimplexCategory.σ i ≫ alpha)
        ((Δ[1] : SSet.{max u v}).σ i t) (Fin.last (n + 1)))
  have hBeta := quillenATargetFiberRhoIndexMap_sigma i alpha t
  have hBetaIndex : betaDeg.toOrderHom (Fin.last (n + 1)) =
      beta.toOrderHom iN := by
    exact congrArg (fun gamma ↦ gamma.toOrderHom (Fin.last (n + 1))) hBeta
  have hAlphaIndex :
      (SimplexCategory.σ i ≫ alpha).toOrderHom (Fin.last (n + 1)) =
        alpha.toOrderHom iN := by
    rfl
  have hPath : y.map f ≫ y.map g = y.map h ≫ y.map j := by
    rw [← y.map_comp, ← y.map_comp]
    apply congrArg y.map
    apply Subsingleton.elim
  have hRightTop : ((nerve D).map alpha.op y).right =
      y.obj (alpha.toOrderHom (Fin.last n)) := rfl
  have hRightDeg : ((nerve D).σ i ((nerve D).map alpha.op y)).right =
      y.obj ((SimplexCategory.σ i ≫
        alpha).toOrderHom (Fin.last (n + 1))) :=
    (congrArg (fun L : ComposableArrows D (n + 1) ↦ L.right) hGDeg).trans rfl
  let leftPrefix :=
    y.map fDeg ≫ eqToHom hRightDeg.symm ≫
      eqToHom (quillenABridgeDegInnerRightObj n i
        ((nerve D).map alpha.op y))
  let rightPrefix :=
    eqToHom (quillenABridgeDegInnerRightObj n i
      ((nerve D).map beta.op y)) ≫
      y.map j ≫ eqToHom hRightTop.symm
  have hLeft : HEq leftPrefix (y.map f ≫ y.map g) := by
    cases hBetaIndex
    cases hAlphaIndex
    have hf : y.map fDeg = y.map f :=
      congrArg y.map (Subsingleton.elim _ _)
    have hDegRfl : hRightDeg = rfl := Subsingleton.elim _ _
    let hIdx := quillenABridgeDegInnerLast n i
    have hAIdx : alpha.toOrderHom iN = alpha.toOrderHom (Fin.last n) := by
      exact congrArg alpha.toOrderHom hIdx
    have hSuffix :
        eqToHom (quillenABridgeDegInnerRightObj n i
          ((nerve D).map alpha.op y)) = y.map g := by
      change eqToHom (congrArg y.obj hAIdx) = y.map g
      rw [← eqToHom_map]
      · exact congrArg y.map (Subsingleton.elim _ _)
      · exact hAIdx
    unfold leftPrefix
    rw [hDegRfl, eqToHom_refl, Category.id_comp, hSuffix, hf]
  have hRight : HEq rightPrefix (y.map h ≫ y.map j) := by
    let hIdx := quillenABridgeDegInnerLast n i
    have hBIdx : beta.toOrderHom iN = beta.toOrderHom (Fin.last n) := by
      exact congrArg beta.toOrderHom hIdx
    have hPrefix :
        eqToHom (quillenABridgeDegInnerRightObj n i
          ((nerve D).map beta.op y)) = y.map h := by
      change eqToHom (congrArg y.obj hBIdx) = y.map h
      rw [← eqToHom_map]
      · exact congrArg y.map (Subsingleton.elim _ _)
      · exact hBIdx
    have hBetaDegRight :
        ((nerve D).σ i ((nerve D).map beta.op y)).right =
          y.obj (beta.toOrderHom iN) := rfl
    have hBetaObjLast : ((nerve D).map beta.op y).right =
        y.obj (beta.toOrderHom (Fin.last n)) := rfl
    have hPrefixHEq : HEq
        (eqToHom (quillenABridgeDegInnerRightObj n i
          ((nerve D).map beta.op y))) (y.map h) := heq_of_eq hPrefix
    have hSuffix : HEq (y.map j ≫ eqToHom hRightTop.symm)
        (y.map j) := CategoryTheory.comp_eqToHom_heq (y.map j) hRightTop.symm
    have hc := CategoryTheory.heq_comp
      hBetaDegRight hBetaObjLast hRightTop hPrefixHEq hSuffix
    simpa only [Category.assoc] using hc
  have hBetaDegRight :
      ((nerve D).σ i ((nerve D).map beta.op y)).right =
        y.obj (beta.toOrderHom iN) := rfl
  have hLeftTheta : HEq (leftPrefix ≫ theta)
      ((y.map f ≫ y.map g) ≫ theta) := by
    exact CategoryTheory.heq_comp
      (congrArg y.obj hBetaIndex) hRightTop rfl hLeft HEq.rfl
  have hRightTheta : HEq (rightPrefix ≫ theta)
      ((y.map h ≫ y.map j) ≫ theta) := by
    exact CategoryTheory.heq_comp
      hBetaDegRight hRightTop rfl hRight HEq.rfl
  have hPathTheta : (y.map f ≫ y.map g) ≫ theta =
      (y.map h ≫ y.map j) ≫ theta :=
    congrArg (fun z ↦ z ≫ theta) hPath
  have hPrefixTheta := hLeftTheta.trans
    ((heq_of_eq hPathTheta).trans hRightTheta.symm)
  have hSource : y.obj (betaDeg.toOrderHom (Fin.last (n + 1))) =
      ((nerve D).σ i ((nerve D).map beta.op y)).right :=
    (congrArg y.obj hBetaIndex).trans hBetaDegRight.symm
  have hFinal := CategoryTheory.heq_comp hSource rfl rfl
    hPrefixTheta (HEq.rfl : HEq
      (F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H)))
      (F.map (eqToHom (quillenABridgeDegInnerLeftObj n i H))))
  simpa only [leftPrefix, rightPrefix, Category.assoc] using hFinal

private def quillenATargetFiberRhoDegRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n + 1⦌) :=
  ⟨quillenAMappingIndex (n + 1) ((nerve C).σ i p.1),
    quillenAMappingCarrierInner F (n + 1)
      ((nerve C).σ i p.1)
      ((nerve D).σ i (CategoryBar.barChain x))
      (eqToHom (quillenABridgeDegInnerRightObj n i
          (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
        F.map (eqToHom (quillenABridgeDegInnerLeftObj n i p.1)))⟩

private noncomputable def quillenATargetFiberRhoCarrierDeg
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hGDeg : (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) :=
  quillenATargetFiberRhoCarrierFromRaw F y (n + 1)
    (SimplexCategory.σ i ≫ alpha)
      (quillenATargetFiberRhoDegRaw F n i p x) hGDeg
      ((Δ[1] : SSet.{max u v}).σ i t)

private noncomputable def quillenATargetFiberRhoOutputDegRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n + 1⦌) := by
  let betaTop := quillenATargetFiberRhoIndexMap (op ⦋n⦌) alpha t
  let GtTop : ComposableArrows D n := (nerve D).map betaTop.op y
  have hRightTop : (CategoryBar.barChain x).right =
      y.obj (alpha.toOrderHom (Fin.last n)) :=
    (congrArg (fun K : ComposableArrows D n ↦ K.right) hG).trans rfl
  let thetaTTop : GtTop.right ⟶ F.obj p.1.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n⦌) alpha t (Fin.last n))) ≫
        eqToHom hRightTop.symm ≫ CategoryBar.barCoeffR x
  exact ⟨quillenAMappingIndex (n + 1) ((nerve C).σ i p.1),
    quillenAMappingCarrierInner F (n + 1)
      ((nerve C).σ i p.1) ((nerve D).σ i GtTop)
      (eqToHom (quillenABridgeDegInnerRightObj n i GtTop) ≫
        thetaTTop ≫
        F.map (eqToHom (quillenABridgeDegInnerLeftObj n i p.1)))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTopRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawEquiv F (n + 1)
        ((quillenAMappingCarrier F).σ i
          (quillenATargetFiberRhoCarrierTop
            F y n p x alpha hG t)) =
      quillenATargetFiberRhoOutputDegRaw
        F y n i p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierTop
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoOutputDegRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_σ]
  rw [quillenAMappingCarrierDegInner_eq_canonical]
  refine Sigma.ext ?_ ?_
  · refine Sigma.ext
      (quillenAMappingCarrierDegIndex_chain n i
        (quillenAMappingIndex n p.1)) ?_
    change HEq (_ : PUnit) (_ : PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoDegRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGDeg : (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenAMappingCarrierRawEquiv F (n + 1)
        (quillenATargetFiberRhoCarrierDeg
          F y n i p x alpha hGDeg t) =
      quillenATargetFiberRhoOutputDegRaw
        F y n i p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierDeg
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoDegRaw
    quillenATargetFiberRhoOutputDegRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_incl]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext ?_ ?_
  · exact quillenATargetFiberRhoChain_sigma y i alpha t
  · apply quillenAProd_heq
    · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    · exact quillenATargetFiberRhoTheta_sigma
        F y n i p.1 (CategoryBar.barChain x) (CategoryBar.barCoeffR x)
          alpha hG hGDeg t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoCarrier_sigma_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGDeg : (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoCarrierDeg
        F y n i p x alpha hGDeg t =
      (quillenAMappingCarrier F).σ i
        (quillenATargetFiberRhoCarrierTop
          F y n p x alpha hG t) := by
  apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
  exact (quillenATargetFiberRhoDegRaw_sigma
    F y n i p x alpha hG hGDeg t).trans
      (quillenATargetFiberRhoTopRaw_sigma
        F y n i p x alpha hG t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFromRaw_sigma_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n)
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌))
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGDeg : (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map (SimplexCategory.σ i ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoFromRaw F y (n + 1)
        (SimplexCategory.σ i ≫ alpha)
          (quillenATargetFiberRhoDegRaw F n i p x) hGDeg
          ((Δ[1] : SSet.{max u v}).σ i t) =
      quillenATargetFiberDecodedMap F y (SimplexCategory.σ i).op
        (quillenATargetFiberRhoFromRaw F y n alpha ⟨p, x⟩ hG t) := by
  unfold quillenATargetFiberRhoFromRaw
    quillenATargetFiberDecodedMap
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · exact quillenATargetFiberRhoCarrier_sigma_canonical
      F y n i p x alpha hG hGDeg t
  · exact quillenATargetFiberRhoIndexMap_sigma i alpha t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoDecoded_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
        (SimplexCategory.mk n ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n⦌) p.1 =
        (nerve D).map p.2.op y})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoDecoded F y (n + 1)
        (quillenATargetFiberDecodedMap F y (SimplexCategory.σ i).op d)
        ((Δ[1] : SSet.{max u v}).σ i t) =
      quillenATargetFiberDecodedMap F y (SimplexCategory.σ i).op
        (quillenATargetFiberRhoDecoded F y n d t) := by
  let k := (SimplexCategory.σ i).op
  let e := quillenATargetFiberDecodedMap F y k d
  let rTop := quillenAMappingCarrierRawEquiv F n d.1.1
  have hGTop : CategoryBar.barChain rTop.2 =
      (nerve D).map d.1.2.op y :=
    (quillenATarget_eq_raw_chain F n d.1.1).symm.trans d.2
  let rDeg := quillenAMappingCarrierRawEquiv F (n + 1) e.1.1
  let alphaDeg := e.1.2
  have hGDeg : CategoryBar.barChain rDeg.2 =
      (nerve D).map alphaDeg.op y :=
    (quillenATarget_eq_raw_chain F (n + 1) e.1.1).symm.trans e.2
  let p := rTop.1
  let x := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          n p).app (op ⦋n⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F n).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_σ_of F n i p x
  change quillenAMappingCarrierRawEquiv F (n + 1)
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            n p).app (op ⦋n⦌) x)) = _ at hRaw
  let rExpected : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n + 1⦌) :=
    ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit C) n i p,
      quillenAMappingCarrierDegInnerOf F n i p x⟩
  have hRawE : rDeg = rExpected := by
    unfold rDeg e quillenATargetFiberDecodedMap
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alphaDeg.op y := by
    rw [← hRawE]
    exact hGDeg
  let rCanonical : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1),
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n + 1⦌) :=
    ⟨quillenAMappingIndex (n + 1) ((nerve C).σ i p.1),
      quillenAMappingCarrierInner F (n + 1) ((nerve C).σ i p.1)
        ((nerve D).σ i (CategoryBar.barChain x))
        (eqToHom (quillenABridgeDegInnerRightObj n i
            (CategoryBar.barChain x)) ≫ CategoryBar.barCoeffR x ≫
          F.map (eqToHom (quillenABridgeDegInnerLeftObj n i p.1)))⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      unfold rExpected rCanonical quillenAMappingIndex
      refine Sigma.ext (quillenAMappingCarrierDegIndex_chain n i p) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierDegInnerOf_eq_canonical F n i p x)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaDeg.op y := by
    rw [← hCanonical]
    exact hGExpected
  let alphaCanonical := SimplexCategory.σ i ≫ d.1.2
  have hk : k.unop = SimplexCategory.σ i := by
    rfl
  have hAlpha : alphaDeg = alphaCanonical := by
    unfold alphaDeg e quillenATargetFiberDecodedMap alphaCanonical
    dsimp only [k]
    rw [hk]
  have hGCanonicalExplicit : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaCanonical.op y := by
    rw [← hAlpha]
    exact hGCanonical
  have hReplace := quillenATargetFiberRhoFromRaw_congr
    F y (n + 1) (rfl : alphaDeg = alphaDeg) hRawE hGDeg hGExpected
      ((Δ[1] : SSet.{max u v}).σ i t)
  have hReplaceCanonical := quillenATargetFiberRhoFromRaw_congr
    F y (n + 1) (rfl : alphaDeg = alphaDeg) hCanonical
      hGExpected hGCanonical ((Δ[1] : SSet.{max u v}).σ i t)
  have hReplaceAlpha := quillenATargetFiberRhoFromRaw_congr
    F y (n + 1) hAlpha (rfl : rCanonical = rCanonical)
      hGCanonical hGCanonicalExplicit ((Δ[1] : SSet.{max u v}).σ i t)
  have hGSigma : (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y := by
    have h := hGCanonicalExplicit
    change (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y at h
    exact h
  let rDegAlias := quillenATargetFiberRhoDegRaw F n i p x
  have hDegAlias : rCanonical = rDegAlias := by
    rfl
  have hGDegAlias : CategoryBar.barChain rDegAlias.2 =
      (nerve D).map alphaCanonical.op y := by
    change (nerve D).σ i (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y
    exact hGSigma
  have hReplaceAlias := quillenATargetFiberRhoFromRaw_congr
    F y (n + 1) (rfl : alphaCanonical = alphaCanonical) hDegAlias
      hGCanonicalExplicit hGDegAlias ((Δ[1] : SSet.{max u v}).σ i t)
  unfold quillenATargetFiberRhoDecoded
  change quillenATargetFiberRhoFromRaw F y (n + 1)
      alphaDeg rDeg hGDeg ((Δ[1] : SSet.{max u v}).σ i t) =
    quillenATargetFiberDecodedMap F y k
      (quillenATargetFiberRhoFromRaw F y n d.1.2 rTop hGTop t)
  calc
    _ = quillenATargetFiberRhoFromRaw F y (n + 1)
        alphaDeg rExpected hGExpected
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplace
    _ = quillenATargetFiberRhoFromRaw F y (n + 1)
        alphaDeg rCanonical hGCanonical
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplaceCanonical
    _ = quillenATargetFiberRhoFromRaw F y (n + 1)
        alphaCanonical rCanonical hGCanonicalExplicit
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplaceAlpha
    _ = quillenATargetFiberRhoFromRaw F y (n + 1)
        alphaCanonical rDegAlias hGDegAlias
          ((Δ[1] : SSet.{max u v}).σ i t) := hReplaceAlias
    _ = _ := by
      simpa only [alphaCanonical, rDegAlias, rTop, p, x, k] using
        quillenATargetFiberRhoFromRaw_sigma_canonical
          F y n i p x d.1.2 hGTop hGSigma t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_sigma
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ) (i : Fin (n + 1))
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoAppRaw F y (n + 1)
        ((SSet.leftFiber (quillenATarget F) y ⊗
          (Δ[1] : SSet.{max u v})).σ i zt) =
      (SSet.leftFiber (quillenATarget F) y).σ i
        (quillenATargetFiberRhoAppRaw F y n zt) := by
  let k := (SimplexCategory.σ i).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n + 1⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  change quillenATargetFiberRhoDecoded F y (n + 1)
      (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n + 1⦌)
        ((SSet.leftFiber (quillenATarget F) y).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change quillenATargetFiberRhoDecoded F y (n + 1)
      (quillenATargetFiberDecodedMap F y k
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n + 1⦌))
      ((SSet.leftFiber (quillenATarget F) y).map k
        (quillenATargetFiberRhoAppRaw F y n zt))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  exact quillenATargetFiberRhoDecoded_sigma F y n i
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n⦌) zt.1) zt.2

private def quillenATargetFiberRhoFaceLastRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
  ⟨quillenAMappingIndex n ((nerve C).δ (Fin.last (n + 1)) p.1),
    quillenAMappingCarrierInner F n
      ((nerve C).δ (Fin.last (n + 1)) p.1)
      ((nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x))
      (eqToHom (quillenABridgeFaceLastRight n
          (CategoryBar.barChain x)) ≫
        (CategoryBar.barChain x).map' n (n + 1) ≫
        CategoryBar.barCoeffR x)⟩

private noncomputable def quillenATargetFiberRhoCarrierFaceLast
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hGFace : (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    (quillenAMappingCarrier F).obj (op ⦋n⦌) :=
  quillenATargetFiberRhoCarrierFromRaw F y n
    (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
      (quillenATargetFiberRhoFaceLastRaw F n p x) hGFace
      ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)

private noncomputable def quillenATargetFiberRhoOutputFaceLastRaw
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    Σ r : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) := by
  let betaTop := quillenATargetFiberRhoBetaTop alpha t
  let GtTop : ComposableArrows D (n + 1) := (nerve D).map betaTop.op y
  have hRightTop : (CategoryBar.barChain x).right =
      y.obj (alpha.toOrderHom (Fin.last (n + 1))) :=
    (congrArg (fun K : ComposableArrows D (n + 1) ↦ K.right) hG).trans rfl
  let thetaTTop : GtTop.right ⟶ F.obj p.1.left :=
    y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
      (op ⦋n + 1⦌) alpha t (Fin.last (n + 1)))) ≫
        eqToHom hRightTop.symm ≫ CategoryBar.barCoeffR x
  exact ⟨quillenAMappingIndex n
      ((nerve C).δ (Fin.last (n + 1)) p.1),
    quillenAMappingCarrierInner F n
      ((nerve C).δ (Fin.last (n + 1)) p.1)
      ((nerve D).δ (Fin.last (n + 1)) GtTop)
      (eqToHom (quillenABridgeFaceLastRight n GtTop) ≫
        GtTop.map' n (n + 1) ≫ thetaTTop)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTopRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        ((quillenAMappingCarrier F).δ (Fin.last (n + 1))
          (quillenATargetFiberRhoCarrierTop
            F y (n + 1) p x alpha hG t)) =
      quillenATargetFiberRhoOutputFaceLastRaw
        F y n p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierTop
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoOutputFaceLastRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_δ_last]
  rw [quillenAMappingCarrierFaceLastInner_eq_canonical]
  refine Sigma.ext ?_ ?_
  · refine Sigma.ext
      (quillenAMappingCarrierFaceLastIndex_chain n
        (quillenAMappingIndex (n + 1) p.1)) ?_
    change HEq (_ : PUnit) (_ : PUnit)
    exact heq_of_eq (Subsingleton.elim _ _)
  · rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFaceRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenAMappingCarrierRawEquiv F n
        (quillenATargetFiberRhoCarrierFaceLast
          F y n p x alpha hGFace t) =
      quillenATargetFiberRhoOutputFaceLastRaw
        F y n p x alpha hG t := by
  unfold quillenATargetFiberRhoCarrierFaceLast
    quillenATargetFiberRhoCarrierFromRaw
    quillenATargetFiberRhoFaceLastRaw
    quillenATargetFiberRhoOutputFaceLastRaw
  dsimp only
  rw [quillenAMappingCarrierRawEquiv_incl]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext ?_ ?_
  · exact quillenATargetFiberRhoChain_delta_last y alpha t
  · apply quillenAProd_heq
    · change HEq (_ : ULift PUnit) (_ : ULift PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    · exact quillenATargetFiberRhoTheta_delta_last
        F y n p.1 (CategoryBar.barChain x) (CategoryBar.barCoeffR x)
          alpha hG hGFace t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoCarrier_delta_last_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoCarrierFaceLast
        F y n p x alpha hGFace t =
      (quillenAMappingCarrier F).δ (Fin.last (n + 1))
        (quillenATargetFiberRhoCarrierTop
          F y (n + 1) p x alpha hG t) := by
  apply (quillenAMappingCarrierRawEquiv F n).injective
  exact (quillenATargetFiberRhoFaceRaw_delta_last
    F y n p x alpha hG hGFace t).trans
      (quillenATargetFiberRhoTopRaw_delta_last
        F y n p x alpha hG t).symm

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoFromRaw_delta_last_canonical
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1))
    (x : ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n + 1⦌))
    (alpha : ⦋n + 1⦌ ⟶ ⦋m⦌)
    (hG : CategoryBar.barChain x = (nerve D).map alpha.op y)
    (hGFace : (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha).op y)
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoFromRaw F y n
        (SimplexCategory.δ (Fin.last (n + 1)) ≫ alpha)
          (quillenATargetFiberRhoFaceLastRaw F n p x) hGFace
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ (Fin.last (n + 1))).op
          (quillenATargetFiberRhoFromRaw F y (n + 1)
            alpha ⟨p, x⟩ hG t) := by
  unfold quillenATargetFiberRhoFromRaw
    quillenATargetFiberDecodedMap
  dsimp only [id]
  apply Subtype.ext
  apply Prod.ext
  · exact quillenATargetFiberRhoCarrier_delta_last_canonical
      F y n p x alpha hG hGFace t
  · exact quillenATargetFiberRhoIndexMap_delta_last alpha t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoDecoded_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (d : {p : (quillenAMappingCarrier F).obj (op ⦋n + 1⦌) ×
        (SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk m) //
      (quillenATarget F).app (op ⦋n + 1⦌) p.1 =
        (nerve D).map p.2.op y})
    (t : (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoDecoded F y n
        (quillenATargetFiberDecodedMap F y
          (SimplexCategory.δ (Fin.last (n + 1))).op d)
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) =
      quillenATargetFiberDecodedMap F y
        (SimplexCategory.δ (Fin.last (n + 1))).op
          (quillenATargetFiberRhoDecoded F y (n + 1) d t) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  let e := quillenATargetFiberDecodedMap F y k d
  let rTop := quillenAMappingCarrierRawEquiv F (n + 1) d.1.1
  have hGTop : CategoryBar.barChain rTop.2 =
      (nerve D).map d.1.2.op y :=
    (quillenATarget_eq_raw_chain F (n + 1) d.1.1).symm.trans d.2
  let rFace := quillenAMappingCarrierRawEquiv F n e.1.1
  let alphaFace := e.1.2
  have hGFace : CategoryBar.barChain rFace.2 =
      (nerve D).map alphaFace.op y :=
    (quillenATarget_eq_raw_chain F n e.1.1).symm.trans e.2
  let p := rTop.1
  let x := rTop.2
  have hCarrier : d.1.1 =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) (quillenAMappingDiagram F)
          (n + 1) p).app (op ⦋n + 1⦌) x := by
    apply (quillenAMappingCarrierRawEquiv F (n + 1)).injective
    rw [quillenAMappingCarrierRawEquiv_wbarIncl]
  have hRaw := quillenAMappingCarrierRawEquiv_δ_last_of F n p x
  change quillenAMappingCarrierRawEquiv F n
      ((quillenAMappingCarrier F).map k
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) (quillenAMappingDiagram F)
            (n + 1) p).app (op ⦋n + 1⦌) x)) = _ at hRaw
  let rExpected : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
    ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n p,
      quillenAMappingCarrierFaceLastInnerOf F n p x⟩
  have hRawE : rFace = rExpected := by
    unfold rFace e quillenATargetFiberDecodedMap
    dsimp only [k]
    rw [hCarrier]
    exact hRaw
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hRawE]
    exact hGFace
  let rCanonical : Σ r : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj r.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n
        ((nerve C).δ (Fin.last (n + 1)) p.1),
      quillenAMappingCarrierInner F n
        ((nerve C).δ (Fin.last (n + 1)) p.1)
        ((nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x))
        (eqToHom (quillenABridgeFaceLastRight n
            (CategoryBar.barChain x)) ≫
          (CategoryBar.barChain x).map' n (n + 1) ≫
          CategoryBar.barCoeffR x)⟩
  have hCanonical : rExpected = rCanonical := by
    have hp : rExpected.1 = rCanonical.1 := by
      unfold rExpected rCanonical quillenAMappingIndex
      refine Sigma.ext
        (quillenAMappingCarrierFaceLastIndex_chain n p) ?_
      change HEq (_ : PUnit) (_ : PUnit)
      exact heq_of_eq (Subsingleton.elim _ _)
    refine Sigma.ext hp ?_
    exact heq_of_eq
      (quillenAMappingCarrierFaceLastInnerOf_eq_canonical F n p x)
  have hGCanonical : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaFace.op y := by
    rw [← hCanonical]
    exact hGExpected
  let alphaCanonical :=
    SimplexCategory.δ (Fin.last (n + 1)) ≫ d.1.2
  have hk : k.unop = SimplexCategory.δ (Fin.last (n + 1)) := by
    rfl
  have hAlpha : alphaFace = alphaCanonical := by
    unfold alphaFace e quillenATargetFiberDecodedMap alphaCanonical
    dsimp only [k]
    rw [hk]
  have hGCanonicalExplicit : CategoryBar.barChain rCanonical.2 =
      (nerve D).map alphaCanonical.op y := by
    rw [← hAlpha]
    exact hGCanonical
  have hReplace := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hRawE hGFace hGExpected
      ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  have hReplaceCanonical := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaFace = alphaFace) hCanonical
      hGExpected hGCanonical
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  have hReplaceAlpha := quillenATargetFiberRhoFromRaw_congr
    F y n hAlpha (rfl : rCanonical = rCanonical)
      hGCanonical hGCanonicalExplicit
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  have hGDelta :
      (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
        (nerve D).map alphaCanonical.op y := by
    have h := hGCanonicalExplicit
    change (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y at h
    exact h
  let rFaceAlias := quillenATargetFiberRhoFaceLastRaw F n p x
  have hFaceAlias : rCanonical = rFaceAlias := by
    rfl
  have hGFaceAlias : CategoryBar.barChain rFaceAlias.2 =
      (nerve D).map alphaCanonical.op y := by
    change (nerve D).δ (Fin.last (n + 1)) (CategoryBar.barChain x) =
      (nerve D).map alphaCanonical.op y
    exact hGDelta
  have hReplaceAlias := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alphaCanonical = alphaCanonical) hFaceAlias
      hGCanonicalExplicit hGFaceAlias
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t)
  unfold quillenATargetFiberRhoDecoded
  change quillenATargetFiberRhoFromRaw F y n
      alphaFace rFace hGFace
        ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) =
    quillenATargetFiberDecodedMap F y k
      (quillenATargetFiberRhoFromRaw F y (n + 1)
        d.1.2 rTop hGTop t)
  calc
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rExpected hGExpected
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := hReplace
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaFace rCanonical hGCanonical
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) :=
      hReplaceCanonical
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rCanonical hGCanonicalExplicit
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := hReplaceAlpha
    _ = quillenATargetFiberRhoFromRaw F y n
        alphaCanonical rFaceAlias hGFaceAlias
          ((Δ[1] : SSet.{max u v}).δ (Fin.last (n + 1)) t) := hReplaceAlias
    _ = _ := by
      simpa only [alphaCanonical, rFaceAlias, rTop, p, x, k] using
        quillenATargetFiberRhoFromRaw_delta_last_canonical
          F y n p x d.1.2 hGTop hGDelta t

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_delta_last
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (zt : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n + 1⦌) ×
      (Δ[1] : SSet.{max u v}).obj (op ⦋n + 1⦌)) :
    quillenATargetFiberRhoAppRaw F y n
        ((SSet.leftFiber (quillenATarget F) y ⊗
          (Δ[1] : SSet.{max u v})).δ (Fin.last (n + 1)) zt) =
      (SSet.leftFiber (quillenATarget F) y).δ (Fin.last (n + 1))
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt) := by
  let k := (SimplexCategory.δ (Fin.last (n + 1))).op
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  change quillenATargetFiberRhoDecoded F y n
      (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌)
        ((SSet.leftFiber (quillenATarget F) y).map k zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) = _
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  change quillenATargetFiberRhoDecoded F y n
      (quillenATargetFiberDecodedMap F y k
        (SSet.leftFiber.objEquiv
          (quillenATarget F) y (op ⦋n + 1⦌) zt.1))
      ((Δ[1] : SSet.{max u v}).map k zt.2) =
    (SSet.leftFiber.objEquiv (quillenATarget F) y (op ⦋n⦌))
      ((SSet.leftFiber (quillenATarget F) y).map k
        (quillenATargetFiberRhoAppRaw F y (n + 1) zt))
  rw [← quillenATargetFiberDecodedMap_objEquiv F y k]
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  exact quillenATargetFiberRhoDecoded_delta_last F y n
    (SSet.leftFiber.objEquiv
      (quillenATarget F) y (op ⦋n + 1⦌) zt.1) zt.2

private noncomputable def quillenATargetFiberRhoAppNat
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌)
    (a : SimplexCategoryᵒᵖ) :
    ((SSet.leftFiber (quillenATarget F) y) ⊗
      (Δ[1] : SSet.{max u v})).obj a ⟶
        (SSet.leftFiber (quillenATarget F) y).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact ↾(quillenATargetFiberRhoAppRaw F y n)

private noncomputable def quillenATargetFiberRhoMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    (SSet.leftFiber (quillenATarget F) y) ⊗
        (Δ[1] : SSet.{max u v}) ⟶
      SSet.leftFiber (quillenATarget F) y where
  app a := quillenATargetFiberRhoAppNat F y a
  naturality {a b} k := by
    let W : MorphismProperty SimplexCategory := fun {A B} f ↦
      ((SSet.leftFiber (quillenATarget F) y) ⊗
          (Δ[1] : SSet.{max u v})).map f.op ≫
          quillenATargetFiberRhoAppNat F y (op A) =
        quillenATargetFiberRhoAppNat F y (op B) ≫
          (SSet.leftFiber (quillenATarget F) y).map f.op
    have hW : W.IsMultiplicative :=
      { id_mem := by
          intro A
          dsimp only [W]
          rw [op_id, Functor.map_id, Functor.map_id]
          rw [Category.id_comp, Category.comp_id]
        comp_mem := by
          intro A B E f g hf hg
          dsimp only [W] at hf hg ⊢
          rw [op_comp, Functor.map_comp, Functor.map_comp,
            Category.assoc, hf, ← Category.assoc, hg, Category.assoc] }
    have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
        W (SimplexCategory.δ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberRhoAppRaw F y n
          (((SSet.leftFiber (quillenATarget F) y) ⊗
            (Δ[1] : SSet.{max u v})).δ i z) =
        (SSet.leftFiber (quillenATarget F) y).δ i
          (quillenATargetFiberRhoAppRaw F y (n + 1) z)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact quillenATargetFiberRhoAppRaw_delta_zero F y n z
      · refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · exact quillenATargetFiberRhoAppRaw_delta_last F y n z
        · exact quillenATargetFiberRhoAppRaw_delta_inner F y n q z
    have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
        W (SimplexCategory.σ i) := by
      intro n i
      dsimp only [W]
      ext z
      change quillenATargetFiberRhoAppRaw F y (n + 1)
          (((SSet.leftFiber (quillenATarget F) y) ⊗
            (Δ[1] : SSet.{max u v})).σ i z) =
        (SSet.leftFiber (quillenATarget F) y).σ i
          (quillenATargetFiberRhoAppRaw F y n z)
      exact quillenATargetFiberRhoAppRaw_sigma F y n i z
    have hTop : W = ⊤ :=
      @SimplexCategory.morphismProperty_eq_top W hW hδ hσ
    have hk : W k.unop := by
      rw [hTop]
      trivial
    exact hk

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_iota_one
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C n)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (theta : ((nerve D).map alpha.op y).right ⟶ F.obj H.left)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    let beta := quillenATargetFiberRhoIndexMap
      (op ⦋n⦌) alpha (SSet.ι₁.app (op ⦋n⦌) z).2
    let Gt : ComposableArrows D n := (nerve D).map beta.op y
    have hRight : ((nerve D).map alpha.op y).right =
        y.obj (alpha.toOrderHom (Fin.last n)) := rfl
    let thetaT : Gt.right ⟶ F.obj H.left :=
      y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
        (op ⦋n⦌) alpha (SSet.ι₁.app (op ⦋n⦌) z).2
          (Fin.last n))) ≫ eqToHom hRight.symm ≫ theta
    HEq thetaT theta := by
  dsimp only
  unfold quillenATargetFiberRhoIndexMap
  simp only [Nat.reduceAdd, Monoidal.tensorObj_obj, Fin.isValue,
    Quiver.Hom.unop_op, homOfLE_refl, Functor.map_id, eqToHom_refl,
    Category.id_comp, heq_eq_eq]
  exact Category.id_comp theta

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoTheta_iota_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C n)
    (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (theta : ((nerve D).map alpha.op y).right ⟶ F.obj H.left)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    let beta := quillenATargetFiberRhoIndexMap
      (op ⦋n⦌) alpha (SSet.ι₀.app (op ⦋n⦌) z).2
    let Gt : ComposableArrows D n := (nerve D).map beta.op y
    have hRight : ((nerve D).map alpha.op y).right =
        y.obj (alpha.toOrderHom (Fin.last n)) := rfl
    let thetaT : Gt.right ⟶ F.obj H.left :=
      y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
        (op ⦋n⦌) alpha (SSet.ι₀.app (op ⦋n⦌) z).2
          (Fin.last n))) ≫ eqToHom hRight.symm ≫ theta
    let alphaZero := quillenATargetFiberFirstVertexMap m n
    let GZero : ComposableArrows D n := (nerve D).map alphaZero.op y
    have hRightZero : GZero.right = y.obj 0 := rfl
    let phi : y.obj 0 ⟶ F.obj H.left :=
      y.map (homOfLE (Fin.zero_le (alpha.toOrderHom (Fin.last n)))) ≫
        eqToHom hRight.symm ≫ theta
    let thetaZero : GZero.right ⟶ F.obj H.left :=
      eqToHom hRightZero ≫ phi
    HEq thetaT thetaZero := by
  dsimp only
  unfold quillenATargetFiberRhoIndexMap
    quillenATargetFiberFirstVertexMap
  simp

private structure quillenATargetFiberEndpointInnerPacket
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ} (H : ComposableArrows C n) where
  output : Σ L : ComposableArrows D n, L.right ⟶ F.obj H.left
  expected : Σ L : ComposableArrows D n, L.right ⟶ F.obj H.left
  eq : HEq output expected

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quillenATargetFiberRhoInnerIotaOnePacket
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C n) (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (theta : ((nerve D).map alpha.op y).right ⟶ F.obj H.left)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    quillenATargetFiberEndpointInnerPacket F H where
  output :=
    let beta := quillenATargetFiberRhoIndexMap
      (op ⦋n⦌) alpha (SSet.ι₁.app (op ⦋n⦌) z).2
    let Gt : ComposableArrows D n := (nerve D).map beta.op y
    have hRight : ((nerve D).map alpha.op y).right =
        y.obj (alpha.toOrderHom (Fin.last n)) := rfl
    let thetaT : Gt.right ⟶ F.obj H.left :=
      y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
        (op ⦋n⦌) alpha (SSet.ι₁.app (op ⦋n⦌) z).2
          (Fin.last n))) ≫ eqToHom hRight.symm ≫ theta
    ⟨Gt, thetaT⟩
  expected := ⟨(nerve D).map alpha.op y, theta⟩
  eq := by
    dsimp only
    exact quillenASigma_heq
      (heq_of_eq (congrArg
        (fun beta : ⦋n⦌ ⟶ ⦋m⦌ ↦ (nerve D).map beta.op y)
        (quillenATargetFiberRhoIndexMap_iota_one z alpha)))
      (quillenATargetFiberRhoTheta_iota_one F y n H alpha theta z)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quillenATargetFiberRhoInnerIotaZeroPacket
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (H : ComposableArrows C n) (alpha : ⦋n⦌ ⟶ ⦋m⦌)
    (theta : ((nerve D).map alpha.op y).right ⟶ F.obj H.left)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    quillenATargetFiberEndpointInnerPacket F H where
  output :=
    let beta := quillenATargetFiberRhoIndexMap
      (op ⦋n⦌) alpha (SSet.ι₀.app (op ⦋n⦌) z).2
    let Gt : ComposableArrows D n := (nerve D).map beta.op y
    have hRight : ((nerve D).map alpha.op y).right =
        y.obj (alpha.toOrderHom (Fin.last n)) := rfl
    let thetaT : Gt.right ⟶ F.obj H.left :=
      y.map (homOfLE (quillenATargetFiberRhoIndexMap_le
        (op ⦋n⦌) alpha (SSet.ι₀.app (op ⦋n⦌) z).2
          (Fin.last n))) ≫ eqToHom hRight.symm ≫ theta
    ⟨Gt, thetaT⟩
  expected :=
    let alphaZero := quillenATargetFiberFirstVertexMap m n
    let GZero : ComposableArrows D n := (nerve D).map alphaZero.op y
    have hRight : ((nerve D).map alpha.op y).right =
        y.obj (alpha.toOrderHom (Fin.last n)) := rfl
    have hRightZero : GZero.right = y.obj 0 := rfl
    let phi : y.obj 0 ⟶ F.obj H.left :=
      y.map (homOfLE (Fin.zero_le (alpha.toOrderHom (Fin.last n)))) ≫
        eqToHom hRight.symm ≫ theta
    let thetaZero : GZero.right ⟶ F.obj H.left :=
      eqToHom hRightZero ≫ phi
    ⟨GZero, thetaZero⟩
  eq := by
    dsimp only
    exact quillenASigma_heq
      (heq_of_eq (congrArg
        (fun beta : ⦋n⦌ ⟶ ⦋m⦌ ↦ (nerve D).map beta.op y)
        (quillenATargetFiberRhoIndexMap_iota_zero z alpha)))
      (quillenATargetFiberRhoTheta_iota_zero F y n H alpha theta z)

private theorem quillenAMappingRaw_eq_of_endpointPacket
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {n : ℕ} (H : ComposableArrows C n)
    (P : quillenATargetFiberEndpointInnerPacket F H) :
    (⟨quillenAMappingIndex n H,
      quillenAMappingCarrierInner F n H P.output.1 P.output.2⟩ :
        Σ p : StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n,
          ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) =
      ⟨quillenAMappingIndex n H,
        quillenAMappingCarrierInner F n H P.expected.1 P.expected.2⟩ :=
  congrArg
    (fun q : Σ G : ComposableArrows D n, G.right ⟶ F.obj H.left ↦
      (⟨quillenAMappingIndex n H,
        quillenAMappingCarrierInner F n H q.1 q.2⟩ :
          Σ p : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n,
            ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)))
    (eq_of_heq P.eq)



set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_iota_one
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoAppRaw F y n
        (SSet.ι₁.app (op ⦋n⦌) z) = z := by
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv]
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌) z
  change quillenATargetFiberRhoDecoded F y n d
      (SSet.ι₁.app (op ⦋n⦌) z).2 = d
  rcases d with ⟨⟨c, alpha⟩, hd⟩
  rcases hc : quillenAMappingCarrierObjEquiv F n c with ⟨H, G, theta⟩
  have hc' : c = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [hc, quillenAMappingCarrierObjEquiv_incl]
  subst c
  have hG : G = (nerve D).map alpha.op y := by
    rw [quillenATarget_carrierIncl] at hd
    exact hd
  subst G
  let d' : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenATarget F).app (op ⦋n⦌) p.1 =
      (nerve D).map p.2.op y} :=
    ⟨⟨quillenAMappingCarrierIncl F n H
      ((nerve D).map alpha.op y) theta, alpha⟩, hd⟩
  let r := quillenAMappingCarrierRawEquiv F n d'.1.1
  let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n H,
      quillenAMappingCarrierInner F n H
        ((nerve D).map alpha.op y) theta⟩
  have hRaw : r = rExpected := by
    unfold r d' rExpected
    exact quillenAMappingCarrierRawEquiv_incl F n H
      ((nerve D).map alpha.op y) theta
  have hGActual : CategoryBar.barChain r.2 =
      (nerve D).map alpha.op y :=
    quillenATargetFiberRhoDecoded_hG F y n d'
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alpha.op y := rfl
  have hReplace := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alpha = alpha) hRaw hGActual hGExpected
      (SSet.ι₁.app (op ⦋n⦌) z).2
  unfold quillenATargetFiberRhoDecoded
  change quillenATargetFiberRhoFromRaw F y n
      alpha r hGActual (SSet.ι₁.app (op ⦋n⦌) z).2 = d'
  calc
    _ = quillenATargetFiberRhoFromRaw F y n
        alpha rExpected hGExpected
          (SSet.ι₁.app (op ⦋n⦌) z).2 := hReplace
    _ = d' := by
      unfold quillenATargetFiberRhoFromRaw
      dsimp only [rExpected, d', id]
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F n).injective
        unfold quillenATargetFiberRhoCarrierFromRaw
        dsimp only [id]
        rw [quillenAMappingCarrierRawEquiv_incl,
          quillenAMappingCarrierRawEquiv_incl]
        let P := quillenATargetFiberRhoInnerIotaOnePacket
          F y n H alpha theta z
        change (⟨quillenAMappingIndex n H,
            quillenAMappingCarrierInner F n H P.output.1 P.output.2⟩ :
              Σ p : StrictOrdinaryWeightedBar.WIdx C
                (CategoryBar.replUnit C) n,
                ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) =
          ⟨quillenAMappingIndex n H,
            quillenAMappingCarrierInner F n H P.expected.1 P.expected.2⟩
        exact quillenAMappingRaw_eq_of_endpointPacket F H P
      · exact quillenATargetFiberRhoIndexMap_iota_one z alpha

set_option backward.isDefEq.respectTransparency false in
private theorem quillenATargetFiberRhoAppRaw_iota_zero
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) (n : ℕ)
    (z : (SSet.leftFiber (quillenATarget F) y).obj (op ⦋n⦌)) :
    quillenATargetFiberRhoAppRaw F y n
        (SSet.ι₀.app (op ⦋n⦌) z) =
      quillenATargetFiberSectionApp F y n
        (quillenATargetFiberRetractionAppRaw F y n z) := by
  apply (SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌)).injective
  rw [quillenATargetFiberRhoAppRaw_objEquiv,
    quillenATargetFiberSectionApp_objEquiv]
  let d := SSet.leftFiber.objEquiv
    (quillenATarget F) y (op ⦋n⦌) z
  change quillenATargetFiberRhoDecoded F y n d
      (SSet.ι₀.app (op ⦋n⦌) z).2 =
    quillenATargetFiberSectionDecoded F y n
      (quillenATargetFiberRetractionDecoded F y n d)
  rcases d with ⟨⟨c, alpha⟩, hd⟩
  rcases hc : quillenAMappingCarrierObjEquiv F n c with ⟨H, G, theta⟩
  have hc' : c = quillenAMappingCarrierIncl F n H G theta := by
    apply (quillenAMappingCarrierObjEquiv F n).injective
    rw [hc, quillenAMappingCarrierObjEquiv_incl]
  subst c
  have hG : G = (nerve D).map alpha.op y := by
    rw [quillenATarget_carrierIncl] at hd
    exact hd
  subst G
  let d' : {p : (quillenAMappingCarrier F).obj (op ⦋n⦌) ×
      (⦋n⦌ ⟶ ⦋m⦌) //
    (quillenATarget F).app (op ⦋n⦌) p.1 =
      (nerve D).map p.2.op y} :=
    ⟨⟨quillenAMappingCarrierIncl F n H
      ((nerve D).map alpha.op y) theta, alpha⟩, hd⟩
  let r := quillenAMappingCarrierRawEquiv F n d'.1.1
  let rExpected : Σ p : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n,
      ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌) :=
    ⟨quillenAMappingIndex n H,
      quillenAMappingCarrierInner F n H
        ((nerve D).map alpha.op y) theta⟩
  have hRaw : r = rExpected := by
    unfold r d' rExpected
    exact quillenAMappingCarrierRawEquiv_incl F n H
      ((nerve D).map alpha.op y) theta
  have hGActual : CategoryBar.barChain r.2 =
      (nerve D).map alpha.op y :=
    quillenATargetFiberRhoDecoded_hG F y n d'
  have hGExpected : CategoryBar.barChain rExpected.2 =
      (nerve D).map alpha.op y := rfl
  have hRhoReplace := quillenATargetFiberRhoFromRaw_congr
    F y n (rfl : alpha = alpha) hRaw hGActual hGExpected
      (SSet.ι₀.app (op ⦋n⦌) z).2
  have hRetReplace := quillenATargetFiberRetractionFromRaw_congr
    F y n (rfl : alpha = alpha) hRaw hGActual hGExpected
  have hSectionReplace := congrArg
    (quillenATargetFiberSectionDecoded F y n) hRetReplace
  unfold quillenATargetFiberRhoDecoded
    quillenATargetFiberRetractionDecoded
  change quillenATargetFiberRhoFromRaw F y n
      alpha r hGActual (SSet.ι₀.app (op ⦋n⦌) z).2 =
    quillenATargetFiberSectionDecoded F y n
      (quillenATargetFiberRetractionFromRaw F y n alpha r hGActual)
  calc
    _ = quillenATargetFiberRhoFromRaw F y n
        alpha rExpected hGExpected
          (SSet.ι₀.app (op ⦋n⦌) z).2 := hRhoReplace
    _ = quillenATargetFiberSectionDecoded F y n
        (quillenATargetFiberRetractionFromRaw F y n
          alpha rExpected hGExpected) := by
      unfold quillenATargetFiberRhoFromRaw
        quillenATargetFiberRetractionFromRaw
        quillenATargetFiberSectionDecoded
      dsimp only [rExpected, id]
      apply Subtype.ext
      apply Prod.ext
      · apply (quillenAMappingCarrierRawEquiv F n).injective
        unfold quillenATargetFiberRhoCarrierFromRaw
        dsimp only [id]
        rw [quillenAMappingCarrierRawEquiv_incl,
          quillenAMappingCarrierRawEquiv_incl]
        let P := quillenATargetFiberRhoInnerIotaZeroPacket
          F y n H alpha theta z
        change (⟨quillenAMappingIndex n H,
            quillenAMappingCarrierInner F n H P.output.1 P.output.2⟩ :
              Σ p : StrictOrdinaryWeightedBar.WIdx C
                (CategoryBar.replUnit C) n,
                ((quillenAMappingDiagram F).obj p.1.left).obj (op ⦋n⦌)) =
          ⟨quillenAMappingIndex n H,
            quillenAMappingCarrierInner F n H P.expected.1 P.expected.2⟩
        exact quillenAMappingRaw_eq_of_endpointPacket F H P
      · exact quillenATargetFiberRhoIndexMap_iota_zero z alpha
    _ = quillenATargetFiberSectionDecoded F y n
        (quillenATargetFiberRetractionFromRaw F y n
          alpha r hGActual) := hSectionReplace.symm

private theorem quillenATargetFiberRhoMap_h0
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    SSet.ι₀ ≫ quillenATargetFiberRhoMap F y =
      quillenATargetFiberRetraction F y ≫
        quillenATargetFiberSection F y := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenATargetFiberRhoAppRaw_iota_zero F y n z

private theorem quillenATargetFiberRhoMap_h1
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    SSet.ι₁ ≫ quillenATargetFiberRhoMap F y =
      𝟙 (SSet.leftFiber (quillenATarget F) y) := by
  apply SSet.hom_ext
  intro a
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n =>
      ext z
      exact quillenATargetFiberRhoAppRaw_iota_one F y n z

private noncomputable def quillenATargetFiberRhoHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {m : ℕ}
    (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    SSet.Homotopy
      (quillenATargetFiberRetraction F y ≫
        quillenATargetFiberSection F y)
      (𝟙 (SSet.leftFiber (quillenATarget F) y)) where
  h := quillenATargetFiberRhoMap F y
  h₀ := quillenATargetFiberRhoMap_h0 F y
  h₁ := quillenATargetFiberRhoMap_h1 F y
  rel := by
    ext a z
    exact z.1.2.elim


private noncomputable def quillenARealizedHomotopyEquivOfSectionRetractionToId
    {X Y : SSet.{w}} (r : X ⟶ Y) (s : Y ⟶ X)
    (hsr : s ≫ r = 𝟙 Y)
    (H : SSet.Homotopy (r ≫ s) (𝟙 X)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map r).hom
  invFun := (SSet.toTop.map s).hom
  left_inv := by
    refine ⟨?_⟩
    have h := SSet.realizeHomotopy X X (r ≫ s) (𝟙 X) H
    apply ContinuousMap.Homotopy.cast h
    · rw [Functor.map_comp]
      rfl
    · exact congrArg ConcreteCategory.hom
        (CategoryTheory.Functor.map_id SSet.toTop X)
  right_inv := by
    have hcomp :
        (SSet.toTop.map r).hom.comp (SSet.toTop.map s).hom =
          ContinuousMap.id (SSet.toTop.obj Y) := by
      rw [← TopCat.hom_comp, ← Functor.map_comp, hsr,
        CategoryTheory.Functor.map_id]
      rfl
    rw [hcomp]

private theorem quillenARetraction_mem_realizationWeakEquivalences_of_homotopy_to_id
    {X Y : SSet.{w}} (r : X ⟶ Y) (s : Y ⟶ X)
    (hsr : s ≫ r = 𝟙 Y)
    (H : SSet.Homotopy (r ≫ s) (𝟙 X)) :
    SSet.realizationWeakEquivalences r := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map r)
  exact TopCat.mem_of_eq_toFun
    (quillenARealizedHomotopyEquivOfSectionRetractionToId r s hsr H) rfl

private theorem quillenATargetFiber_to_terminal_of_retraction
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (d : D) (X : SSet.{max u v})
    (r : X ⟶ CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F d))
    (s : CategoryBar.simplicialReplacement
      (CategoryBar.commaCoeffL F d) ⟶ X)
    (hsr : s ≫ r = 𝟙 _)
    (H : SSet.Homotopy (r ≫ s) (𝟙 X))
    (h : SSet.realizationWeakEquivalences
      (terminal.from (nerve (StructuredArrow d F) : SSet.{max u v}))) :
    SSet.realizationWeakEquivalences (terminal.from X) := by
  have hr := quillenARetraction_mem_realizationWeakEquivalences_of_homotopy_to_id r s hsr H
  have hi : SSet.realizationWeakEquivalences
      (CategoryBar.commaReplacementNerveIso F d).hom :=
    MorphismProperty.of_isIso SSet.realizationWeakEquivalences _
  have hri := SSet.realizationWeakEquivalences.comp_mem r
    (CategoryBar.commaReplacementNerveIso F d).hom hr hi
  have htotal := SSet.realizationWeakEquivalences.comp_mem
    (r ≫ (CategoryBar.commaReplacementNerveIso F d).hom)
    (terminal.from (nerve (StructuredArrow d F) : SSet.{max u v})) hri h
  simpa only [Category.assoc,
    Subsingleton.elim
      ((r ≫ (CategoryBar.commaReplacementNerveIso F d).hom) ≫
        terminal.from (nerve (StructuredArrow d F) : SSet.{max u v}))
      (terminal.from X)] using htotal

private theorem quillenATargetFiber_to_terminal_mem
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D)
    (h : ∀ d : D, SSet.realizationWeakEquivalences
      (terminal.from
        (nerve (StructuredArrow d F) : SSet.{max u v})))
    {m : ℕ} (y : (nerve D : SSet.{max u v}) _⦋m⦌) :
    SSet.realizationWeakEquivalences
      (terminal.from (SSet.leftFiber (quillenATarget F) y)) := by
  exact quillenATargetFiber_to_terminal_of_retraction
    F (y.obj 0) (SSet.leftFiber (quillenATarget F) y)
    (quillenATargetFiberRetraction F y)
    (quillenATargetFiberSection F y)
    (quillenATargetFiberSection_comp_retraction F y)
    (quillenATargetFiberRhoHomotopy F y)
    (h (y.obj 0))

private theorem quillenAPairTerminal_cancel
    {X Y : SSet.{w}} (f : X ⟶ Y)
    (h : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (prod.lift f (terminal.from X)))) :
    SSet.realizationWeakEquivalences f := by
  have hp : SSet.realizationWeakEquivalences
      (prod.lift f (terminal.from X)) := h
  have hu : SSet.realizationWeakEquivalences
      (Limits.prod.rightUnitor Y).hom :=
    MorphismProperty.of_isIso SSet.realizationWeakEquivalences _
  have hc := SSet.realizationWeakEquivalences.comp_mem
    (prod.lift f (terminal.from X)) (Limits.prod.rightUnitor Y).hom hp hu
  simpa only [Limits.prod.rightUnitor_hom, prod.lift_fst] using hc

public theorem nerveMap_mem_realizationWeakEquivalences_of_structuredArrow
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D)
    (h : ∀ d : D, SSet.realizationWeakEquivalences
      (terminal.from
        (nerve (StructuredArrow d F) : SSet.{max u v}))) :
    SSet.realizationWeakEquivalences (nerveMap F) := by
  have hTargetPair := SSet.theoremAStar
    (quillenATarget F) (terminal.from (quillenAMappingCarrier F))
    (fun m y ↦ by
      have heq : SSet.leftFiber.π (quillenATarget F) y ≫
          terminal.from (quillenAMappingCarrier F) =
        terminal.from (SSet.leftFiber (quillenATarget F) y) :=
        Subsingleton.elim _ _
      rw [heq]
      exact quillenATargetFiber_to_terminal_mem F h y)
  have hTarget : SSet.realizationWeakEquivalences (quillenATarget F) :=
    quillenAPairTerminal_cancel (quillenATarget F) hTargetPair
  have hSourcePair := SSet.theoremAStar
    (quillenASource F) (terminal.from (quillenAMappingCarrier F))
    (fun m x ↦ by
      have heq : SSet.leftFiber.π (quillenASource F) x ≫
          terminal.from (quillenAMappingCarrier F) =
        terminal.from (SSet.leftFiber (quillenASource F) x) :=
        Subsingleton.elim _ _
      rw [heq]
      exact quillenASourceFiber_to_terminal_mem F x)
  have hSource : SSet.realizationWeakEquivalences (quillenASource F) :=
    quillenAPairTerminal_cancel (quillenASource F) hSourcePair
  have hComposite : SSet.realizationWeakEquivalences
      (quillenASource F ≫ nerveMap F) :=
    quillenARealizationWeakEquivalences_of_homotopy
      (quillenAMappingHomotopy F) hTarget
  exact SSet.realizationWeakEquivalences.of_precomp
    (quillenASource F) (nerveMap F) hSource hComposite

end CategoryTheory
