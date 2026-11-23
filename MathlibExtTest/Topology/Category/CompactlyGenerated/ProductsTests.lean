/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedByCounit
public import MathlibExt.Topology.Category.CompactlyGenerated.Products

/-!
# Tests for products of compactly generated spaces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace MathlibExtTest.CompactlyGenerated.ProductsTests

section Symbolic

variable {I : Type v} (X : I → CompactlyGenerated.{u, v}) (i : I)

#check CompactlyGenerated.piObj
#check CompactlyGenerated.piπ
#check CompactlyGenerated.piFan
#check CompactlyGenerated.piFanIsLimit
#check CompactlyGenerated.piIsoPi
#check CompactlyGenerated.piComparisonToTop
#check CompactlyGenerated.piComparisonToTop_apply
#check CompactlyGenerated.piComparisonToTop_generic_coherence
#check CompactlyGenerated.piComparisonToTop_isHomeomorph_iff
#check CompactlyGenerated.prodComparisonToTop

example : HasProducts.{v} CompactlyGenerated.{u, v} := inferInstance

example : CartesianMonoidalCategory CompactlyGenerated.{u, v} := inferInstance

example : HasProducts.{v} CompactlyGenerated.{u, v} :=
  CompactlyGenerated.instHasProducts

example : CartesianMonoidalCategory CompactlyGenerated.{u, v} :=
  CompactlyGenerated.instCartesianMonoidalCategory

example : (inferInstance : HasProducts.{v} CompactlyGenerated.{u, v}) =
    CompactlyGenerated.instHasProducts := rfl

example :
    (inferInstance : CartesianMonoidalCategory CompactlyGenerated.{u, v}) =
      CompactlyGenerated.instCartesianMonoidalCategory := rfl

example : CompactlyGenerated.piObj X ⟶ X i := CompactlyGenerated.piπ X i

example :
    CompactlyGenerated.piπ X i ≫ CompactlyGenerated.adj.unit.app (X i) =
      TopCat.toCompactlyGenerated.map
        (TopCat.piπ (fun i ↦
          CompactlyGenerated.compactlyGeneratedToTop.obj (X i)) i) := by
  simp [CompactlyGenerated.piπ]
  rfl

example :
    (CompactlyGenerated.piIsoPi X).hom ≫ CompactlyGenerated.piπ X i =
      Pi.π X i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) (CompactlyGenerated.piFanIsLimit X) ⟨i⟩

example (x : CompactlyGenerated.piObj X) :
    CompactlyGenerated.piComparisonToTop X x = x :=
  CompactlyGenerated.piComparisonToTop_apply X x

example :
    CompactlyGenerated.compactlyGeneratedToTop.map
          (CompactlyGenerated.piIsoPi X).hom ≫
        CompactlyGenerated.piComparisonToTop X =
      Limits.piComparison CompactlyGenerated.compactlyGeneratedToTop X ≫
        (TopCat.piIsoPi (fun i ↦
          CompactlyGenerated.compactlyGeneratedToTop.obj (X i))).hom :=
  CompactlyGenerated.piComparisonToTop_generic_coherence X

example (h : IsHomeomorph (CompactlyGenerated.piComparisonToTop X)) :
    UCompactlyGeneratedSpace.{u}
      ((TopCat.piFan (fun i ↦
        CompactlyGenerated.compactlyGeneratedToTop.obj (X i))).pt : Type v) :=
  (CompactlyGenerated.piComparisonToTop_isHomeomorph_iff X).mp h

example (h : UCompactlyGeneratedSpace.{u}
    ((TopCat.piFan (fun i ↦
      CompactlyGenerated.compactlyGeneratedToTop.obj (X i))).pt : Type v)) :
    IsHomeomorph (CompactlyGenerated.piComparisonToTop X) :=
  (CompactlyGenerated.piComparisonToTop_isHomeomorph_iff X).mpr h

end Symbolic

section UniverseMatrix

example : HasProducts.{0} CompactlyGenerated.{0, 0} := inferInstance
example : HasProducts.{1} CompactlyGenerated.{1, 1} := inferInstance
example : HasProducts.{1} CompactlyGenerated.{0, 1} := inferInstance
example : HasProducts.{0} CompactlyGenerated.{1, 0} := inferInstance

example : CartesianMonoidalCategory CompactlyGenerated.{0, 0} := inferInstance
example : CartesianMonoidalCategory CompactlyGenerated.{1, 1} := inferInstance
example : CartesianMonoidalCategory CompactlyGenerated.{0, 1} := inferInstance
example : CartesianMonoidalCategory CompactlyGenerated.{1, 0} := inferInstance

end UniverseMatrix

section EmptyAndSingleton

private abbrev emptyFamily : PEmpty → CompactlyGenerated.{u, v} :=
  fun i ↦ i.elim

  private abbrev emptyFan (Z : CompactlyGenerated.{u, v}) :
    Fan emptyFamily :=
  Fan.mk Z (fun j ↦ j.elim)

example (Z : CompactlyGenerated.{u, v}) :
    Z ⟶ CompactlyGenerated.piObj emptyFamily :=
  (CompactlyGenerated.piFanIsLimit emptyFamily).lift (emptyFan Z)

example {Z : CompactlyGenerated.{u, v}}
    (a b : Z ⟶ CompactlyGenerated.piObj emptyFamily) : a = b := by
  apply (CompactlyGenerated.piFanIsLimit emptyFamily).hom_ext
  rintro ⟨i⟩
  exact i.elim

private abbrev singletonFamily (X : CompactlyGenerated.{u, v}) :
    PUnit → CompactlyGenerated.{u, v} :=
  fun _ ↦ X

example (X : CompactlyGenerated.{u, v}) :
    (∏ᶜ singletonFamily X) ≅
      CompactlyGenerated.piObj (singletonFamily X) :=
  CompactlyGenerated.piIsoPi (singletonFamily X)

example (X : CompactlyGenerated.{u, v}) :
    (CompactlyGenerated.piIsoPi (singletonFamily X)).hom ≫
        CompactlyGenerated.piπ (singletonFamily X) PUnit.unit =
      Pi.π (singletonFamily X) PUnit.unit :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit _)
    (CompactlyGenerated.piFanIsLimit (singletonFamily X))
    ⟨PUnit.unit⟩

example (X Z : CompactlyGenerated.{u, v})
    (a b : Z ⟶ ∏ᶜ singletonFamily X)
    (h : a ≫ Pi.π (singletonFamily X) PUnit.unit =
      b ≫ Pi.π (singletonFamily X) PUnit.unit) :
    a = b := by
  apply (limit.isLimit (Discrete.functor (singletonFamily X))).hom_ext
  rintro ⟨j⟩
  obtain rfl : j = PUnit.unit := Subsingleton.elim _ _
  exact h

end EmptyAndSingleton

section Binary

local notation "U" => CompactlyGenerated.compactlyGeneratedToTop

private abbrev auditPairFamily
    (X Y : CompactlyGenerated.{u, v}) :
    WalkingPair → CompactlyGenerated.{u, v}
  | WalkingPair.left => X
  | WalkingPair.right => Y

private def auditWalkingPairPiEquivProd
    (X Y : CompactlyGenerated.{u, v}) :
    ((TopCat.piFan (fun j : ULift.{v} WalkingPair ↦
      (U).obj ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :
        Type v) ≃
      ↥((U).obj X) × ↥((U).obj Y) where
  toFun f :=
    (show X from f (ULift.up WalkingPair.left),
      show Y from f (ULift.up WalkingPair.right))
  invFun p
    | ⟨WalkingPair.left⟩ => p.1
    | ⟨WalkingPair.right⟩ => p.2
  left_inv f := by
    funext j
    rcases j with ⟨_ | _⟩ <;> rfl
  right_inv p := by
    rcases p with ⟨x, y⟩
    rfl

private def auditWalkingPairPiHomeomorphProd
    (X Y : CompactlyGenerated.{u, v}) :
    ((TopCat.piFan (fun j : ULift.{v} WalkingPair ↦
      (U).obj ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :
        Type v) ≃ₜ
      ↥((U).obj X) × ↥((U).obj Y) where
  toEquiv := @auditWalkingPairPiEquivProd.{u, v} X Y
  continuous_toFun := by
    dsimp only [auditWalkingPairPiEquivProd]
    exact (continuous_apply (ULift.up WalkingPair.left)).prodMk
      (continuous_apply (ULift.up WalkingPair.right))
  continuous_invFun := by
    dsimp only [auditWalkingPairPiEquivProd]
    apply continuous_pi
    intro j
    rcases j with ⟨_ | _⟩
    · exact continuous_fst
    · exact continuous_snd

private noncomputable def auditPairProductIsoTensor
    (X Y : CompactlyGenerated.{u, v}) :
    (∏ᶜ auditPairFamily X Y) ≅ X ⊗ Y := by
  let F : WalkingPair → CompactlyGenerated.{u, v} :=
    auditPairFamily X Y
  let c : Fan F := Fan.mk (X ⊗ Y) (fun j => match j with
    | WalkingPair.left => CartesianMonoidalCategory.fst X Y
    | WalkingPair.right => CartesianMonoidalCategory.snd X Y)
  let hc : IsLimit c := by
    refine
      { lift := fun s => CartesianMonoidalCategory.lift
          (s.π.app ⟨WalkingPair.left⟩)
          (s.π.app ⟨WalkingPair.right⟩)
        fac := ?_
        uniq := ?_ }
    · rintro s ⟨j⟩
      cases j
      · exact CartesianMonoidalCategory.lift_fst _ _
      · exact CartesianMonoidalCategory.lift_snd _ _
    · intro s m hm
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm ⟨WalkingPair.left⟩).trans
          (CartesianMonoidalCategory.lift_fst _ _).symm
      · exact (hm ⟨WalkingPair.right⟩).trans
          (CartesianMonoidalCategory.lift_snd _ _).symm
  exact (limit.isLimit _).conePointUniqueUpToIso hc

@[simp]
private theorem auditPairProductIsoTensor_inv_fst
    (X Y : CompactlyGenerated.{u, v}) :
    (auditPairProductIsoTensor X Y).inv ≫
        Pi.π (auditPairFamily X Y) WalkingPair.left =
      CartesianMonoidalCategory.fst X Y := by
  unfold auditPairProductIsoTensor
  simp

@[simp]
private theorem auditPairProductIsoTensor_inv_snd
    (X Y : CompactlyGenerated.{u, v}) :
    (auditPairProductIsoTensor X Y).inv ≫
        Pi.π (auditPairFamily X Y) WalkingPair.right =
      CartesianMonoidalCategory.snd X Y := by
  unfold auditPairProductIsoTensor
  simp

private noncomputable def auditBinaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥((U).obj X) × ↥((U).obj Y))) ≅ X ⊗ Y :=
  TopCat.toCompactlyGenerated.mapIso
      (TopCat.isoOfHomeo
        (auditWalkingPairPiHomeomorphProd X Y).symm) ≪≫
    (@CompactlyGenerated.piIsoPi.{u, v} (ULift.{v} WalkingPair)
      (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})).symm ≪≫
    Pi.reindex (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0}) (auditPairFamily X Y) ≪≫
    auditPairProductIsoTensor X Y

@[simp]
private theorem auditBinaryKificationIso_hom_fst
    (X Y : CompactlyGenerated.{u, v}) :
    (auditBinaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.fst X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodFst : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
            (U).obj X) ≫
        (asIso (CompactlyGenerated.adj.unit.app X)).inv := by
  let h : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
      (TopCat.piFan (fun j ↦ (U).obj
        ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :=
    (TopCat.isoOfHomeo
      (auditWalkingPairPiHomeomorphProd X Y).symm).hom
  have hRaw : h ≫ (TopCat.piFan (fun j ↦ (U).obj
      ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).π.app
      ⟨ULift.up WalkingPair.left⟩ =
      (TopCat.prodFst : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
        (U).obj X) := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hPair : (auditPairProductIsoTensor X Y).hom ≫
      CartesianMonoidalCategory.fst X Y =
      Pi.π (auditPairFamily X Y) WalkingPair.left := by
    apply (cancel_epi (auditPairProductIsoTensor X Y).inv).1
    simp only [Iso.inv_hom_id_assoc, auditPairProductIsoTensor_inv_fst]
  have hReindex :
      (Pi.reindex (C := CompactlyGenerated.{u, v})
          (Equiv.ulift.{v, 0}) (auditPairFamily X Y)).hom ≫
          Pi.π (auditPairFamily X Y) WalkingPair.left =
        Pi.π (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) := by
    exact Pi.reindex_hom_π (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0}) (auditPairFamily X Y)
      (ULift.up WalkingPair.left)
  have hPi : (CompactlyGenerated.piIsoPi
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})).symm.hom ≫
        Pi.π (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) =
      CompactlyGenerated.piπ
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.left) := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit _)
      (CompactlyGenerated.piFanIsLimit
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0}))
      ⟨ULift.up WalkingPair.left⟩
  simp only [auditBinaryKificationIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [hPair, hReindex]
  calc
    _ = TopCat.toCompactlyGenerated.map h ≫
        CompactlyGenerated.piπ
          (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
            (ULift.up WalkingPair.left) := by
      exact congrArg (fun q ↦ TopCat.toCompactlyGenerated.map h ≫ q) hPi
    _ = _ := by
      unfold CompactlyGenerated.piπ
      rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
      rfl

@[simp]
private theorem auditBinaryKificationIso_hom_snd
    (X Y : CompactlyGenerated.{u, v}) :
    (auditBinaryKificationIso X Y).hom ≫
        CartesianMonoidalCategory.snd X Y =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodSnd : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
            (U).obj Y) ≫
        (asIso (CompactlyGenerated.adj.unit.app Y)).inv := by
  let h : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
      (TopCat.piFan (fun j ↦ (U).obj
        ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).pt :=
    (TopCat.isoOfHomeo
      (auditWalkingPairPiHomeomorphProd X Y).symm).hom
  have hRaw : h ≫ (TopCat.piFan (fun j ↦ (U).obj
      ((auditPairFamily X Y ∘ Equiv.ulift.{v, 0}) j))).π.app
      ⟨ULift.up WalkingPair.right⟩ =
      (TopCat.prodSnd : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶
        (U).obj Y) := by
    apply TopCat.hom_ext
    ext p
    rfl
  have hPair : (auditPairProductIsoTensor X Y).hom ≫
      CartesianMonoidalCategory.snd X Y =
      Pi.π (auditPairFamily X Y) WalkingPair.right := by
    apply (cancel_epi (auditPairProductIsoTensor X Y).inv).1
    simp only [Iso.inv_hom_id_assoc, auditPairProductIsoTensor_inv_snd]
  have hReindex :
      (Pi.reindex (C := CompactlyGenerated.{u, v})
          (Equiv.ulift.{v, 0}) (auditPairFamily X Y)).hom ≫
          Pi.π (auditPairFamily X Y) WalkingPair.right =
        Pi.π (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) := by
    exact Pi.reindex_hom_π (C := CompactlyGenerated.{u, v})
      (Equiv.ulift.{v, 0}) (auditPairFamily X Y)
      (ULift.up WalkingPair.right)
  have hPi : (CompactlyGenerated.piIsoPi
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})).symm.hom ≫
        Pi.π (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) =
      CompactlyGenerated.piπ
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
          (ULift.up WalkingPair.right) := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit _)
      (CompactlyGenerated.piFanIsLimit
        (auditPairFamily X Y ∘ Equiv.ulift.{v, 0}))
      ⟨ULift.up WalkingPair.right⟩
  simp only [auditBinaryKificationIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [hPair, hReindex]
  calc
    _ = TopCat.toCompactlyGenerated.map h ≫
        CompactlyGenerated.piπ
          (auditPairFamily X Y ∘ Equiv.ulift.{v, 0})
            (ULift.up WalkingPair.right) := by
      exact congrArg (fun q ↦ TopCat.toCompactlyGenerated.map h ≫ q) hPi
    _ = _ := by
      unfold CompactlyGenerated.piπ
      rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
      rfl

variable (X Y : CompactlyGenerated.{u, v})

example :
    CompactlyGenerated.compactlyGeneratedToTop.obj (X ⊗ Y) ⟶
      CompactlyGenerated.compactlyGeneratedToTop.obj X ⨯
        CompactlyGenerated.compactlyGeneratedToTop.obj Y :=
  CompactlyGenerated.prodComparisonToTop X Y

example :
    CompactlyGenerated.prodComparisonToTop X Y ≫ Limits.prod.fst =
      CompactlyGenerated.compactlyGeneratedToTop.map
        (CartesianMonoidalCategory.fst X Y) := by
  unfold CompactlyGenerated.prodComparisonToTop
  rw [Limits.prod.lift_fst]

example :
    CompactlyGenerated.prodComparisonToTop X Y ≫ Limits.prod.snd =
      CompactlyGenerated.compactlyGeneratedToTop.map
        (CartesianMonoidalCategory.snd X Y) := by
  unfold CompactlyGenerated.prodComparisonToTop
  rw [Limits.prod.lift_snd]

example :
    (U).map (auditBinaryKificationIso X Y).inv ≫
        CompactlyGenerated.adj.counit.app
          (TopCat.of (↥((U).obj X) × ↥((U).obj Y))) ≫
        (TopCat.prodIsoProd ((U).obj X) ((U).obj Y)).inv =
      CompactlyGenerated.prodComparisonToTop X Y := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc]
    rw [TopCat.prodIsoProd_inv_fst]
    unfold CompactlyGenerated.prodComparisonToTop
    rw [Limits.prod.lift_fst]
    have hCounit : CompactlyGenerated.adj.counit.app ((U).obj X) =
        (U).map
          (asIso (CompactlyGenerated.adj.unit.app X)).inv := by
      apply (cancel_epi ((U).map
        (CompactlyGenerated.adj.unit.app X))).1
      calc
        (U).map (CompactlyGenerated.adj.unit.app X) ≫
            CompactlyGenerated.adj.counit.app ((U).obj X) = 𝟙 _ :=
          CompactlyGenerated.adj.left_triangle_components X
        _ = (U).map (CompactlyGenerated.adj.unit.app X) ≫
            (U).map
              (asIso (CompactlyGenerated.adj.unit.app X)).inv := by
          change 𝟙 _ = (U).map
            ((asIso (CompactlyGenerated.adj.unit.app X)).hom ≫
              (asIso (CompactlyGenerated.adj.unit.app X)).inv)
          rw [Iso.hom_inv_id, (U).map_id]
    have hInv : (auditBinaryKificationIso X Y).inv ≫
        TopCat.toCompactlyGenerated.map
            (TopCat.prodFst : TopCat.of
              (↥((U).obj X) × ↥((U).obj Y)) ⟶ (U).obj X) ≫
          (asIso (CompactlyGenerated.adj.unit.app X)).inv =
        CartesianMonoidalCategory.fst X Y := by
      apply (cancel_epi (auditBinaryKificationIso X Y).hom).1
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        (auditBinaryKificationIso_hom_fst X Y).symm
    let p : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶ (U).obj X :=
      TopCat.prodFst
    calc
      (U).map (auditBinaryKificationIso X Y).inv ≫
          CompactlyGenerated.adj.counit.app
            (TopCat.of (↥((U).obj X) × ↥((U).obj Y))) ≫ p =
        (U).map (auditBinaryKificationIso X Y).inv ≫
          (U).map (TopCat.toCompactlyGenerated.map p) ≫
            CompactlyGenerated.adj.counit.app ((U).obj X) := by
        simpa only [Category.assoc, Functor.id_map,
          Functor.comp_map] using congrArg
          (fun q ↦ (U).map (auditBinaryKificationIso X Y).inv ≫ q)
          (CompactlyGenerated.adj.counit.naturality p).symm
      _ = (U).map (auditBinaryKificationIso X Y).inv ≫
          (U).map (TopCat.toCompactlyGenerated.map p) ≫
            (U).map
              (asIso (CompactlyGenerated.adj.unit.app X)).inv := by
        rw [hCounit]
      _ = (U).map ((auditBinaryKificationIso X Y).inv ≫
          TopCat.toCompactlyGenerated.map p ≫
            (asIso (CompactlyGenerated.adj.unit.app X)).inv) := by
        simp only [(U).map_comp]
      _ = (U).map (CartesianMonoidalCategory.fst X Y) := by
        rw [hInv]
  · simp only [Category.assoc]
    rw [TopCat.prodIsoProd_inv_snd]
    unfold CompactlyGenerated.prodComparisonToTop
    rw [Limits.prod.lift_snd]
    have hCounit : CompactlyGenerated.adj.counit.app ((U).obj Y) =
        (U).map
          (asIso (CompactlyGenerated.adj.unit.app Y)).inv := by
      apply (cancel_epi ((U).map
        (CompactlyGenerated.adj.unit.app Y))).1
      calc
        (U).map (CompactlyGenerated.adj.unit.app Y) ≫
            CompactlyGenerated.adj.counit.app ((U).obj Y) = 𝟙 _ :=
          CompactlyGenerated.adj.left_triangle_components Y
        _ = (U).map (CompactlyGenerated.adj.unit.app Y) ≫
            (U).map
              (asIso (CompactlyGenerated.adj.unit.app Y)).inv := by
          change 𝟙 _ = (U).map
            ((asIso (CompactlyGenerated.adj.unit.app Y)).hom ≫
              (asIso (CompactlyGenerated.adj.unit.app Y)).inv)
          rw [Iso.hom_inv_id, (U).map_id]
    have hInv : (auditBinaryKificationIso X Y).inv ≫
        TopCat.toCompactlyGenerated.map
            (TopCat.prodSnd : TopCat.of
              (↥((U).obj X) × ↥((U).obj Y)) ⟶ (U).obj Y) ≫
          (asIso (CompactlyGenerated.adj.unit.app Y)).inv =
        CartesianMonoidalCategory.snd X Y := by
      apply (cancel_epi (auditBinaryKificationIso X Y).hom).1
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        (auditBinaryKificationIso_hom_snd X Y).symm
    let p : TopCat.of (↥((U).obj X) × ↥((U).obj Y)) ⟶ (U).obj Y :=
      TopCat.prodSnd
    calc
      (U).map (auditBinaryKificationIso X Y).inv ≫
          CompactlyGenerated.adj.counit.app
            (TopCat.of (↥((U).obj X) × ↥((U).obj Y))) ≫ p =
        (U).map (auditBinaryKificationIso X Y).inv ≫
          (U).map (TopCat.toCompactlyGenerated.map p) ≫
            CompactlyGenerated.adj.counit.app ((U).obj Y) := by
        simpa only [Category.assoc, Functor.id_map,
          Functor.comp_map] using congrArg
          (fun q ↦ (U).map (auditBinaryKificationIso X Y).inv ≫ q)
          (CompactlyGenerated.adj.counit.naturality p).symm
      _ = (U).map (auditBinaryKificationIso X Y).inv ≫
          (U).map (TopCat.toCompactlyGenerated.map p) ≫
            (U).map
              (asIso (CompactlyGenerated.adj.unit.app Y)).inv := by
        rw [hCounit]
      _ = (U).map ((auditBinaryKificationIso X Y).inv ≫
          TopCat.toCompactlyGenerated.map p ≫
            (asIso (CompactlyGenerated.adj.unit.app Y)).inv) := by
        simp only [(U).map_comp]
      _ = (U).map (CartesianMonoidalCategory.snd X Y) := by
        rw [hInv]

#guard_msgs (error, substring := true) in
example :
    (U).map (auditBinaryKificationIso X Y).inv =
      CompactlyGenerated.prodComparisonToTop X Y := by
  rfl

end Binary

section Negative

example : True := by
  fail_if_success
    let _ : MonoidalClosed CompactlyGenerated.{u, v} := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.walkingPairPiEquivProd

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.binaryKificationIso

end Negative

#print axioms CompactlyGenerated.piObj
#print axioms CompactlyGenerated.piFanIsLimit
#print axioms CompactlyGenerated.piComparisonToTop_generic_coherence
#print axioms CompactlyGenerated.piComparisonToTop_isHomeomorph_iff
#print axioms CompactlyGenerated.prodComparisonToTop

end MathlibExtTest.CompactlyGenerated.ProductsTests
