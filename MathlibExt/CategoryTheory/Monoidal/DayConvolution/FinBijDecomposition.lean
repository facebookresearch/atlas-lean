/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluationRelabeling
public import MathlibExt.CategoryTheory.Operad.FinBijCard
public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal
public import MathlibExt.CategoryTheory.Operad.FinBijBlockSubgroup
public import MathlibExt.CategoryTheory.Action.FreeActionCopower
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Components of free modules over finite-bijection Day monoids

This file computes the components of a free module over a Day monoid indexed
by the small groupoid of finite sets and bijections.  The scalar/complement
block is first and the free input block is last.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace CategoryTheory.Operad.SmallFinBijGroupoid

universe v u

/-- Every object of the small finite-bijection groupoid is canonically
isomorphic to the skeleton object with the same cardinality. -/
noncomputable def cardIso (i : SmallFinBijGroupoid) :
    card i.of.len ≅ i :=
  Core.isoMk (eqToIso (FintypeCat.Skeleton.ext _ _ rfl))

/-- Ordered block sum of canonical cardinal objects. -/
noncomputable def cardBlockSumIso {r n m : ℕ} (h : r + n = m) :
    card r ⊗ card n ≅ card m :=
  eqToIso (congrArg card h)

/-- Complement-first decompositions of `m` relative to the input `i`. -/
abbrev BlockDecomposition (i m : SmallFinBijGroupoid) :=
  CostructuredArrow (tensorRight i) m

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The diagram assigning a coefficient tensor to each block decomposition. -/
abbrev blockDecompositionDiagram
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    BlockDecomposition i m ⥤ V :=
  CostructuredArrow.proj (tensorRight i) m ⋙
    A.functor ⋙ tensorRight X

/-- The map of block-decomposition diagrams induced by a scalar morphism. -/
def blockDecompositionMap
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) :
    blockDecompositionDiagram A i m X ⟶
      blockDecompositionDiagram A i m Y where
  app d := 𝟙 (A.functor.obj d.left) ⊗ₘ f
  naturality {d e} g := by
    dsimp [blockDecompositionDiagram]
    simpa only [id_tensorHom] using
      (whisker_exchange (A.functor.map g.left) f).symm

/-- The complement-first decomposition colimit, functorial in the input
object. -/
noncomputable def dayFreeAtComponentFunctor
    [HasColimitsOfSize.{0, 0} V]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) : V ⥤ V where
  obj X := colimit (blockDecompositionDiagram A i m X)
  map f := colim.map (blockDecompositionMap A i m f)
  map_id X := by
    apply colimit.hom_ext
    intro d
    simp [blockDecompositionMap]
  map_comp f g := by
    apply colimit.hom_ext
    intro d
    simp [blockDecompositionMap]

/-- The Day diagram obtained from the free diagram at a selected finite-bijection index. -/
abbrev dayFreeDiagram
    [HasColimitsOfSize.{0, 0} V]
    (i : SmallFinBijGroupoid) (X : V) :
    DayFunctor SmallFinBijGroupoid V :=
  (DayFunctor.equiv SmallFinBijGroupoid V).symm.functor.obj
    ((evaluationLeftAdjoint V i).obj X)

/-- The diagram computing one component of a Day tensor with a free diagram. -/
abbrev dayTensorComponentDiagram
    [HasColimitsOfSize.{0, 0} V]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    CostructuredArrow (tensor SmallFinBijGroupoid) m ⥤ V :=
  CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙
    (A.functor ⊠ (dayFreeDiagram i X).functor)

/-- The block decomposition obtained by absorbing a selected coordinate bijection. -/
abbrev collapsedDecomposition
    (i m : SmallFinBijGroupoid)
    (d : CostructuredArrow (tensor SmallFinBijGroupoid) m)
    (β : i ⟶ d.left.2) : BlockDecomposition i m :=
  CostructuredArrow.mk ((d.left.1 ◁ β) ≫ d.hom)

/-- The cocone collapsing the Day free tensor to complement-first block decompositions. -/
noncomputable abbrev dayTensorCollapseCocone
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    Cocone (dayTensorComponentDiagram A i m X) where
  pt := colimit (blockDecompositionDiagram A i m X)
  ι :=
    { app := fun d =>
        (PreservesCoproduct.iso (tensorLeft (A.functor.obj d.left.1))
            (fun _ : i ⟶ d.left.2 => X)).hom ≫
          Sigma.desc (fun β =>
            colimit.ι (blockDecompositionDiagram A i m X)
              (collapsedDecomposition i m d β))
      naturality := by
        intro d e g
        apply (cancel_epi
          (PreservesCoproduct.iso
            (tensorLeft (A.functor.obj d.left.1))
            (fun _ : i ⟶ d.left.2 => X)).inv).1
        apply Sigma.hom_ext
        intro β
        dsimp [dayTensorComponentDiagram, dayFreeDiagram,
          DayFunctor.equiv, evaluationLeftAdjoint, blockDecompositionDiagram,
          dayFreeAtComponentFunctor]
        simp only [Category.comp_id]
        rw [← Category.assoc]
        have hσ :
            Sigma.ι (fun _ : i ⟶ d.left.2 =>
              A.functor.obj d.left.1 ⊗ X) β ≫
                sigmaComparison (tensorLeft (A.functor.obj d.left.1))
                  (fun _ : i ⟶ d.left.2 => X) =
              (tensorLeft (A.functor.obj d.left.1)).map
                (Sigma.ι (fun _ : i ⟶ d.left.2 => X) β) := by
          change
            Sigma.ι (fun _ : i ⟶ d.left.2 =>
              (tensorLeft (A.functor.obj d.left.1)).obj X) β ≫
                sigmaComparison (tensorLeft (A.functor.obj d.left.1))
                  (fun _ : i ⟶ d.left.2 => X) = _
          exact ι_comp_sigmaComparison
            (tensorLeft (A.functor.obj d.left.1))
            (fun _ : i ⟶ d.left.2 => X) β
        rw [hσ]
        rw [show
          (tensorLeft (A.functor.obj d.left.1)).map
              (Sigma.ι (fun _ : i ⟶ d.left.2 => X) β) =
            A.functor.obj d.left.1 ◁
              Sigma.ι (fun _ : i ⟶ d.left.2 => X) β from rfl]
        simp only [Category.assoc]
        rw [whisker_exchange_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [Sigma.ι_comp_desc]
        have hpres :
            A.functor.obj e.left.1 ◁
                Sigma.ι (fun _ : i ⟶ e.left.2 => X)
                  (β ≫ g.left.2) ≫
              (PreservesCoproduct.iso
                (tensorLeft (A.functor.obj e.left.1))
                (fun _ : i ⟶ e.left.2 => X)).hom =
            Sigma.ι (fun _ : i ⟶ e.left.2 =>
              A.functor.obj e.left.1 ⊗ X) (β ≫ g.left.2) := by
          have hσe :
              Sigma.ι (fun _ : i ⟶ e.left.2 =>
                A.functor.obj e.left.1 ⊗ X) (β ≫ g.left.2) ≫
                  sigmaComparison (tensorLeft (A.functor.obj e.left.1))
                    (fun _ : i ⟶ e.left.2 => X) =
                (tensorLeft (A.functor.obj e.left.1)).map
                  (Sigma.ι (fun _ : i ⟶ e.left.2 => X)
                    (β ≫ g.left.2)) := by
            change
              Sigma.ι (fun _ : i ⟶ e.left.2 =>
                (tensorLeft (A.functor.obj e.left.1)).obj X)
                  (β ≫ g.left.2) ≫
                    sigmaComparison (tensorLeft (A.functor.obj e.left.1))
                      (fun _ : i ⟶ e.left.2 => X) = _
            exact ι_comp_sigmaComparison
              (tensorLeft (A.functor.obj e.left.1))
              (fun _ : i ⟶ e.left.2 => X) (β ≫ g.left.2)
          apply (cancel_mono
            (PreservesCoproduct.iso
              (tensorLeft (A.functor.obj e.left.1))
              (fun _ : i ⟶ e.left.2 => X)).inv).1
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
          rw [PreservesCoproduct.inv_hom, hσe]
          rfl
        have hpres_assoc {Z : V}
            (k : (∐ fun _ : i ⟶ e.left.2 =>
              A.functor.obj e.left.1 ⊗ X) ⟶ Z) :
            A.functor.obj e.left.1 ◁
                Sigma.ι (fun _ : i ⟶ e.left.2 => X)
                  (β ≫ g.left.2) ≫
              (PreservesCoproduct.iso
                (tensorLeft (A.functor.obj e.left.1))
                (fun _ : i ⟶ e.left.2 => X)).hom ≫ k =
            Sigma.ι (fun _ : i ⟶ e.left.2 =>
              A.functor.obj e.left.1 ⊗ X) (β ≫ g.left.2) ≫ k := by
          rw [← Category.assoc, hpres]
        rw [hpres_assoc]
        rw [Sigma.ι_comp_desc]
        rw [← PreservesCoproduct.inv_hom]
        simp only [Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]
        let collapsedMap :
            collapsedDecomposition i m d β ⟶
              collapsedDecomposition i m e (β ≫ g.left.2) :=
          CostructuredArrow.homMk g.left.1 (by
            dsimp [collapsedDecomposition]
            rw [MonoidalCategory.whiskerLeft_comp]
            rw [Category.assoc, ← whisker_exchange_assoc]
            rw [← tensorHom_def_assoc]
            rw [← Category.assoc]
            change d.left.1 ◁ β ≫
              ((tensor SmallFinBijGroupoid).map g.left ≫ e.hom) = _
            rw [CostructuredArrow.w g])
        simpa [blockDecompositionDiagram, collapsedMap] using
          (colimit.w (blockDecompositionDiagram A i m X) collapsedMap) }

/-- The forward component map from the Day tensor of a free diagram. -/
noncomputable def dayFreeAtComponentForward
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorRight W)]
    (A : DayFunctor SmallFinBijGroupoid V) [MonObj A]
    (i m : SmallFinBijGroupoid) (X : V) :
    ((Mod.dayFreeAt A i).obj X).X.functor.obj m ⟶
      (dayFreeAtComponentFunctor A i m).obj X :=
  let G := dayFreeDiagram i X
  let hDay : (Functor.LeftExtension.mk (A ⊗ G).functor
      (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V)
      (D := DayFunctor SmallFinBijGroupoid V) A G m
  let eFree :=
    ((DayFunctor.equiv SmallFinBijGroupoid V).functor.mapIso
      (eqToIso (Mod.free_obj A G))).app m
  eFree.hom ≫
    hDay.isoColimit.hom ≫
    colimit.desc (dayTensorComponentDiagram A i m X)
      (dayTensorCollapseCocone A i m X)

/-- The block cocone using the original identity free generator in the Day tensor colimit. -/
noncomputable abbrev dayFreeAtComponentBackward
    [HasColimitsOfSize.{0, 0} V]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    Cocone (blockDecompositionDiagram A i m X) :=
  let G := dayFreeDiagram i X
  let D := dayTensorComponentDiagram A i m X
  let rawObj (d : BlockDecomposition i m) :
      CostructuredArrow (tensor SmallFinBijGroupoid) m :=
    CostructuredArrow.mk (Y := (d.left, i)) d.hom
  let leg (d : BlockDecomposition i m) :
      (blockDecompositionDiagram A i m X).obj d ⟶ colimit D :=
    (𝟙 (A.functor.obj d.left) ⊗ₘ
        Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)) ≫
      colimit.ι D (rawObj d)
  { pt := colimit D
    ι :=
      { app := leg
        naturality := by
            intro d e g
            let rawMap : rawObj d ⟶ rawObj e :=
              CostructuredArrow.homMk (g.left, 𝟙 i) (by
                change (tensorRight i).map g.left ≫ e.hom = d.hom
                exact CostructuredArrow.w g)
            let jd : A.functor.obj d.left ⊗ X ⟶ D.obj (rawObj d) :=
              𝟙 (A.functor.obj d.left) ⊗ₘ
                Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
            let je : A.functor.obj e.left ⊗ X ⟶ D.obj (rawObj e) :=
              𝟙 (A.functor.obj e.left) ⊗ₘ
                Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
            have hj :
                (blockDecompositionDiagram A i m X).map g ≫ je =
                  jd ≫ D.map rawMap := by
              dsimp [blockDecompositionDiagram, D, rawObj, rawMap,
                dayTensorComponentDiagram]
              simp only [Functor.map_id]
              dsimp [jd, je, G, dayFreeDiagram, DayFunctor.equiv,
                evaluationLeftAdjoint]
              simp only [id_tensorHom, MonoidalCategory.whiskerLeft_id,
                Category.comp_id]
              exact (whisker_exchange (A.functor.map g.left)
                (Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i))).symm
            have hnat :
                (blockDecompositionDiagram A i m X).map g ≫ leg e =
                  leg d := by
              change
                (blockDecompositionDiagram A i m X).map g ≫ je ≫
                    colimit.ι D (rawObj e) =
                  jd ≫ colimit.ι D (rawObj d)
              rw [← Category.assoc, hj, Category.assoc]
              rw [colimit.w D rawMap]
            rw [Functor.const_obj_map]
            exact hnat.trans (Category.comp_id _).symm } }

theorem dayFreeAtComponentBackward_forward
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    colimit.desc (blockDecompositionDiagram A i m X)
        (dayFreeAtComponentBackward A i m X) ≫
      colimit.desc (dayTensorComponentDiagram A i m X)
        (dayTensorCollapseCocone A i m X) =
      𝟙 ((dayFreeAtComponentFunctor A i m).obj X) := by
  apply colimit.hom_ext
  intro d
  rw [colimit.ι_desc_assoc]
  let D := dayTensorComponentDiagram A i m X
  let rawObj : CostructuredArrow (tensor SmallFinBijGroupoid) m :=
    CostructuredArrow.mk (Y := (d.left, i)) d.hom
  let jd : (blockDecompositionDiagram A i m X).obj d ⟶ D.obj rawObj :=
    𝟙 (A.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  have happ :
      (dayFreeAtComponentBackward A i m X).ι.app d =
        jd ≫ colimit.ι D rawObj := rfl
  rw [happ, Category.assoc, colimit.ι_desc]
  let collapseLeg : D.obj rawObj ⟶
      (dayFreeAtComponentFunctor A i m).obj X :=
    (PreservesCoproduct.iso (tensorLeft (A.functor.obj d.left))
        (fun _ : i ⟶ i => X)).hom ≫
      Sigma.desc (fun β =>
        colimit.ι (blockDecompositionDiagram A i m X)
          (collapsedDecomposition i m rawObj β))
  have hcapp :
      (dayTensorCollapseCocone A i m X).ι.app rawObj =
        collapseLeg := rfl
  rw [hcapp]
  dsimp [D, rawObj, dayTensorComponentDiagram, dayFreeDiagram,
    DayFunctor.equiv, evaluationLeftAdjoint,
    dayFreeAtComponentFunctor] at jd collapseLeg
  have hσ :
      Sigma.ι (fun _ : i ⟶ i => A.functor.obj d.left ⊗ X) (𝟙 i) ≫
          sigmaComparison (tensorLeft (A.functor.obj d.left))
            (fun _ : i ⟶ i => X) =
        (tensorLeft (A.functor.obj d.left)).map
          (Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)) := by
    change
      Sigma.ι (fun _ : i ⟶ i =>
        (tensorLeft (A.functor.obj d.left)).obj X) (𝟙 i) ≫
          sigmaComparison (tensorLeft (A.functor.obj d.left))
            (fun _ : i ⟶ i => X) = _
    exact ι_comp_sigmaComparison
      (tensorLeft (A.functor.obj d.left))
      (fun _ : i ⟶ i => X) (𝟙 i)
  have hpres :
      jd ≫
          (PreservesCoproduct.iso (tensorLeft (A.functor.obj d.left))
            (fun _ : i ⟶ i => X)).hom =
        Sigma.ι (fun _ : i ⟶ i => A.functor.obj d.left ⊗ X)
          (𝟙 i) := by
    apply (cancel_mono
      (PreservesCoproduct.iso (tensorLeft (A.functor.obj d.left))
        (fun _ : i ⟶ i => X)).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom, hσ]
    change
      (𝟙 (A.functor.obj d.left) ⊗ₘ
          Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)) =
        A.functor.obj d.left ◁
          Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
    exact id_tensorHom _ _
  have hcalc :
      jd ≫ collapseLeg =
        colimit.ι (blockDecompositionDiagram A i m X)
          (collapsedDecomposition i m rawObj (𝟙 i)) := by
    have hc := congrArg
      (fun q => q ≫ Sigma.desc (fun β =>
        colimit.ι (blockDecompositionDiagram A i m X)
          (collapsedDecomposition i m rawObj β))) hpres
    simp only [Category.assoc, Sigma.ι_comp_desc] at hc
    convert hc using 1
    rfl
  let idMap : collapsedDecomposition i m rawObj (𝟙 i) ⟶ d :=
    CostructuredArrow.homMk (𝟙 d.left) (by
      dsimp [collapsedDecomposition, rawObj]
      simp)
  have hid := colimit.w (blockDecompositionDiagram A i m X) idMap
  have hid' :
      colimit.ι (blockDecompositionDiagram A i m X)
          (collapsedDecomposition i m rawObj (𝟙 i)) =
        colimit.ι (blockDecompositionDiagram A i m X) d := by
    have hmap :
        A.functor.map (𝟙 d.left) ▷ X =
          𝟙 (A.functor.obj d.left ⊗ X) := by simp
    dsimp [blockDecompositionDiagram, idMap] at hid
    rw [hmap] at hid
    exact hid.symm.trans (Category.id_comp _)
  exact hcalc.trans (hid'.trans (Category.comp_id _).symm)

theorem dayFreeAtComponentForward_backward
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    colimit.desc (dayTensorComponentDiagram A i m X)
        (dayTensorCollapseCocone A i m X) ≫
      colimit.desc (blockDecompositionDiagram A i m X)
        (dayFreeAtComponentBackward A i m X) =
      𝟙 (colimit (dayTensorComponentDiagram A i m X)) := by
  apply colimit.hom_ext
  intro q
  rw [colimit.ι_desc_assoc]
  let D := dayTensorComponentDiagram A i m X
  let B := blockDecompositionDiagram A i m X
  let P := PreservesCoproduct.iso
    (tensorLeft (A.functor.obj q.left.1))
    (fun _ : i ⟶ q.left.2 => X)
  let collapseLeg : D.obj q ⟶ colimit B :=
    P.hom ≫ Sigma.desc (fun β =>
      colimit.ι B (collapsedDecomposition i m q β))
  have hcapp :
      (dayTensorCollapseCocone A i m X).ι.app q =
        collapseLeg := rfl
  rw [hcapp]
  let Pinv : (∐ fun _ : i ⟶ q.left.2 =>
      (tensorLeft (A.functor.obj q.left.1)).obj X) ⟶ D.obj q := P.inv
  have hmain :
      collapseLeg ≫ colimit.desc B
          (dayFreeAtComponentBackward A i m X) =
        colimit.ι D q := by
    let _ : IsIso Pinv := by
      dsimp [Pinv]
      exact P.isIso_inv
    apply (cancel_epi Pinv).1
    apply Sigma.hom_ext
    intro β
    have hcollapse : collapseLeg =
        P.hom ≫ Sigma.desc (fun beta =>
          colimit.ι B (collapsedDecomposition i m q beta)) := rfl
    have hpc :
        Pinv ≫ collapseLeg =
          Sigma.desc (fun beta =>
            colimit.ι B (collapsedDecomposition i m q beta)) := by
      rw [hcollapse]
      exact Iso.inv_hom_id_assoc P _
    have hright :
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
            (tensorLeft (A.functor.obj q.left.1)).obj X) β ≫ Pinv =
          (tensorLeft (A.functor.obj q.left.1)).map
            (Sigma.ι (fun _ : i ⟶ q.left.2 => X) β) := by
      change _ ≫ P.inv = _
      rw [PreservesCoproduct.inv_hom]
      exact ι_comp_sigmaComparison
        (tensorLeft (A.functor.obj q.left.1))
        (fun _ : i ⟶ q.left.2 => X) β
    have hpc_assoc :
        Pinv ≫ collapseLeg ≫
            colimit.desc B (dayFreeAtComponentBackward A i m X) =
          Sigma.desc (fun beta =>
              colimit.ι B (collapsedDecomposition i m q beta)) ≫
            colimit.desc B (dayFreeAtComponentBackward A i m X) := by
      rw [← Category.assoc, hpc]
    have hright_assoc :
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
            (tensorLeft (A.functor.obj q.left.1)).obj X) β ≫
            Pinv ≫ colimit.ι D q =
          (tensorLeft (A.functor.obj q.left.1)).map
              (Sigma.ι (fun _ : i ⟶ q.left.2 => X) β) ≫
            colimit.ι D q := by
      rw [← Category.assoc, hright]
      rfl
    rw [hpc_assoc]
    rw [Sigma.ι_comp_desc_assoc, colimit.ι_desc]
    rw [hright_assoc]
    let b := collapsedDecomposition i m q β
    let sec : CostructuredArrow (tensor SmallFinBijGroupoid) m :=
      CostructuredArrow.mk (Y := (b.left, i)) b.hom
    let jsec : B.obj b ⟶ D.obj sec :=
      𝟙 (A.functor.obj b.left) ⊗ₘ
        Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
    let rawMap : sec ⟶ q :=
      CostructuredArrow.homMk (𝟙 q.left.1, β) (by
        dsimp [sec, b, collapsedDecomposition]
        simp)
    have happ :
        (dayFreeAtComponentBackward A i m X).ι.app b =
          jsec ≫ colimit.ι D sec := rfl
    have hj :
        jsec ≫ D.map rawMap =
          (tensorLeft (A.functor.obj q.left.1)).map
            (Sigma.ι (fun _ : i ⟶ q.left.2 => X) β) := by
      dsimp [jsec, D, rawMap, sec, b, dayTensorComponentDiagram,
        dayFreeDiagram, DayFunctor.equiv, evaluationLeftAdjoint,
        collapsedDecomposition]
      simp only [id_tensorHom, Functor.map_id, id_whiskerRight, Category.id_comp]
      rw [← MonoidalCategory.whiskerLeft_comp]
      simp
    rw [happ]
    have hw := colimit.w D rawMap
    calc
      jsec ≫ colimit.ι D sec =
          jsec ≫ (D.map rawMap ≫ colimit.ι D q) := by rw [hw]
      _ = (jsec ≫ D.map rawMap) ≫ colimit.ι D q :=
        (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hj]
        rfl
  exact hmain.trans (Category.comp_id _).symm

theorem dayIsoColimit_naturality
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorRight W)]
    (A : DayFunctor SmallFinBijGroupoid V)
    (m : SmallFinBijGroupoid)
    {G H : DayFunctor SmallFinBijGroupoid V} (g : G ⟶ H)
    (dmap :
      (CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙
          (A.functor ⊠ G.functor)) ⟶
        (CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙
          (A.functor ⊠ H.functor)))
    (hdmap : ∀ q, dmap.app q =
      𝟙 (A.functor.obj q.left.1) ⊗ₘ g.natTrans.app q.left.2) :
    (A ◁ g).natTrans.app m ≫ (
      LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
          (C := SmallFinBijGroupoid) (V := V)
          (D := DayFunctor SmallFinBijGroupoid V) A H m).isoColimit.hom = (
      LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
          (C := SmallFinBijGroupoid) (V := V)
          (D := DayFunctor SmallFinBijGroupoid V) A G m).isoColimit.hom ≫
        colim.map dmap := by
  let hG : (Functor.LeftExtension.mk (A ⊗ G).functor
      (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V)
      (D := DayFunctor SmallFinBijGroupoid V) A G m
  let hH : (Functor.LeftExtension.mk (A ⊗ H).functor
      (DayFunctor.η A H)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V)
      (D := DayFunctor SmallFinBijGroupoid V) A H m
  apply hG.hom_ext'
  intro Z φ
  let q : CostructuredArrow (tensor SmallFinBijGroupoid) m :=
    CostructuredArrow.mk (Y := Z) φ
  change
    (DayFunctor.η A G).app Z ≫ (A ⊗ G).functor.map φ ≫
        (A ◁ g).natTrans.app m ≫ hH.isoColimit.hom =
      (DayFunctor.η A G).app Z ≫ (A ⊗ G).functor.map φ ≫
        hG.isoColimit.hom ≫ colim.map dmap
  rw [(A ◁ g).natTrans.naturality_assoc]
  have hη :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      V A g Z.1 Z.2
  change
    (DayFunctor.η A G).app Z ≫
        (A ◁ g).natTrans.app ((tensor SmallFinBijGroupoid).obj Z) =
      (A.functor.obj Z.1 ◁ g.natTrans.app Z.2) ≫
        (DayFunctor.η A H).app Z at hη
  rw [← Category.assoc, hη, Category.assoc]
  have hHι := hH.ι_isoColimit_hom q
  have hGι := hG.ι_isoColimit_hom q
  change
    (DayFunctor.η A H).app Z ≫ (A ⊗ H).functor.map φ ≫
      hH.isoColimit.hom =
        colimit.ι (CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙
          (A.functor ⊠ H.functor)) q at hHι
  change
    (DayFunctor.η A G).app Z ≫ (A ⊗ G).functor.map φ ≫
      hG.isoColimit.hom =
        colimit.ι (CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙
          (A.functor ⊠ G.functor)) q at hGι
  rw [hHι]
  have hGassoc := congrArg (fun k => k ≫ colim.map dmap) hGι
  simp only [Category.assoc] at hGassoc
  rw [hGassoc]
  have hw := (ι_colimMap dmap q).symm
  rw [hdmap q] at hw
  simpa [q, id_tensorHom] using hw

private theorem dayFreeAtComponentForward_naturality
    [HasColimitsOfSize.{0, 0} V]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    [∀ W : V, PreservesColimitsOfSize.{0, 0} (tensorRight W)]
    (A : DayFunctor SmallFinBijGroupoid V) [MonObj A]
    (i m : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) :
    (Mod.dayEvaluation A m).map ((Mod.dayFreeAt A i).map f) ≫
        dayFreeAtComponentForward A i m Y =
      dayFreeAtComponentForward A i m X ≫
        (dayFreeAtComponentFunctor A i m).map f := by
  let GX := dayFreeDiagram i X
  let GY := dayFreeDiagram i Y
  let g : GX ⟶ GY :=
    (DayFunctor.equiv SmallFinBijGroupoid V).symm.functor.map
      ((evaluationLeftAdjoint V i).map f)
  let eX := ((DayFunctor.equiv SmallFinBijGroupoid V).functor.mapIso
    (eqToIso (Mod.free_obj A GX))).app m
  let eY := ((DayFunctor.equiv SmallFinBijGroupoid V).functor.mapIso
    (eqToIso (Mod.free_obj A GY))).app m
  let eXhom : ((Mod.free A).obj GX).X.functor.obj m ⟶
      (A ⊗ GX).functor.obj m :=
    eX.hom
  let eXinv : (A ⊗ GX).functor.obj m ⟶
      ((Mod.free A).obj GX).X.functor.obj m :=
    eX.inv
  let eYhom : ((Mod.free A).obj GY).X.functor.obj m ⟶
      (A ⊗ GY).functor.obj m :=
    eY.hom
  let smap : ((Mod.free A).obj GX).X.functor.obj m ⟶
      ((Mod.free A).obj GY).X.functor.obj m :=
    (Mod.dayEvaluation A m).map ((Mod.dayFreeAt A i).map f)
  let DX := dayTensorComponentDiagram A i m X
  let DY := dayTensorComponentDiagram A i m Y
  let BX := blockDecompositionDiagram A i m X
  let BY := blockDecompositionDiagram A i m Y
  let hDayX : (Functor.LeftExtension.mk (A ⊗ GX).functor
      (DayFunctor.η A GX)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V)
      (D := DayFunctor SmallFinBijGroupoid V) A GX m
  let hDayY : (Functor.LeftExtension.mk (A ⊗ GY).functor
      (DayFunctor.η A GY)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V)
      (D := DayFunctor SmallFinBijGroupoid V) A GY m
  let cX : colimit DX ⟶ colimit BX :=
    colimit.desc DX (dayTensorCollapseCocone A i m X)
  let cY : colimit DY ⟶ colimit BY :=
    colimit.desc DY (dayTensorCollapseCocone A i m Y)
  let bmap : colimit BX ⟶ colimit BY :=
    colim.map (blockDecompositionMap A i m f)
  have hFX : dayFreeAtComponentForward A i m X =
      eXhom ≫ hDayX.isoColimit.hom ≫ cX := rfl
  have hFY : dayFreeAtComponentForward A i m Y =
      eYhom ≫ hDayY.isoColimit.hom ≫ cY := rfl
  rw [hFX, hFY]
  have hsmap :
      (Mod.dayEvaluation A m).map ((Mod.dayFreeAt A i).map f) =
        smap := rfl
  rw [hsmap]
  have hbmap : (dayFreeAtComponentFunctor A i m).map f = bmap := rfl
  rw [hbmap]
  change smap ≫ eYhom ≫ hDayY.isoColimit.hom ≫ cY =
    (eXhom ≫ hDayX.isoColimit.hom ≫ cX) ≫ bmap
  have hfreeDay := Mod.free_map A g
  have hsDay :
      eqToHom (Mod.free_obj A GX).symm ≫
          ((Mod.free A).map g).hom ≫
          eqToHom (Mod.free_obj A GY) =
        A ◁ g := by
    rw [← hfreeDay, ← Category.assoc]
    simp
  have hsmapfree :
      smap = ((Mod.free A).map g).hom.natTrans.app m := by
    have heq := DayFunctor.equiv_functor_map SmallFinBijGroupoid V
      (((Mod.free A).map g).hom)
    exact congrArg (fun k => k.app m) heq
  have hs :
      eXinv ≫ smap ≫ eYhom =
        (A ◁ g).natTrans.app m := by
    rw [hsmapfree]
    have hc := congrArg (fun k => k.natTrans.app m) hsDay
    dsimp [eXinv, eYhom] at hc ⊢
    convert hc using 1
    rfl
  have heX : eXinv ≫ eXhom = 𝟙 ((A ⊗ GX).functor.obj m) :=
    eX.inv_hom_id
  have heX' : eXhom ≫ eXinv =
      𝟙 (((Mod.free A).obj GX).X.functor.obj m) := eX.hom_inv_id
  let _ : IsIso eXinv := eX.isIso_inv
  apply (cancel_epi eXinv).1
  have hleft :
      (eXinv ≫ smap ≫ eYhom) ≫
          hDayY.isoColimit.hom ≫ cY =
        (A ◁ g).natTrans.app m ≫ hDayY.isoColimit.hom ≫ cY := by
    exact congrArg (fun q => q ≫ hDayY.isoColimit.hom ≫ cY) hs
  have hbaseRight :
      eXinv ≫ (eXhom ≫ hDayX.isoColimit.hom ≫ cX) =
        hDayX.isoColimit.hom ≫ cX := by
    rw [← Category.assoc, heX, Category.id_comp]
  have hright :
      (eXinv ≫ (eXhom ≫ hDayX.isoColimit.hom ≫ cX)) ≫ bmap =
        (hDayX.isoColimit.hom ≫ cX) ≫ bmap := by
    exact congrArg (fun q => q ≫ bmap) hbaseRight
  let dg : DX ⟶ DY :=
    { app := fun q =>
        𝟙 (A.functor.obj q.left.1) ⊗ₘ g.natTrans.app q.left.2
      naturality := by
        intro q r h
        dsimp [DX, DY, dayTensorComponentDiagram]
        simp only [id_tensorHom, Category.assoc]
        rw [← MonoidalCategory.whiskerLeft_comp]
        rw [g.natTrans.naturality]
        rw [MonoidalCategory.whiskerLeft_comp]
        rw [← whisker_exchange_assoc] }
  let dmap : colimit DX ⟶ colimit DY := colim.map dg
  have hDayNat :
      (A ◁ g).natTrans.app m ≫ hDayY.isoColimit.hom =
        hDayX.isoColimit.hom ≫ dmap := by
    exact dayIsoColimit_naturality A m g dg (fun q => rfl)
  have hCollapseNat : dmap ≫ cY = cX ≫ bmap := by
    apply colimit.hom_ext
    intro q
    have hw :
        colimit.ι DX q ≫ colim.map dg ≫ cY =
          dg.app q ≫ colimit.ι DY q ≫ cY :=
      ι_colimMap_assoc dg q cY
    rw [show dmap = colim.map dg from rfl, hw]
    dsimp [cX, cY]
    rw [colimit.ι_desc, colimit.ι_desc_assoc]
    let PX := PreservesCoproduct.iso
      (tensorLeft (A.functor.obj q.left.1))
      (fun _ : i ⟶ q.left.2 => X)
    let PY := PreservesCoproduct.iso
      (tensorLeft (A.functor.obj q.left.1))
      (fun _ : i ⟶ q.left.2 => Y)
    let lX : (tensorLeft (A.functor.obj q.left.1)).obj
          (∐ fun _ : i ⟶ q.left.2 => X) ⟶ colimit BX :=
      PX.hom ≫ Sigma.desc (fun β =>
        colimit.ι BX (collapsedDecomposition i m q β))
    let lY : (tensorLeft (A.functor.obj q.left.1)).obj
          (∐ fun _ : i ⟶ q.left.2 => Y) ⟶ colimit BY :=
      PY.hom ≫ Sigma.desc (fun β =>
        colimit.ι BY (collapsedDecomposition i m q β))
    have hlX : (dayTensorCollapseCocone A i m X).ι.app q = lX := rfl
    have hlY : (dayTensorCollapseCocone A i m Y).ι.app q = lY := rfl
    rw [hlX, hlY]
    let PXinv : (∐ fun _ : i ⟶ q.left.2 =>
        (tensorLeft (A.functor.obj q.left.1)).obj X) ⟶
          (tensorLeft (A.functor.obj q.left.1)).obj
            (∐ fun _ : i ⟶ q.left.2 => X) := PX.inv
    let _ : IsIso PXinv := PX.isIso_inv
    apply (cancel_epi PXinv).1
    apply Sigma.hom_ext
    intro β
    let a := A.functor.obj q.left.1
    let b := collapsedDecomposition i m q β
    have hPX :
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
            (tensorLeft a).obj X) β ≫ PXinv =
          (tensorLeft a).map
            (Sigma.ι (fun _ : i ⟶ q.left.2 => X) β) := by
      change _ ≫ PX.inv = _
      rw [PreservesCoproduct.inv_hom]
      exact ι_comp_sigmaComparison (tensorLeft a)
        (fun _ : i ⟶ q.left.2 => X) β
    let gq : (∐ fun _ : i ⟶ q.left.2 => X) ⟶
        (∐ fun _ : i ⟶ q.left.2 => Y) :=
      Sigma.desc (fun beta =>
        f ≫ Sigma.ι (fun _ : i ⟶ q.left.2 => Y) beta)
    have hgq : g.natTrans.app q.left.2 = gq := by
      dsimp [g, GX, GY, gq, dayFreeDiagram, DayFunctor.equiv,
        evaluationLeftAdjoint]
    have hgβ :
        Sigma.ι (fun _ : i ⟶ q.left.2 => X) β ≫
            gq =
          f ≫ Sigma.ι (fun _ : i ⟶ q.left.2 => Y) β := by
      dsimp [gq]
      rw [Sigma.ι_comp_desc]
    have hPY :
        (tensorLeft a).map
              (Sigma.ι (fun _ : i ⟶ q.left.2 => Y) β) ≫
            PY.hom =
          Sigma.ι (fun _ : i ⟶ q.left.2 => a ⊗ Y) β := by
      apply (cancel_mono PY.inv).1
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [PreservesCoproduct.inv_hom]
      exact (ι_comp_sigmaComparison (tensorLeft a)
        (fun _ : i ⟶ q.left.2 => Y) β).symm
    have hpcX :
        PXinv ≫ lX =
          Sigma.desc (fun beta =>
            colimit.ι BX (collapsedDecomposition i m q beta)) := by
      dsimp [lX]
      change PX.inv ≫ PX.hom ≫ _ = _
      rw [Iso.inv_hom_id_assoc]
      rfl
    let dgq : (tensorLeft a).obj (∐ fun _ : i ⟶ q.left.2 => X) ⟶
        (tensorLeft a).obj (∐ fun _ : i ⟶ q.left.2 => Y) :=
      𝟙 a ⊗ₘ gq
    have hdgq : dg.app q = dgq := by
      dsimp [dg, dgq, a]
      rw [hgq]
      rfl
    let descY := Sigma.desc (fun beta =>
      colimit.ι BY (collapsedDecomposition i m q beta))
    have hPYassoc :
        (a ◁ Sigma.ι (fun _ : i ⟶ q.left.2 => Y) β) ≫
            PY.hom ≫ descY =
          Sigma.ι (fun _ : i ⟶ q.left.2 => a ⊗ Y) β ≫
            descY := by
      change
        (tensorLeft a).map
              (Sigma.ι (fun _ : i ⟶ q.left.2 => Y) β) ≫
            PY.hom ≫ descY = _
      simpa only [Category.assoc] using congrArg (fun k => k ≫ descY) hPY
    have hL :
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
              (tensorLeft a).obj X) β ≫ PXinv ≫ dgq ≫ lY =
          (a ◁ f) ≫ colimit.ι BY b := by
      rw [← Category.assoc, hPX]
      dsimp [dgq]
      simp only [id_tensorHom]
      dsimp [lY]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, hgβ,
        MonoidalCategory.whiskerLeft_comp_assoc]
      change
        (a ◁ f) ≫
            ((a ◁ Sigma.ι (fun _ : i ⟶ q.left.2 => Y) β) ≫
              PY.hom ≫ descY) = _
      rw [hPYassoc]
      dsimp [descY, b]
      rw [Sigma.ι_comp_desc]
    have hpcXassoc :
        PXinv ≫ lX ≫ bmap =
          Sigma.desc (fun beta =>
              colimit.ι BX (collapsedDecomposition i m q beta)) ≫
            bmap := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ bmap) hpcX
    have hR :
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
              (tensorLeft a).obj X) β ≫ PXinv ≫ lX ≫ bmap =
          (a ◁ f) ≫ colimit.ι BY b := by
      have hstart := congrArg
        (fun k => Sigma.ι (fun _ : i ⟶ q.left.2 =>
          (tensorLeft a).obj X) β ≫ k) hpcXassoc
      calc
        Sigma.ι (fun _ : i ⟶ q.left.2 =>
              (tensorLeft a).obj X) β ≫ PXinv ≫ lX ≫ bmap =
            Sigma.ι (fun _ : i ⟶ q.left.2 =>
              (tensorLeft a).obj X) β ≫
              Sigma.desc (fun beta =>
                colimit.ι BX (collapsedDecomposition i m q beta)) ≫
              bmap := hstart
        _ = colimit.ι BX b ≫ bmap := by
          rw [Sigma.ι_comp_desc_assoc]
        _ = (a ◁ f) ≫ colimit.ι BY b := by
          change colimit.ι BX b ≫ colim.map
              (blockDecompositionMap A i m f) = _
          have hwB := ι_colimMap (blockDecompositionMap A i m f) b
          have happ : (blockDecompositionMap A i m f).app b = a ◁ f := by
            dsimp [blockDecompositionMap, b, a]
            rw [id_tensorHom]
          rw [happ] at hwB
          exact hwB
    rw [hdgq]
    exact hL.trans hR.symm
  have hDayNatAssoc := congrArg (fun k => k ≫ cY) hDayNat
  simp only [Category.assoc] at hDayNatAssoc
  have hCollapseNatAssoc := congrArg
    (fun k => hDayX.isoColimit.hom ≫ k) hCollapseNat
  have hcore :
      (A ◁ g).natTrans.app m ≫ hDayY.isoColimit.hom ≫ cY =
        hDayX.isoColimit.hom ≫ cX ≫ bmap := by
    exact hDayNatAssoc.trans hCollapseNatAssoc
  have hleftCurrent :
      eXinv ≫ smap ≫ eYhom ≫ hDayY.isoColimit.hom ≫ cY =
        (eXinv ≫ smap ≫ eYhom) ≫ hDayY.isoColimit.hom ≫ cY := by
    simp only [Category.assoc]
  have hrightCurrent :
      eXinv ≫ (eXhom ≫ hDayX.isoColimit.hom ≫ cX) ≫ bmap =
        (eXinv ≫ (eXhom ≫ hDayX.isoColimit.hom ≫ cX)) ≫ bmap := by
    simp only [Category.assoc]
  rw [hleftCurrent, hleft, hrightCurrent, hright]
  simpa only [Category.assoc] using hcore

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Mod

open Operad SmallFinBijGroupoid

universe v u

variable {W : Type u} [Category.{v} W] [MonoidalCategory W]

/-- Evaluation of a free Day module at `m` is the colimit over
complement-first decompositions of `m`. -/
noncomputable def dayFreeAtComponentIso
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    (i m : SmallFinBijGroupoid) :
    dayFreeAt A i ⋙ dayEvaluation A m ≅
      dayFreeAtComponentFunctor A i m :=
  NatIso.ofComponents (fun X => by
    let G := dayFreeDiagram i X
    let D := dayTensorComponentDiagram A i m X
    let B := blockDecompositionDiagram A i m X
    let hDay : (Functor.LeftExtension.mk (A ⊗ G).functor
        (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
      LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
        (C := SmallFinBijGroupoid) (V := W)
        (D := DayFunctor SmallFinBijGroupoid W) A G m
    let eFree :=
      ((DayFunctor.equiv SmallFinBijGroupoid W).functor.mapIso
        (eqToIso (free_obj A G))).app m
    let k : colimit D ≅ colimit B :=
      { hom := colimit.desc D (dayTensorCollapseCocone A i m X)
        inv := colimit.desc B (dayFreeAtComponentBackward A i m X)
        hom_inv_id := dayFreeAtComponentForward_backward A i m X
        inv_hom_id := dayFreeAtComponentBackward_forward A i m X }
    exact eFree ≪≫ hDay.isoColimit ≪≫ k) (by
      intro X Y f
      change
        (dayEvaluation A m).map ((dayFreeAt A i).map f) ≫
            dayFreeAtComponentForward A i m Y =
          dayFreeAtComponentForward A i m X ≫
            (dayFreeAtComponentFunctor A i m).map f
      exact dayFreeAtComponentForward_naturality A i m f)

/-- The component comparison sends the literal free generator to its
decomposition-colimit leg. -/
theorem dayFreeAtComponentIso_generator
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    (i m : SmallFinBijGroupoid) (X : W)
    (d : BlockDecomposition i m) :
    let G := (DayFunctor.equiv SmallFinBijGroupoid W).symm.functor.obj
      ((evaluationLeftAdjoint W i).obj X)
    (((𝟙 (A.functor.obj d.left) ⊗ₘ
            Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)) ≫
          (DayFunctor.η A G).app (d.left, i) ≫
          (A ⊗ G).functor.map d.hom ≫
          (eqToHom (free_obj A G).symm).natTrans.app m) ≫
        (dayFreeAtComponentIso A i m).hom.app X) =
      colimit.ι
        (CostructuredArrow.proj (tensorRight i) m ⋙
          A.functor ⋙ tensorRight X) d := by
  let G := dayFreeDiagram i X
  let D := dayTensorComponentDiagram A i m X
  let B := blockDecompositionDiagram A i m X
  let hDay : (Functor.LeftExtension.mk (A ⊗ G).functor
      (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := W)
      (D := DayFunctor SmallFinBijGroupoid W) A G m
  let eFree : ((free A).obj G).X.functor.obj m ≅
      (A ⊗ G).functor.obj m :=
    ((DayFunctor.equiv SmallFinBijGroupoid W).functor.mapIso
      (eqToIso (free_obj A G))).app m
  let collapse : colimit D ⟶ colimit B :=
    colimit.desc D (dayTensorCollapseCocone A i m X)
  let expand : colimit B ⟶ colimit D :=
    colimit.desc B (dayFreeAtComponentBackward A i m X)
  let rawObj : CostructuredArrow (tensor SmallFinBijGroupoid) m :=
    CostructuredArrow.mk (Y := (d.left, i)) d.hom
  have hiso : (dayFreeAtComponentIso A i m).hom.app X =
      eFree.hom ≫ hDay.isoColimit.hom ≫ collapse := rfl
  rw [hiso]
  let j : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ G.functor).obj (d.left, i) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  let oldFreeInv : (A ⊗ G).functor.obj m ⟶
      ((free A).obj G).X.functor.obj m :=
    (eqToHom (free_obj A G).symm).natTrans.app m
  let genOld : A.functor.obj d.left ⊗ X ⟶
      ((free A).obj G).X.functor.obj m :=
    j ≫ (DayFunctor.η A G).app (d.left, i) ≫
      (A ⊗ G).functor.map d.hom ≫ oldFreeInv
  let genNew : A.functor.obj d.left ⊗ X ⟶
      ((free A).obj G).X.functor.obj m :=
    j ≫ (DayFunctor.η A G).app (d.left, i) ≫
      (A ⊗ G).functor.map d.hom ≫ eFree.inv
  change genOld ≫ eFree.hom ≫ hDay.isoColimit.hom ≫ collapse = _
  have hInv :
      (eqToHom (free_obj A G).symm).natTrans.app m = eFree.inv := by
    have heq := DayFunctor.equiv_functor_map SmallFinBijGroupoid W
      (eqToHom (free_obj A G).symm)
    exact congrArg (fun k => k.app m) heq.symm
  have hgen : genOld = genNew := by
    dsimp [genOld, genNew, oldFreeInv]
    rw [hInv]
  rw [hgen]
  let pre : A.functor.obj d.left ⊗ X ⟶ (A ⊗ G).functor.obj m :=
    j ≫ (DayFunctor.η A G).app (d.left, i) ≫
      (A ⊗ G).functor.map d.hom
  have hgenNew : genNew = pre ≫ eFree.inv := by
    dsimp [genNew, pre]
    simp only [Category.assoc]
  have hcancel : genNew ≫ eFree.hom = pre := by
    rw [hgenNew, Category.assoc, eFree.inv_hom_id, Category.comp_id]
  have hcancelAssoc := congrArg
    (fun k => k ≫ hDay.isoColimit.hom ≫ collapse) hcancel
  have hcancelCurrent :
      genNew ≫ eFree.hom ≫ hDay.isoColimit.hom ≫ collapse =
        pre ≫ hDay.isoColimit.hom ≫ collapse := by
    simpa only [Category.assoc] using hcancelAssoc
  rw [hcancelCurrent]
  dsimp [pre]
  have hraw := hDay.ι_isoColimit_hom rawObj
  change
    (DayFunctor.η A G).app (d.left, i) ≫
        (A ⊗ G).functor.map d.hom ≫ hDay.isoColimit.hom =
      colimit.ι D rawObj at hraw
  have hpreRaw : pre ≫ hDay.isoColimit.hom =
      j ≫ colimit.ι D rawObj := by
    dsimp [pre]
    simpa only [Category.assoc] using congrArg (fun k => j ≫ k) hraw
  have hpreRawAssoc := congrArg (fun k => k ≫ collapse) hpreRaw
  simp only [Category.assoc] at hpreRawAssoc
  rw [hpreRawAssoc]
  have hbf : expand ≫ collapse = 𝟙 (colimit B) :=
    dayFreeAtComponentBackward_forward A i m X
  have happ :
      (dayFreeAtComponentBackward A i m X).ι.app d =
        (𝟙 (A.functor.obj d.left) ⊗ₘ
            Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)) ≫
          colimit.ι D rawObj := rfl
  have hExpand : colimit.ι B d ≫ expand =
      (dayFreeAtComponentBackward A i m X).ι.app d :=
    colimit.ι_desc _ _
  have happJ : (dayFreeAtComponentBackward A i m X).ι.app d =
      j ≫ colimit.ι D rawObj := by
    dsimp [j]
    convert happ using 1
    all_goals rfl
  calc
    j ≫ colimit.ι D rawObj ≫ collapse =
        (dayFreeAtComponentBackward A i m X).ι.app d ≫ collapse := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ collapse) happJ.symm
    _ = (colimit.ι B d ≫ expand) ≫ collapse := by rw [hExpand]
    _ = colimit.ι B d ≫ (expand ≫ collapse) := Category.assoc _ _ _
    _ = colimit.ι B d ≫ 𝟙 (colimit B) := by rw [hbf]
    _ = colimit.ι B d := Category.comp_id _

omit [MonoidalCategory W] in
private theorem dayFreeAtComponentSourceGeneratorPath
    {T EJ CJ MJ QJ QI MI CIJ EIJ EII CII : W}
    (a : T ⟶ EJ) (b : EJ ⟶ CJ) (c : CJ ⟶ MJ)
    (u : MJ ⟶ QJ) (v : QJ ⟶ QI)
    (pM : MJ ⟶ MI) (z : MI ⟶ QI)
    (pJ : CJ ⟶ CIJ) (cI : CIJ ⟶ MI)
    (wPg : EJ ⟶ EIJ) (etaIj : EIJ ⟶ CIJ)
    (inj : T ⟶ EIJ)
    (x : T ⟶ EII) (wGI : EII ⟶ EIJ)
    (etaIi : EII ⟶ CII) (cG : CII ⟶ CIJ)
    (cI' : CII ⟶ MI)
    (hFree : u ≫ v = pM ≫ z)
    (hNat : c ≫ pM = pJ ≫ cI)
    (hEtaPg : b ≫ pJ = wPg ≫ etaIj)
    (hInjPg : a ≫ wPg = inj)
    (hInjGI : x ≫ wGI = inj)
    (hEtaSource : wGI ≫ etaIj = etaIi ≫ cG)
    (hMap : cG ≫ cI = cI') :
    (a ≫ (b ≫ (c ≫ u))) ≫ v =
      x ≫ (etaIi ≫ (cI' ≫ z)) := by
  have hJ0 :
      (a ≫ (b ≫ (c ≫ u))) ≫ v =
        a ≫ ((b ≫ (c ≫ u)) ≫ v) :=
    Category.assoc _ _ _
  have hJ1 :
      a ≫ ((b ≫ (c ≫ u)) ≫ v) =
        a ≫ (b ≫ ((c ≫ u) ≫ v)) :=
    congrArg (fun q => a ≫ q) (Category.assoc _ _ _)
  have hJ2 :
      a ≫ (b ≫ ((c ≫ u) ≫ v)) =
        a ≫ (b ≫ (c ≫ (u ≫ v))) :=
    congrArg (fun q => a ≫ (b ≫ q)) (Category.assoc _ _ _)
  have hFreeWhole :
      a ≫ (b ≫ (c ≫ (u ≫ v))) =
        a ≫ (b ≫ (c ≫ (pM ≫ z))) :=
    congrArg (fun q => a ≫ (b ≫ (c ≫ q))) hFree
  have hNatTail : c ≫ (pM ≫ z) = pJ ≫ (cI ≫ z) := by
    calc
      c ≫ (pM ≫ z) = (c ≫ pM) ≫ z := (Category.assoc _ _ _).symm
      _ = (pJ ≫ cI) ≫ z := congrArg (fun q => q ≫ z) hNat
      _ = pJ ≫ (cI ≫ z) := Category.assoc _ _ _
  have hNatWhole :
      a ≫ (b ≫ (c ≫ (pM ≫ z))) =
        a ≫ (b ≫ (pJ ≫ (cI ≫ z))) :=
    congrArg (fun q => a ≫ (b ≫ q)) hNatTail
  have hEtaPgTail :
      b ≫ (pJ ≫ (cI ≫ z)) = wPg ≫ (etaIj ≫ (cI ≫ z)) := by
    calc
      b ≫ (pJ ≫ (cI ≫ z)) = (b ≫ pJ) ≫ (cI ≫ z) :=
        (Category.assoc _ _ _).symm
      _ = (wPg ≫ etaIj) ≫ (cI ≫ z) :=
        congrArg (fun q => q ≫ (cI ≫ z)) hEtaPg
      _ = wPg ≫ (etaIj ≫ (cI ≫ z)) := Category.assoc _ _ _
  have hEtaPgWhole :
      a ≫ (b ≫ (pJ ≫ (cI ≫ z))) =
        a ≫ (wPg ≫ (etaIj ≫ (cI ≫ z))) :=
    congrArg (fun q => a ≫ q) hEtaPgTail
  have hInjPgTail :
      a ≫ (wPg ≫ (etaIj ≫ (cI ≫ z))) =
        inj ≫ (etaIj ≫ (cI ≫ z)) := by
    calc
      a ≫ (wPg ≫ (etaIj ≫ (cI ≫ z))) =
          (a ≫ wPg) ≫ (etaIj ≫ (cI ≫ z)) :=
        (Category.assoc _ _ _).symm
      _ = inj ≫ (etaIj ≫ (cI ≫ z)) :=
        congrArg (fun q => q ≫ (etaIj ≫ (cI ≫ z))) hInjPg
  have hInjGITail :
      inj ≫ (etaIj ≫ (cI ≫ z)) =
        x ≫ (wGI ≫ (etaIj ≫ (cI ≫ z))) := by
    calc
      inj ≫ (etaIj ≫ (cI ≫ z)) =
          (x ≫ wGI) ≫ (etaIj ≫ (cI ≫ z)) :=
        congrArg (fun q => q ≫ (etaIj ≫ (cI ≫ z))) hInjGI.symm
      _ = x ≫ (wGI ≫ (etaIj ≫ (cI ≫ z))) := Category.assoc _ _ _
  have hEtaSourceTail :
      wGI ≫ (etaIj ≫ (cI ≫ z)) =
        etaIi ≫ (cG ≫ (cI ≫ z)) := by
    calc
      wGI ≫ (etaIj ≫ (cI ≫ z)) =
          (wGI ≫ etaIj) ≫ (cI ≫ z) :=
        (Category.assoc _ _ _).symm
      _ = (etaIi ≫ cG) ≫ (cI ≫ z) :=
        congrArg (fun q => q ≫ (cI ≫ z)) hEtaSource
      _ = etaIi ≫ (cG ≫ (cI ≫ z)) := Category.assoc _ _ _
  have hEtaSourceWhole :
      x ≫ (wGI ≫ (etaIj ≫ (cI ≫ z))) =
        x ≫ (etaIi ≫ (cG ≫ (cI ≫ z))) :=
    congrArg (fun q => x ≫ q) hEtaSourceTail
  have hMapTail : cG ≫ (cI ≫ z) = cI' ≫ z := by
    calc
      cG ≫ (cI ≫ z) = (cG ≫ cI) ≫ z :=
        (Category.assoc _ _ _).symm
      _ = cI' ≫ z := congrArg (fun q => q ≫ z) hMap
  have hMapWhole :
      x ≫ (etaIi ≫ (cG ≫ (cI ≫ z))) =
        x ≫ (etaIi ≫ (cI' ≫ z)) :=
    congrArg (fun q => x ≫ (etaIi ≫ q)) hMapTail
  exact hJ0.trans <| hJ1.trans <| hJ2.trans <| hFreeWhole.trans <|
    hNatWhole.trans <| hEtaPgWhole.trans <| hInjPgTail.trans <|
    hInjGITail.trans <| hEtaSourceWhole.trans hMapWhole

private theorem dayFreeAtComponentSourceMate
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j : SmallFinBijGroupoid} (g : i ⟶ j) (X : W) :
    ((dayFreeAtFunctor A).map g.op).app X =
      (free A).map
        ((DayFunctor.equiv SmallFinBijGroupoid W).symm.functor.map
          ({ app := fun s => Sigma.desc (fun β : j ⟶ s =>
                Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
             naturality := by
               intro s t h
               apply Sigma.hom_ext
               intro β
               dsimp [evaluationLeftAdjoint]
               simp [Category.assoc] } :
            (evaluationLeftAdjoint W j).obj X ⟶
              (evaluationLeftAdjoint W i).obj X)) := by
  let FJ := (evaluationLeftAdjoint W j).obj X
  let FI := (evaluationLeftAdjoint W i).obj X
  let pre : FJ ⟶ FI :=
    { app := fun s => Sigma.desc (fun β : j ⟶ s =>
        Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
      naturality := by
        intro s t h
        apply Sigma.hom_ext
        intro β
        dsimp [FJ, FI, evaluationLeftAdjoint]
        simp [Category.assoc] }
  let eqv := (DayFunctor.equiv SmallFinBijGroupoid W).symm
  let GJ := eqv.functor.obj FJ
  let GI := eqv.functor.obj FI
  let pg : GJ ⟶ GI := eqv.functor.map pre
  let cand := (free A).map pg
  let candM : (dayFreeAt A j).obj X ⟶ (dayFreeAt A i).obj X := cand
  let mate : (dayFreeAt A j).obj X ⟶ (dayFreeAt A i).obj X :=
    ((dayFreeAtFunctor A).map g.op).app X
  let evalJ := CategoryTheory.evaluation SmallFinBijGroupoid W |>.obj j
  let evalI := CategoryTheory.evaluation SmallFinBijGroupoid W |>.obj i
  let adjJ := evaluationAdjunctionRight W j
  let adjI := evaluationAdjunctionRight W i
  let adjE := eqv.toAdjunction
  let adjF := freeForgetAdjunction A
  let u0J := adjJ.unit.app X
  let u0I := adjI.unit.app X
  let u1J := adjE.unit.app FJ
  let u1I := adjE.unit.app FI
  let u2J := adjF.unit.app GJ
  let u2I := adjF.unit.app GI
  have unitJ : (dayFreeAtEvaluationAdjunction A j).unit.app X =
      (u0J ≫ evalJ.map u1J) ≫
        (eqv.inverse ⋙ evalJ).map u2J := by
    change (((adjJ.comp adjE).comp adjF).unit.app X) = _
    rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
    dsimp [u0J, u1J, u2J, evalJ, eqv, adjJ, adjE, adjF, GJ, FJ]
  have unitI : (dayFreeAtEvaluationAdjunction A i).unit.app X =
      (u0I ≫ evalI.map u1I) ≫
        (eqv.inverse ⋙ evalI).map u2I := by
    change (((adjI.comp adjE).comp adjF).unit.app X) = _
    rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
    dsimp [u0I, u1I, u2I, evalI, eqv, adjI, adjE, adjF, GI, FI]
  have hEval : u0J ≫ evalJ.map pre = u0I ≫ FI.map g := by
    dsimp [u0J, u0I, adjJ, adjI, evalJ, evalI, FJ, FI,
      evaluationLeftAdjoint, pre]
    rw [evaluationAdjunctionRight_unit_app,
      evaluationAdjunctionRight_unit_app]
    rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    simp
  let candHom : ((free A).obj GJ).X ⟶ ((free A).obj GI).X := cand.hom
  have hCandEquivMap :=
    DayFunctor.equiv_functor_map SmallFinBijGroupoid W candHom
  have hCandEvalAt (k : SmallFinBijGroupoid) :
      (dayEvaluation A k).map cand = candHom.natTrans.app k := by
    exact congrArg (fun q => q.app k) hCandEquivMap
  have hTargetMap : ((dayFreeAt A i).obj X).X.functor.map g =
      ((free A).obj GI).X.functor.map g := rfl
  have hu1I : evalI.map u1I = u1I.app i := rfl
  have hu2I : (eqv.inverse ⋙ evalI).map u2I =
      u2I.natTrans.app i := by
    dsimp [eqv, evalI]
    rw [DayFunctor.equiv_functor_map]
  have hCandidate :
      (dayFreeAtEvaluationAdjunction A j).unit.app X ≫
          (dayEvaluation A j).map cand =
        (dayFreeAtEvaluationAdjunction A i).unit.app X ≫
          ((dayFreeAt A i).obj X).X.functor.map g := by
    rw [unitJ, unitI]
    have h2 := adjF.unit.naturality pg
    have h1 := adjE.unit.naturality pre
    let EJ := eqv.inverse ⋙ evalJ
    let EI := eqv.inverse ⋙ evalI
    change
      ((u0J ≫ evalJ.map u1J) ≫ EJ.map u2J) ≫
          EJ.map ((forget A).map cand) =
        ((u0I ≫ evalI.map u1I) ≫ EI.map u2I) ≫
          ((dayFreeAt A i).obj X).X.functor.map g
    have hcandMap : (forget A).map cand = (free A ⋙ forget A).map pg := rfl
    erw [hcandMap]
    simp only [Category.assoc]
    rw [← EJ.map_comp]
    rw [← h2]
    rw [EJ.map_comp]
    simp only [Functor.id_map]
    have h1E := congrArg (fun k => evalJ.map k) h1
    simp only [Functor.map_comp] at h1E
    have h1E' :
        evalJ.map pre ≫ evalJ.map u1I =
          evalJ.map u1J ≫ evalJ.map (eqv.inverse.map pg) := by
      convert h1E using 1 <;> rfl
    have hEJpg : EJ.map pg = evalJ.map (eqv.inverse.map pg) := by
      rfl
    have h1EJ :
        evalJ.map pre ≫ evalJ.map u1I =
          evalJ.map u1J ≫ EJ.map pg := by
      rw [hEJpg]
      exact h1E'
    slice_lhs 2 3 => rw [← h1EJ]
    slice_lhs 1 2 => rw [hEval]
    have hu1Ij : evalJ.map u1I = u1I.app j := rfl
    have hu2Ij : EJ.map u2I = u2I.natTrans.app j := by
      dsimp [EJ, eqv, evalJ]
      rw [DayFunctor.equiv_functor_map]
    have hu2Ii : EI.map u2I = u2I.natTrans.app i := by
      exact hu2I
    have hu1Nat :
        FI.map g ≫ u1I.app j =
          u1I.app i ≫ GI.functor.map g := by
      change FI.map g ≫ u1I.app j =
        u1I.app i ≫ (eqv.inverse.obj GI).map g
      exact u1I.naturality g
    have hu2Nat :
        GI.functor.map g ≫ u2I.natTrans.app j =
          u2I.natTrans.app i ≫
            ((free A).obj GI).X.functor.map g := by
      exact u2I.natTrans.naturality g
    rw [hu1Ij, hu2Ij, hu1I, hu2Ii, hTargetMap]
    have hu1NatTail :
        FI.map g ≫ (u1I.app j ≫ u2I.natTrans.app j) =
          u1I.app i ≫
            (GI.functor.map g ≫ u2I.natTrans.app j) := by
      calc
        FI.map g ≫ (u1I.app j ≫ u2I.natTrans.app j) =
            (FI.map g ≫ u1I.app j) ≫ u2I.natTrans.app j :=
          (Category.assoc _ _ _).symm
        _ = (u1I.app i ≫ GI.functor.map g) ≫
            u2I.natTrans.app j := by
          exact congrArg (fun q => q ≫ u2I.natTrans.app j) hu1Nat
        _ = u1I.app i ≫
            (GI.functor.map g ≫ u2I.natTrans.app j) :=
          Category.assoc _ _ _
    have hu1Whole :
        u0I ≫ (FI.map g ≫
          (u1I.app j ≫ u2I.natTrans.app j)) =
        u0I ≫ (u1I.app i ≫
          (GI.functor.map g ≫ u2I.natTrans.app j)) :=
      congrArg (fun q => u0I ≫ q) hu1NatTail
    have hu2Whole :
        u0I ≫ (u1I.app i ≫
          (GI.functor.map g ≫ u2I.natTrans.app j)) =
        u0I ≫ (u1I.app i ≫
          (u2I.natTrans.app i ≫
            ((free A).obj GI).X.functor.map g)) :=
      congrArg (fun q => u0I ≫ (u1I.app i ≫ q)) hu2Nat
    have hLeftAssoc :
        (u0I ≫ (FI.map g ≫ u1I.app j)) ≫
            u2I.natTrans.app j =
          u0I ≫ (FI.map g ≫
            (u1I.app j ≫ u2I.natTrans.app j)) := by
      calc
        (u0I ≫ (FI.map g ≫ u1I.app j)) ≫
              u2I.natTrans.app j =
            u0I ≫ ((FI.map g ≫ u1I.app j) ≫
              u2I.natTrans.app j) := Category.assoc _ _ _
        _ = u0I ≫ (FI.map g ≫
            (u1I.app j ≫ u2I.natTrans.app j)) :=
          congrArg (fun q => u0I ≫ q) (Category.assoc _ _ _)
    have hRightAssoc :
        (u0I ≫ (u1I.app i ≫ u2I.natTrans.app i)) ≫
            ((free A).obj GI).X.functor.map g =
          u0I ≫ (u1I.app i ≫
            (u2I.natTrans.app i ≫
              ((free A).obj GI).X.functor.map g)) := by
      calc
        (u0I ≫ (u1I.app i ≫ u2I.natTrans.app i)) ≫
              ((free A).obj GI).X.functor.map g =
            u0I ≫ ((u1I.app i ≫ u2I.natTrans.app i) ≫
              ((free A).obj GI).X.functor.map g) := Category.assoc _ _ _
        _ = u0I ≫ (u1I.app i ≫
            (u2I.natTrans.app i ≫
              ((free A).obj GI).X.functor.map g)) :=
          congrArg (fun q => u0I ≫ q) (Category.assoc _ _ _)
    have hPrefix :
        ((u0I ≫ FI.map g) ≫ u1I.app j) ≫
            u2I.natTrans.app j =
          (u0I ≫ (FI.map g ≫ u1I.app j)) ≫
            u2I.natTrans.app j :=
      congrArg (fun q => q ≫ u2I.natTrans.app j)
        (Category.assoc u0I (FI.map g) (u1I.app j))
    exact hPrefix.trans (hLeftAssoc.trans
      (hu1Whole.trans (hu2Whole.trans hRightAssoc.symm)))
  have mate_eq_candidate : mate = candM := by
    apply Equiv.injective
      ((dayFreeAtEvaluationAdjunction A j).homEquiv X ((dayFreeAt A i).obj X))
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hm := dayFreeAtFunctor_map_unit A g X
    change
      (dayFreeAtEvaluationAdjunction A i).unit.app X ≫
          ((dayFreeAt A i).obj X).X.functor.map g =
        (dayFreeAtEvaluationAdjunction A j).unit.app X ≫
          (dayEvaluation A j).map mate at hm
    rw [← hm]
    exact hCandidate.symm
  change mate = candM
  exact mate_eq_candidate

omit [MonoidalCategory W] in
private structure SourceCandidateObjects where
  T : W
  EJ : W
  CJ : W
  MJ : W
  QJ : W
  QI : W
  MI : W
  CIJ : W
  EIJ : W
  EII : W
  CII : W

omit [MonoidalCategory W] in
private structure SourceCandidateMaps
    (O : SourceCandidateObjects (W := W)) where
  a : O.T ⟶ O.EJ
  b : O.EJ ⟶ O.CJ
  c : O.CJ ⟶ O.MJ
  u : O.MJ ⟶ O.QJ
  evalMap : O.QJ ⟶ O.QI
  v : O.QJ ⟶ O.QI
  pM : O.MJ ⟶ O.MI
  z : O.MI ⟶ O.QI
  pJ : O.CJ ⟶ O.CIJ
  cI : O.CIJ ⟶ O.MI
  wPg : O.EJ ⟶ O.EIJ
  etaIj : O.EIJ ⟶ O.CIJ
  inj : O.T ⟶ O.EIJ
  x : O.T ⟶ O.EII
  wGI : O.EII ⟶ O.EIJ
  etaIi : O.EII ⟶ O.CII
  cG : O.CII ⟶ O.CIJ
  cI' : O.CII ⟶ O.MI

omit [MonoidalCategory W] in
private structure SourceCandidateLaws
    (O : SourceCandidateObjects (W := W))
    (M : SourceCandidateMaps O) where
  hEval : M.evalMap = M.v
  hFree : M.u ≫ M.v = M.pM ≫ M.z
  hNat : M.c ≫ M.pM = M.pJ ≫ M.cI
  hEtaPg : M.b ≫ M.pJ = M.wPg ≫ M.etaIj
  hInjPg : M.a ≫ M.wPg = M.inj
  hInjGI : M.x ≫ M.wGI = M.inj
  hEtaSource : M.wGI ≫ M.etaIj = M.etaIi ≫ M.cG
  hMap : M.cG ≫ M.cI = M.cI'

private noncomputable def dayFreeAtComponentSourceCandidateObjects
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) : SourceCandidateObjects (W := W) := by
  let FJ := (evaluationLeftAdjoint W j).obj X
  let FI := (evaluationLeftAdjoint W i).obj X
  let pre : FJ ⟶ FI :=
    { app := fun s => Sigma.desc (fun β : j ⟶ s =>
        Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
      naturality := by
        intro s t h
        apply Sigma.hom_ext
        intro β
        dsimp [FJ, FI, evaluationLeftAdjoint]
        simp [Category.assoc] }
  let eqv := (DayFunctor.equiv SmallFinBijGroupoid W).symm
  let GJ := eqv.functor.obj FJ
  let GI := eqv.functor.obj FI
  exact
    { T := A.functor.obj d.left ⊗ X
      EJ := (A.functor ⊠ GJ.functor).obj (d.left, j)
      CJ := (A ⊗ GJ).functor.obj (d.left ⊗ j)
      MJ := (A ⊗ GJ).functor.obj m
      QJ := ((free A).obj GJ).X.functor.obj m
      QI := ((free A).obj GI).X.functor.obj m
      MI := (A ⊗ GI).functor.obj m
      CIJ := (A ⊗ GI).functor.obj (d.left ⊗ j)
      EIJ := (A.functor ⊠ GI.functor).obj (d.left, j)
      EII := (A.functor ⊠ GI.functor).obj (d.left, i)
      CII := (A ⊗ GI).functor.obj (d.left ⊗ i) }

private noncomputable def dayFreeAtComponentSourceCandidateMaps
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) :
    SourceCandidateMaps
      (dayFreeAtComponentSourceCandidateObjects A g X d) := by
  let FJ := (evaluationLeftAdjoint W j).obj X
  let FI := (evaluationLeftAdjoint W i).obj X
  let pre : FJ ⟶ FI :=
    { app := fun s => Sigma.desc (fun β : j ⟶ s =>
        Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
      naturality := by
        intro s t h
        apply Sigma.hom_ext
        intro β
        dsimp [FJ, FI, evaluationLeftAdjoint]
        simp [Category.assoc] }
  let eqv := (DayFunctor.equiv SmallFinBijGroupoid W).symm
  let GJ := eqv.functor.obj FJ
  let GI := eqv.functor.obj FI
  let pg : GJ ⟶ GI := eqv.functor.map pre
  let cand := (free A).map pg
  let candHom : ((free A).obj GJ).X ⟶ ((free A).obj GI).X := cand.hom
  let d' : BlockDecomposition i m :=
    CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)
  let eJ : ((free A).obj GJ).X ≅ A ⊗ GJ :=
    eqToIso (free_obj A GJ)
  let eI : ((free A).obj GI).X ≅ A ⊗ GI :=
    eqToIso (free_obj A GI)
  let sigmaJ : X ⟶ FJ.obj j := by
    dsimp [FJ, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : j ⟶ j => X) (𝟙 j)
  let sigmaI : X ⟶ FI.obj i := by
    dsimp [FI, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  let sigmaG : X ⟶ FI.obj j := by
    dsimp [FI, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : i ⟶ j => X) g
  let sigmaJRaw : X ⟶ GJ.functor.obj j := by
    change X ⟶ FJ.obj j
    exact sigmaJ
  let sigmaIRaw : X ⟶ GI.functor.obj i := by
    change X ⟶ FI.obj i
    exact sigmaI
  let sigmaGRaw : X ⟶ GI.functor.obj j := by
    change X ⟶ FI.obj j
    exact sigmaG
  let jJRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GJ.functor).obj (d.left, j) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaJRaw
  let jIRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GI.functor).obj (d.left, i) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaIRaw
  let injGRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GI.functor).obj (d.left, j) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaGRaw
  let cJ :
      (A ⊗ GJ).functor.obj (d.left ⊗ j) ⟶
        (A ⊗ GJ).functor.obj m :=
    (A ⊗ GJ).functor.map d.hom
  exact
    { a := jJRaw
      b := (DayFunctor.η A GJ).app (d.left, j)
      c := cJ
      u := eJ.inv.natTrans.app m
      evalMap := (dayEvaluation A m).map cand
      v := candHom.natTrans.app m
      pM := (A ◁ pg).natTrans.app m
      z := eI.inv.natTrans.app m
      pJ := (A ◁ pg).natTrans.app (d.left ⊗ j)
      cI := (A ⊗ GI).functor.map d.hom
      wPg := A.functor.obj d.left ◁ pg.natTrans.app j
      etaIj := (DayFunctor.η A GI).app (d.left, j)
      inj := injGRaw
      x := jIRaw
      wGI := A.functor.obj d.left ◁ GI.functor.map g
      etaIi := (DayFunctor.η A GI).app (d.left, i)
      cG := (A ⊗ GI).functor.map (blockSumHom (𝟙 d.left) g)
      cI' := (A ⊗ GI).functor.map d'.hom }

private theorem dayFreeAtComponentSourceCandidateLaws
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) :
    let O := dayFreeAtComponentSourceCandidateObjects A g X d
    let M := dayFreeAtComponentSourceCandidateMaps A g X d
    SourceCandidateLaws O M := by
  let FJ := (evaluationLeftAdjoint W j).obj X
  let FI := (evaluationLeftAdjoint W i).obj X
  let pre : FJ ⟶ FI :=
    { app := fun s => Sigma.desc (fun β : j ⟶ s =>
        Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
      naturality := by
        intro s t h
        apply Sigma.hom_ext
        intro β
        dsimp [FJ, FI, evaluationLeftAdjoint]
        simp [Category.assoc] }
  let eqv := (DayFunctor.equiv SmallFinBijGroupoid W).symm
  let GJ := eqv.functor.obj FJ
  let GI := eqv.functor.obj FI
  let pg : GJ ⟶ GI := eqv.functor.map pre
  let cand := (free A).map pg
  let candHom : ((free A).obj GJ).X ⟶ ((free A).obj GI).X := cand.hom
  have hCandEquivMap :=
    DayFunctor.equiv_functor_map SmallFinBijGroupoid W candHom
  have hCandEvalAt (k : SmallFinBijGroupoid) :
      (dayEvaluation A k).map cand = candHom.natTrans.app k := by
    exact congrArg (fun q => q.app k) hCandEquivMap
  let d' : BlockDecomposition i m :=
    CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)
  let eJ : ((free A).obj GJ).X ≅ A ⊗ GJ :=
    eqToIso (free_obj A GJ)
  let eI : ((free A).obj GI).X ≅ A ⊗ GI :=
    eqToIso (free_obj A GI)
  have hpgApp : pg.natTrans.app j = pre.app j := by
    rfl
  have hGIMap : GI.functor.map g = FI.map g := by
    rfl
  let sigmaJ : X ⟶ FJ.obj j := by
    dsimp [FJ, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : j ⟶ j => X) (𝟙 j)
  let sigmaI : X ⟶ FI.obj i := by
    dsimp [FI, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  let sigmaG : X ⟶ FI.obj j := by
    dsimp [FI, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : i ⟶ j => X) g
  have hpre : sigmaJ ≫ pre.app j = sigmaG := by
    dsimp [sigmaJ, sigmaG, pre, FJ, FI, evaluationLeftAdjoint]
    rw [Sigma.ι_comp_desc]
    simp
  have hpg : sigmaJ ≫ pg.natTrans.app j = sigmaG := by
    rw [hpgApp]
    exact hpre
  have hFIg : sigmaI ≫ FI.map g = sigmaG := by
    dsimp [sigmaI, sigmaG, FI, evaluationLeftAdjoint]
    rw [Sigma.ι_comp_desc]
    simp
  have hGIg : sigmaI ≫ GI.functor.map g = sigmaG := by
    rw [hGIMap]
    exact hFIg
  let sigmaJRaw : X ⟶ GJ.functor.obj j := by
    change X ⟶ FJ.obj j
    exact sigmaJ
  let sigmaIRaw : X ⟶ GI.functor.obj i := by
    change X ⟶ FI.obj i
    exact sigmaI
  let sigmaGRaw : X ⟶ GI.functor.obj j := by
    change X ⟶ FI.obj j
    exact sigmaG
  have hSigmaJRaw : sigmaJRaw = sigmaJ := by
    rfl
  have hSigmaIRaw : sigmaIRaw = sigmaI := by
    rfl
  have hSigmaGRaw : sigmaGRaw = sigmaG := by
    rfl
  let jJRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GJ.functor).obj (d.left, j) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaJRaw
  let jIRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GI.functor).obj (d.left, i) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaIRaw
  let injGRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GI.functor).obj (d.left, j) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaGRaw
  let jJTyped := A.functor.obj d.left ◁ sigmaJ
  let jITyped := A.functor.obj d.left ◁ sigmaI
  let injGTyped := A.functor.obj d.left ◁ sigmaG
  have hJRawWhisker :
      jJRaw = A.functor.obj d.left ◁ sigmaJRaw := by
    dsimp only [jJRaw]
    rw [id_tensorHom]
  have hIRawWhisker :
      jIRaw = A.functor.obj d.left ◁ sigmaIRaw := by
    dsimp only [jIRaw]
    rw [id_tensorHom]
  have hGRawWhisker :
      injGRaw = A.functor.obj d.left ◁ sigmaGRaw := by
    dsimp only [injGRaw]
    rw [id_tensorHom]
  have hJBridge : jJRaw = jJTyped :=
    hJRawWhisker.trans
      (congrArg (fun q => A.functor.obj d.left ◁ q) hSigmaJRaw)
  have hIBridge : jIRaw = jITyped :=
    hIRawWhisker.trans
      (congrArg (fun q => A.functor.obj d.left ◁ q) hSigmaIRaw)
  have hGBridge : injGRaw = injGTyped :=
    hGRawWhisker.trans
      (congrArg (fun q => A.functor.obj d.left ◁ q) hSigmaGRaw)
  have hFree := free_map A pg
  change eJ.hom ≫ (A ◁ pg) = cand.hom ≫ eI.hom at hFree
  have hFreeInv : eJ.inv ≫ cand.hom = (A ◁ pg) ≫ eI.inv := by
    apply (cancel_mono eI.hom).1
    calc
      (eJ.inv ≫ cand.hom) ≫ eI.hom =
          eJ.inv ≫ (cand.hom ≫ eI.hom) := Category.assoc _ _ _
      _ = eJ.inv ≫ (eJ.hom ≫ (A ◁ pg)) := by rw [← hFree]
      _ = (eJ.inv ≫ eJ.hom) ≫ (A ◁ pg) :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ (A ◁ pg) := by rw [eJ.inv_hom_id]
      _ = A ◁ pg := Category.id_comp _
      _ = (A ◁ pg) ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = (A ◁ pg) ≫ (eI.inv ≫ eI.hom) := by
        rw [eI.inv_hom_id]
      _ = ((A ◁ pg) ≫ eI.inv) ≫ eI.hom :=
        (Category.assoc _ _ _).symm
  have hFreeInvM := congrArg (fun q => q.natTrans.app m) hFreeInv
  change
    eJ.inv.natTrans.app m ≫ candHom.natTrans.app m =
      (A ◁ pg).natTrans.app m ≫ eI.inv.natTrans.app m at hFreeInvM
  have hCandAtM : (dayEvaluation A m).map cand =
      candHom.natTrans.app m := hCandEvalAt m
  have hInjPre :
      jJTyped ≫ (A.functor.obj d.left ◁ pre.app j) = injGTyped := by
    dsimp only [jJTyped, injGTyped]
    rw [← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun q => A.functor.obj d.left ◁ q) hpre
  have hInjFI :
      jITyped ≫ (A.functor.obj d.left ◁ FI.map g) = injGTyped := by
    dsimp only [jITyped, injGTyped]
    rw [← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun q => A.functor.obj d.left ◁ q) hFIg
  have hPgWhisker :
      A.functor.obj d.left ◁ pg.natTrans.app j =
        A.functor.obj d.left ◁ pre.app j :=
    congrArg (fun q => A.functor.obj d.left ◁ q) hpgApp
  have hGIWhisker :
      A.functor.obj d.left ◁ GI.functor.map g =
        A.functor.obj d.left ◁ FI.map g :=
    congrArg (fun q => A.functor.obj d.left ◁ q) hGIMap
  have hJAfter :
      jJRaw ≫ (A.functor.obj d.left ◁ pg.natTrans.app j) =
        jJTyped ≫ (A.functor.obj d.left ◁ pg.natTrans.app j) :=
    congrArg
      (fun q => q ≫ (A.functor.obj d.left ◁ pg.natTrans.app j)) hJBridge
  have hPgAfter :
      jJTyped ≫ (A.functor.obj d.left ◁ pg.natTrans.app j) =
        jJTyped ≫ (A.functor.obj d.left ◁ pre.app j) :=
    congrArg (fun q => jJTyped ≫ q) hPgWhisker
  have hInjPg :
      jJRaw ≫ (A.functor.obj d.left ◁ pg.natTrans.app j) = injGRaw := by
    exact hJAfter.trans (hPgAfter.trans (hInjPre.trans hGBridge.symm))
  have hIAfter :
      jIRaw ≫ (A.functor.obj d.left ◁ GI.functor.map g) =
        jITyped ≫ (A.functor.obj d.left ◁ GI.functor.map g) :=
    congrArg
      (fun q => q ≫ (A.functor.obj d.left ◁ GI.functor.map g)) hIBridge
  have hGIAfter :
      jITyped ≫ (A.functor.obj d.left ◁ GI.functor.map g) =
        jITyped ≫ (A.functor.obj d.left ◁ FI.map g) :=
    congrArg (fun q => jITyped ≫ q) hGIWhisker
  have hInjGI :
      jIRaw ≫ (A.functor.obj d.left ◁ GI.functor.map g) = injGRaw := by
    exact hIAfter.trans (hGIAfter.trans (hInjFI.trans hGBridge.symm))
  have hNatPg := (A ◁ pg).natTrans.naturality d.hom
  have hEtaPg :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      W A pg d.left j
  change
    (DayFunctor.η A GJ).app (d.left, j) ≫
        (A ◁ pg).natTrans.app (d.left ⊗ j) =
      (A.functor.obj d.left ◁ pg.natTrans.app j) ≫
        (DayFunctor.η A GI).app (d.left, j) at hEtaPg
  have hEtaSource := (DayFunctor.η A GI).naturality
    ((𝟙 d.left, g) : (d.left, i) ⟶ (d.left, j))
  rw [externalProductBifunctor_obj_map] at hEtaSource
  rw [Functor.comp_map] at hEtaSource
  rw [tensor_map] at hEtaSource
  rw [A.functor.map_id] at hEtaSource
  rw [id_tensorHom] at hEtaSource
  have hWhisker :
      d.left ◁ g = blockSumHom (𝟙 d.left) g := by
    rfl
  have hEtaSourceTyped :
      (A.functor.obj d.left ◁ GI.functor.map g) ≫
          (DayFunctor.η A GI).app (d.left, j) =
        (DayFunctor.η A GI).app (d.left, i) ≫
        (A ⊗ GI).functor.map
          (blockSumHom (𝟙 d.left) g) := by
    simpa only [externalProductBifunctor_obj_obj,
      id_whiskerRight, Category.id_comp, hWhisker] using hEtaSource
  let cJ :
      (A ⊗ GJ).functor.obj (d.left ⊗ j) ⟶
        (A ⊗ GJ).functor.obj m :=
    (A ⊗ GJ).functor.map d.hom
  change
    cJ ≫ (A ◁ pg).natTrans.app m =
      (A ◁ pg).natTrans.app (d.left ⊗ j) ≫
        (A ⊗ GI).functor.map d.hom at hNatPg
  have hMapComp :
      (A ⊗ GI).functor.map (blockSumHom (𝟙 d.left) g) ≫
          (A ⊗ GI).functor.map d.hom =
        (A ⊗ GI).functor.map d'.hom := by
    rw [← Functor.map_comp]
    rfl
  exact
    { hEval := hCandAtM
      hFree := hFreeInvM
      hNat := hNatPg
      hEtaPg := hEtaPg
      hInjPg := hInjPg
      hInjGI := hInjGI
      hEtaSource := by
        change
          (A.functor.obj d.left ◁ GI.functor.map g) ≫
              (DayFunctor.η A GI).app (d.left, j) =
            (DayFunctor.η A GI).app (d.left, i) ≫
              (A ⊗ GI).functor.map
                (blockSumHom (𝟙 d.left) g)
        exact hEtaSourceTyped
      hMap := hMapComp }

omit [MonoidalCategory W] in
private theorem dayFreeAtComponentSourceCandidateGenerator
    (O : SourceCandidateObjects (W := W))
    (M : SourceCandidateMaps O)
    (L : SourceCandidateLaws O M) :
    (M.a ≫ (M.b ≫ (M.c ≫ M.u))) ≫ M.evalMap =
      M.x ≫ (M.etaIi ≫ (M.cI' ≫ M.z)) := by
  have hEvalWhole :
      (M.a ≫ (M.b ≫ (M.c ≫ M.u))) ≫ M.evalMap =
        (M.a ≫ (M.b ≫ (M.c ≫ M.u))) ≫ M.v :=
    congrArg (fun q =>
      (M.a ≫ (M.b ≫ (M.c ≫ M.u))) ≫ q) L.hEval
  have hPath :
      (M.a ≫ (M.b ≫ (M.c ≫ M.u))) ≫ M.v =
        M.x ≫ (M.etaIi ≫ (M.cI' ≫ M.z)) :=
    dayFreeAtComponentSourceGeneratorPath
      (T := O.T) (EJ := O.EJ) (CJ := O.CJ) (MJ := O.MJ)
      (QJ := O.QJ) (QI := O.QI) (MI := O.MI)
      (CIJ := O.CIJ) (EIJ := O.EIJ) (EII := O.EII)
      (CII := O.CII)
      (a := M.a) (b := M.b) (c := M.c) (u := M.u) (v := M.v)
      (pM := M.pM) (z := M.z) (pJ := M.pJ) (cI := M.cI)
      (wPg := M.wPg) (etaIj := M.etaIj) (inj := M.inj)
      (x := M.x) (wGI := M.wGI) (etaIi := M.etaIi)
      (cG := M.cG) (cI' := M.cI')
      (hFree := L.hFree) (hNat := L.hNat) (hEtaPg := L.hEtaPg)
      (hInjPg := L.hInjPg) (hInjGI := L.hInjGI)
      (hEtaSource := L.hEtaSource) (hMap := L.hMap)
  exact hEvalWhole.trans hPath

private theorem dayFreeAtComponentSourceCandidate
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) :
    colimit.ι (blockDecompositionDiagram A j m X) d ≫
      (dayFreeAtComponentIso A j m).inv.app X ≫
      (dayEvaluation A m).map
        ((free A).map
          ((DayFunctor.equiv SmallFinBijGroupoid W).symm.functor.map
            ({ app := fun s => Sigma.desc (fun β : j ⟶ s =>
                  Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
               naturality := by
                 intro s t h
                 apply Sigma.hom_ext
                 intro β
                 dsimp [evaluationLeftAdjoint]
                 simp [Category.assoc] } :
              (evaluationLeftAdjoint W j).obj X ⟶
                (evaluationLeftAdjoint W i).obj X))) ≫
      (dayFreeAtComponentIso A i m).hom.app X =
    colimit.ι (blockDecompositionDiagram A i m X)
      (CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)) := by
  let FJ := (evaluationLeftAdjoint W j).obj X
  let FI := (evaluationLeftAdjoint W i).obj X
  let pre : FJ ⟶ FI :=
    { app := fun s => Sigma.desc (fun β : j ⟶ s =>
        Sigma.ι (fun _ : i ⟶ s => X) (g ≫ β))
      naturality := by
        intro s t h
        apply Sigma.hom_ext
        intro β
        dsimp [FJ, FI, evaluationLeftAdjoint]
        simp [Category.assoc] }
  let eqv := (DayFunctor.equiv SmallFinBijGroupoid W).symm
  let GJ := eqv.functor.obj FJ
  let GI := eqv.functor.obj FI
  let pg : GJ ⟶ GI := eqv.functor.map pre
  let cand := (free A).map pg
  change
    colimit.ι (blockDecompositionDiagram A j m X) d ≫
        (dayFreeAtComponentIso A j m).inv.app X ≫
        (dayEvaluation A m).map cand ≫
        (dayFreeAtComponentIso A i m).hom.app X =
      colimit.ι (blockDecompositionDiagram A i m X)
        (CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom))
  let DJ := blockDecompositionDiagram A j m X
  let DI := blockDecompositionDiagram A i m X
  let d' : BlockDecomposition i m :=
    CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)
  let eJ : ((free A).obj GJ).X ≅ A ⊗ GJ :=
    eqToIso (free_obj A GJ)
  let eI : ((free A).obj GI).X ≅ A ⊗ GI :=
    eqToIso (free_obj A GI)
  let isoJ : ((free A).obj GJ).X.functor.obj m ≅ colimit DJ :=
    (dayFreeAtComponentIso A j m).app X
  let isoI : ((free A).obj GI).X.functor.obj m ≅ colimit DI :=
    (dayFreeAtComponentIso A i m).app X
  let sigmaJ : X ⟶ FJ.obj j := by
    dsimp [FJ, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : j ⟶ j => X) (𝟙 j)
  let sigmaI : X ⟶ FI.obj i := by
    dsimp [FI, evaluationLeftAdjoint]
    exact Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  let sigmaJRaw : X ⟶ GJ.functor.obj j := by
    change X ⟶ FJ.obj j
    exact sigmaJ
  let sigmaIRaw : X ⟶ GI.functor.obj i := by
    change X ⟶ FI.obj i
    exact sigmaI
  let jJRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GJ.functor).obj (d.left, j) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaJRaw
  let jIRaw : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ GI.functor).obj (d.left, i) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ sigmaIRaw
  have hcharJ :
      (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
        ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
          isoJ.hom = colimit.ι DJ d := by
    exact dayFreeAtComponentIso_generator A j m X d
  have hcharI :
      (jIRaw ≫ ((DayFunctor.η A GI).app (d.left, i) ≫
        ((A ⊗ GI).functor.map d'.hom ≫ eI.inv.natTrans.app m))) ≫
          isoI.hom = colimit.ι DI d' := by
    exact dayFreeAtComponentIso_generator A i m X d'
  have hinvJ :
      colimit.ι DJ d ≫ isoJ.inv =
        jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
          ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m)) := by
    calc
      colimit.ι DJ d ≫ isoJ.inv =
          ((jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
            ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
              isoJ.hom) ≫ isoJ.inv := by rw [hcharJ]
      _ = jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
          ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m)) := by
        rw [Category.assoc, isoJ.hom_inv_id, Category.comp_id]
  let sourceObjects := dayFreeAtComponentSourceCandidateObjects A g X d
  let sourceMaps := dayFreeAtComponentSourceCandidateMaps A g X d
  let sourceLaws := dayFreeAtComponentSourceCandidateLaws A g X d
  have hGen := dayFreeAtComponentSourceCandidateGenerator
    sourceObjects sourceMaps sourceLaws
  change
    (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
      ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
        (dayEvaluation A m).map cand =
      jIRaw ≫ ((DayFunctor.η A GI).app (d.left, i) ≫
        ((A ⊗ GI).functor.map d'.hom ≫ eI.inv.natTrans.app m)) at hGen
  have hIsoJInv :
      (dayFreeAtComponentIso A j m).inv.app X = isoJ.inv := by
    rfl
  have hIsoIHom :
      (dayFreeAtComponentIso A i m).hom.app X = isoI.hom := by
    rfl
  rw [hIsoJInv, hIsoIHom]
  let legJ : A.functor.obj d.left ⊗ X ⟶ colimit DJ := colimit.ι DJ d
  let legI : A.functor.obj d.left ⊗ X ⟶ colimit DI := colimit.ι DI d'
  change legJ ≫ isoJ.inv ≫
      (dayEvaluation A m).map cand ≫ isoI.hom = legI
  have hLeft :
      legJ ≫ (isoJ.inv ≫
        ((dayEvaluation A m).map cand ≫ isoI.hom)) =
      (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
        ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom) := by
    calc
      _ = (legJ ≫ isoJ.inv) ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom) :=
        (Category.assoc _ _ _).symm
      _ = (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
            ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom) :=
        congrArg (fun q => q ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom)) hinvJ
  have hRight :
      (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
        ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom) =
      (jIRaw ≫ ((DayFunctor.η A GI).app (d.left, i) ≫
        ((A ⊗ GI).functor.map d'.hom ≫ eI.inv.natTrans.app m))) ≫
          isoI.hom := by
    calc
      _ = ((jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
            ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
          (dayEvaluation A m).map cand) ≫ isoI.hom :=
        (Category.assoc _ _ _).symm
      _ = (jIRaw ≫ ((DayFunctor.η A GI).app (d.left, i) ≫
            ((A ⊗ GI).functor.map d'.hom ≫ eI.inv.natTrans.app m))) ≫
          isoI.hom :=
        congrArg (fun q => q ≫ isoI.hom) hGen
  calc
    legJ ≫ (isoJ.inv ≫
          ((dayEvaluation A m).map cand ≫ isoI.hom)) =
        (jJRaw ≫ ((DayFunctor.η A GJ).app (d.left, j) ≫
          ((A ⊗ GJ).functor.map d.hom ≫ eJ.inv.natTrans.app m))) ≫
            ((dayEvaluation A m).map cand ≫ isoI.hom) := hLeft
    _ = (jIRaw ≫ ((DayFunctor.η A GI).app (d.left, i) ≫
          ((A ⊗ GI).functor.map d'.hom ≫ eI.inv.natTrans.app m))) ≫
            isoI.hom := hRight
    _ = legI := hcharI
private theorem dayFreeAtComponentSourceLeg
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) :
    colimit.ι (blockDecompositionDiagram A j m X) d ≫
        (dayFreeAtComponentIso A j m).inv.app X ≫
        (dayEvaluation A m).map
          (((dayFreeAtFunctor A).map g.op).app X) ≫
        (dayFreeAtComponentIso A i m).hom.app X =
      colimit.ι (blockDecompositionDiagram A i m X)
        (CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)) := by
  rw [dayFreeAtComponentSourceMate A g X]
  exact dayFreeAtComponentSourceCandidate A g X d

/-- The component comparison is contravariant in the free index. -/
theorem dayFreeAtComponentIso_source
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {i j m : SmallFinBijGroupoid} (g : i ⟶ j) (X : W)
    (d : BlockDecomposition j m) :
    colimit.ι
        (CostructuredArrow.proj (tensorRight j) m ⋙
          A.functor ⋙ tensorRight X) d ≫
      (dayFreeAtComponentIso A j m).inv.app X ≫
      (dayEvaluation A m).map
        (((dayFreeAtFunctor A).map g.op).app X) ≫
      (dayFreeAtComponentIso A i m).hom.app X =
    colimit.ι
      (CostructuredArrow.proj (tensorRight i) m ⋙
        A.functor ⋙ tensorRight X)
      (CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom)) := by
  change
    colimit.ι (blockDecompositionDiagram A j m X) d ≫
        (dayFreeAtComponentIso A j m).inv.app X ≫
        (dayEvaluation A m).map
          (((dayFreeAtFunctor A).map g.op).app X) ≫
        (dayFreeAtComponentIso A i m).hom.app X =
      colimit.ι (blockDecompositionDiagram A i m X)
        (CostructuredArrow.mk ((d.left ◁ g) ≫ d.hom))
  exact dayFreeAtComponentSourceLeg A g X d

/-- The component comparison is covariant in the target index. -/
theorem dayFreeAtComponentIso_target
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    (i : SmallFinBijGroupoid) {m m' : SmallFinBijGroupoid}
    (τ : m ⟶ m') (X : W) (d : BlockDecomposition i m) :
    colimit.ι
        (CostructuredArrow.proj (tensorRight i) m ⋙
          A.functor ⋙ tensorRight X) d ≫
        (dayFreeAtComponentIso A i m).inv.app X ≫
        ((dayFreeAt A i).obj X).X.functor.map τ ≫
        (dayFreeAtComponentIso A i m').hom.app X =
      colimit.ι
        (CostructuredArrow.proj (tensorRight i) m' ⋙
          A.functor ⋙ tensorRight X)
        (CostructuredArrow.mk (d.hom ≫ τ)) := by
  let G := dayFreeDiagram i X
  let isoM : ((free A).obj G).X.functor.obj m ≅
      colimit (blockDecompositionDiagram A i m X) :=
    (dayFreeAtComponentIso A i m).app X
  let isoM' : ((free A).obj G).X.functor.obj m' ≅
      colimit (blockDecompositionDiagram A i m' X) :=
    (dayFreeAtComponentIso A i m').app X
  let mmap : ((free A).obj G).X.functor.obj m ⟶
      ((free A).obj G).X.functor.obj m' :=
    ((free A).obj G).X.functor.map τ
  let j : A.functor.obj d.left ⊗ X ⟶
      (A.functor ⊠ G.functor).obj (d.left, i) :=
    𝟙 (A.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)
  let t : (A ⊗ G) ⟶ ((free A).obj G).X :=
    eqToHom (free_obj A G).symm
  let gen : A.functor.obj d.left ⊗ X ⟶
      ((free A).obj G).X.functor.obj m :=
    j ≫ (DayFunctor.η A G).app (d.left, i) ≫
      (A ⊗ G).functor.map d.hom ≫ t.natTrans.app m
  let d' : BlockDecomposition i m' :=
    CostructuredArrow.mk (d.hom ≫ τ)
  let gen' : A.functor.obj d.left ⊗ X ⟶
      ((free A).obj G).X.functor.obj m' :=
    j ≫ (DayFunctor.η A G).app (d.left, i) ≫
      (A ⊗ G).functor.map (d.hom ≫ τ) ≫ t.natTrans.app m'
  have hchar : gen ≫ isoM.hom =
      colimit.ι (blockDecompositionDiagram A i m X) d := by
    exact dayFreeAtComponentIso_generator A i m X d
  have hchar' : gen' ≫ isoM'.hom =
      colimit.ι (blockDecompositionDiagram A i m' X) d' := by
    exact dayFreeAtComponentIso_generator A i m' X d'
  have hinv :
      colimit.ι (blockDecompositionDiagram A i m X) d ≫
          isoM.inv = gen := by
    calc
      colimit.ι (blockDecompositionDiagram A i m X) d ≫ isoM.inv =
          (gen ≫ isoM.hom) ≫ isoM.inv := by rw [hchar]
      _ = gen := by
        rw [Category.assoc, isoM.hom_inv_id, Category.comp_id]
  have hmap : gen ≫ mmap = gen' := by
    have htau := (t.natTrans.naturality τ).symm
    have hc := congrArg
      (fun k => j ≫ (DayFunctor.η A G).app (d.left, i) ≫
        (A ⊗ G).functor.map d.hom ≫ k) htau
    have hfun :
        j ≫ (DayFunctor.η A G).app (d.left, i) ≫
              (A ⊗ G).functor.map d.hom ≫
              (A ⊗ G).functor.map τ ≫ t.natTrans.app m' =
          j ≫ (DayFunctor.η A G).app (d.left, i) ≫
              (A ⊗ G).functor.map (d.hom ≫ τ) ≫
              t.natTrans.app m' := by
      rw [← Functor.map_comp_assoc]
    dsimp [gen, gen', mmap, d']
    have htotal := hc.trans hfun
    simp only [Category.assoc]
    convert htotal using 1
    all_goals rfl
  change colimit.ι (blockDecompositionDiagram A i m X) d ≫
      isoM.inv ≫ mmap ≫ isoM'.hom = _
  calc
    colimit.ι (blockDecompositionDiagram A i m X) d ≫
          isoM.inv ≫ mmap ≫ isoM'.hom =
        gen ≫ mmap ≫ isoM'.hom := by
          simpa only [Category.assoc] using congrArg
            (fun k => k ≫ mmap ≫ isoM'.hom) hinv
    _ = gen' ≫ isoM'.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ isoM'.hom) hmap
    _ = _ := hchar'

end CategoryTheory.Mod

namespace CategoryTheory.Operad.SmallFinBijGroupoid

universe v u

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The canonical functorial coefficient action, retaining literal tensor morphisms. -/
noncomputable def blockCoefficientAction
    (A : DayFunctor SmallFinBijGroupoid V) (R : SmallFinBijGroupoid) (X : V) :
    Aut R →* End (A.functor.obj R ⊗ X) :=
  ((Functor.mapEnd R (A.functor ⋙ tensorRight X)).comp (Aut.toEnd (X := R))).copy
    (fun a => End.of (A.functor.map a.asIso.hom ⊗ₘ 𝟙 X)) (by
      funext a
      apply End.ext
      change A.functor.map a.asIso.hom ⊗ₘ 𝟙 X = A.functor.map a.asIso.hom ▷ X
      exact tensorHom_id _ _)

/-- The coefficient action selects the original tensor of the scalar automorphism. -/
theorem blockCoefficientAction_apply
    (A : DayFunctor SmallFinBijGroupoid V) (R : SmallFinBijGroupoid) (X : V) (a : Aut R) :
    End.asHom (blockCoefficientAction A R X a) = A.functor.map a.asIso.hom ⊗ₘ 𝟙 X := rfl

/-- Coefficient morphisms are equivariant for the actual functorial block action. -/
theorem blockCoefficientAction_naturality
    (A : DayFunctor SmallFinBijGroupoid V) (R : SmallFinBijGroupoid)
    {X Y : V} (f : X ⟶ Y) (a : Aut R) :
    End.asHom (blockCoefficientAction A R X a) ≫ (𝟙 (A.functor.obj R) ⊗ₘ f) =
      (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ End.asHom (blockCoefficientAction A R Y a) := by
  change (A.functor.map a.asIso.hom ⊗ₘ 𝟙 X) ≫ (𝟙 (A.functor.obj R) ⊗ₘ f) =
    (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (A.functor.map a.asIso.hom ⊗ₘ 𝟙 Y)
  simpa only [id_tensorHom, tensorHom_id] using
    (whisker_exchange (A.functor.map a.asIso.hom) f).symm

/-- The canonical induced-object functor for the complement-first block
action at cardinalities `n ≤ m`. -/
noncomputable def cardInducedFunctor
    [HasColimitsOfSize.{0, 0} V]
    (A : DayFunctor SmallFinBijGroupoid V)
    (n m : ℕ) (_h : n ≤ m) : V ⥤ V := by
  let r : ℕ := m - n
  let R : SmallFinBijGroupoid := card r
  let N : SmallFinBijGroupoid := card n
  let M : SmallFinBijGroupoid := card m
  let H : Type := Aut R
  let E : Type := R ⊗ N ≅ M
  let blockAct : MulAction H E := blockMulAction R N M
  letI : MulAction H E := blockAct
  let J (X : V) : ActionCategory H E ⥤ V :=
    ActionCategory.coefficientDiagram H E (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
  let Jmap {X Y : V} (f : X ⟶ Y) : J X ⟶ J Y :=
    ActionCategory.coefficientNatTrans H E (A.functor.obj R ⊗ X) (A.functor.obj R ⊗ Y)
      (blockCoefficientAction A R X) (blockCoefficientAction A R Y)
      (𝟙 (A.functor.obj R) ⊗ₘ f) (blockCoefficientAction_naturality A R f)
  exact
    { obj := fun X => colimit (J X)
      map := fun f => colim.map (Jmap f)
      map_id := by
        intro X
        apply colimit.hom_ext
        intro e
        simp only [colim_obj, colim_map, ι_colimMap, Category.comp_id]
        have hJmapId :
            (Jmap (𝟙 X)).app e = 𝟙 ((J X).obj e) := by
          change 𝟙 (A.functor.obj R) ⊗ₘ 𝟙 X = 𝟙 _
          exact id_tensorHom_id (A.functor.obj R) X
        rw [hJmapId]
        exact Category.id_comp (colimit.ι (J X) e)
      map_comp := by
        intro X Y Z f g
        apply colimit.hom_ext
        intro e
        have hJcomp : (Jmap (f ≫ g)).app e =
            (Jmap f).app e ≫ (Jmap g).app e := by
          change 𝟙 (A.functor.obj R) ⊗ₘ (f ≫ g) =
            (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (𝟙 (A.functor.obj R) ⊗ₘ g)
          exact (congrArg (fun h => h ⊗ₘ (f ≫ g)) (Category.id_comp _)).symm.trans
            (tensorHom_comp_tensorHom (𝟙 (A.functor.obj R)) f
              (𝟙 (A.functor.obj R)) g).symm
        change colimit.ι (J X) e ≫ colimMap (Jmap (f ≫ g)) =
          colimit.ι (J X) e ≫ (colimMap (Jmap f) ≫ colimMap (Jmap g))
        calc
          _ = (Jmap (f ≫ g)).app e ≫ colimit.ι (J Z) e :=
            ι_colimMap (Jmap (f ≫ g)) e
          _ = ((Jmap f).app e ≫ (Jmap g).app e) ≫ colimit.ι (J Z) e :=
            congrArg (fun h => h ≫ colimit.ι (J Z) e) hJcomp
          _ = (Jmap f).app e ≫ ((Jmap g).app e ≫ colimit.ι (J Z) e) :=
            Category.assoc _ _ _
          _ = (Jmap f).app e ≫ (colimit.ι (J Y) e ≫ colimMap (Jmap g)) :=
            congrArg (fun h => (Jmap f).app e ≫ h) (ι_colimMap (Jmap g) e).symm
          _ = ((Jmap f).app e ≫ colimit.ι (J Y) e) ≫ colimMap (Jmap g) :=
            (Category.assoc _ _ _).symm
          _ = (colimit.ι (J X) e ≫ colimMap (Jmap f)) ≫ colimMap (Jmap g) :=
            congrArg (fun h => h ≫ colimMap (Jmap g)) (ι_colimMap (Jmap f) e).symm
          _ = _ := Category.assoc _ _ _ }

/-- The orbit index of complement-first block isomorphisms at cardinalities
`n ≤ m`. -/
noncomputable def cardCosetIndex
    (n m : ℕ) (_h : n ≤ m) : Type := by
  let r : ℕ := m - n
  let R : SmallFinBijGroupoid := card r
  let N : SmallFinBijGroupoid := card n
  let M : SmallFinBijGroupoid := card m
  let H : Type := Aut R
  let E : Type := R ⊗ N ≅ M
  let blockAct : MulAction H E := blockMulAction R N M
  letI : MulAction H E := blockAct
  exact MulAction.orbitRel.Quotient H E

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Mod

open Operad SmallFinBijGroupoid

universe v u

variable {W : Type u} [Category.{v} W] [MonoidalCategory W]

/-- A free Day module generated in cardinality `n` has initial component in
every strictly smaller cardinality `m`. -/
noncomputable def dayFreeAtCardBelowIso
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {n m : ℕ} (h : m < n) :
    dayFreeAt A (card n) ⋙ dayEvaluation A (card m) ≅
      (Functor.const W).obj (⊥_ W) := by
  letI : IsEmpty (BlockDecomposition (card n) (card m)) :=
    ⟨fun d => by
      have hObj :
          (d.left ⊗ card n).of = (card m).of :=
        FintypeCat.Skeleton.is_skeletal ⟨d.hom.iso⟩
      have hLen := congrArg FintypeCat.Skeleton.len hObj
      change d.left.of.len + n = m at hLen
      have hnle : n ≤ m := by
        rw [← hLen]
        exact Nat.le_add_left n d.left.of.len
      exact (Nat.not_le_of_gt h) hnle⟩
  let hInitial (X : W) :
      IsInitial
        ((dayFreeAtComponentFunctor A (card n) (card m)).obj X) := by
    change IsInitial
      (colimit
        (blockDecompositionDiagram A (card n) (card m) X))
    exact isColimitEquivIsInitialOfIsEmpty W
      (colimit.cocone
        (blockDecompositionDiagram A (card n) (card m) X))
      (colimit.isColimit
        (blockDecompositionDiagram A (card n) (card m) X))
  let belowComponentIso :
      dayFreeAtComponentFunctor A (card n) (card m) ≅
        (Functor.const W).obj (⊥_ W) :=
    NatIso.ofComponents
      (fun X => (initialIsoIsInitial (hInitial X)).symm)
      (by
        intro X Y f
        exact (hInitial X).hom_ext _ _)
  exact dayFreeAtComponentIso A (card n) (card m) ≪≫
    belowComponentIso

end CategoryTheory.Mod

namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual complement cardinality of a cardinal block decomposition. -/
theorem cardComplement_length {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) : d.left.of.len = m - n := by
  have hObj : (d.left ⊗ card n).of = (card m).of :=
    FintypeCat.Skeleton.is_skeletal ⟨d.hom.iso⟩
  have hAdd := congrArg FintypeCat.Skeleton.len hObj
  change d.left.of.len + n = m at hAdd
  exact Nat.add_right_cancel (hAdd.trans (Nat.sub_add_cancel h).symm)

/-- The original cardinal proof's exact coefficient normalization. -/
noncomputable def cardComplementIso {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) : card (m - n) ≅ d.left :=
  eqToIso (congrArg card (cardComplement_length h d).symm) ≪≫ cardIso d.left

/-- The original cardinal proof's normalized actual block label. -/
noncomputable def cardNormalizedBlock {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) :
    card (m - n) ⊗ card n ≅ card m :=
  (tensorRight (card n)).mapIso (cardComplementIso h d) ≪≫ asIso d.hom

/-- Target postcomposition retains the actual complement normalization. -/
theorem cardComplementIso_postcompose {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) (k : Aut (card m)) :
    cardComplementIso h (CostructuredArrow.mk (d.hom ≫ k.asIso.hom)) =
      cardComplementIso h d := by
  rfl

/-- Target postcomposition is the literal full target action on normalized labels. -/
theorem cardNormalizedBlock_postcompose {n m : ℕ} (h : n ≤ m)
    (d : BlockDecomposition (card n) (card m)) (k : Aut (card m)) :
    cardNormalizedBlock h (CostructuredArrow.mk (d.hom ≫ k.asIso.hom)) =
      cardNormalizedBlock h d ≪≫ k.asIso := by
  apply Iso.ext
  change (cardComplementIso h (CostructuredArrow.mk (d.hom ≫ k.asIso.hom))).hom ▷ card n ≫
      (d.hom ≫ k.asIso.hom) =
    ((cardComplementIso h d).hom ▷ card n ≫ d.hom) ≫ k.asIso.hom
  rw [cardComplementIso_postcompose]
  exact (Category.assoc _ _ _).symm

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Mod

open Operad SmallFinBijGroupoid

universe v u

variable {W : Type u} [Category.{v} W] [MonoidalCategory W]
variable [HasColimitsOfSize.{0, 0} W]

section NormalizedCocone

variable (A : DayFunctor SmallFinBijGroupoid W)

/-- The original cardinal comparison's actual normalized forward cocone. -/
noncomputable abbrev cardInducedForwardCocone {n m : ℕ} (h : n ≤ m) (X : W) :
    Cocone (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
      A.functor ⋙ tensorRight X) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let H := Aut R
  let E := R ⊗ N ≅ M
  let F := tensorRight N
  let _ := blockMulAction R N M
  let J : ActionCategory H E ⥤ W :=
    ActionCategory.coefficientDiagram H E (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X)
  let k (d : BlockDecomposition N M) := cardComplementIso h d
  let norm (d : BlockDecomposition N M) := cardNormalizedBlock h d
  let a {d e : BlockDecomposition N M} (q : d ⟶ e) : H :=
    Aut.of (k d ≪≫ asIso q.left ≪≫ (k e).symm)
  have qInv {d e : BlockDecomposition N M} (q : d ⟶ e) :
      F.mapIso (asIso q.left).symm ≪≫ asIso d.hom = asIso e.hom := by
    apply Iso.ext
    change F.map (inv q.left) ≫ d.hom = e.hom
    rw [← CostructuredArrow.w q, ← Category.assoc, ← F.map_comp,
      IsIso.inv_hom_id, F.map_id, Category.id_comp]
  have ha {d e : BlockDecomposition N M} (q : d ⟶ e) :
      a q • norm d = norm e := by
    change F.mapIso (a q).asIso.symm ≪≫ norm d = norm e
    calc
      _ = F.mapIso (k e) ≪≫
          (F.mapIso (asIso q.left).symm ≪≫ asIso d.hom) := by
        have hn : norm d = F.mapIso (k d) ≪≫ asIso d.hom := rfl
        rw [hn]
        dsimp only [a]
        simp only [Iso.trans_symm, Functor.mapIso_trans, Iso.trans_assoc,
          Functor.mapIso_symm, Iso.symm_self_id_assoc, Iso.symm_symm_eq]
      _ = F.mapIso (k e) ≪≫ asIso e.hom :=
        congrArg (fun z => F.mapIso (k e) ≪≫ z) (qInv q)
      _ = norm e := rfl
  have hcoeff {d e : BlockDecomposition N M} (q : d ⟶ e) :
      q.left ≫ (k e).inv = (k d).inv ≫ (a q).asIso.hom := by
    dsimp only [a]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc, asIso_hom]
  exact
    { pt := colimit J
      ι :=
        { app := fun d => (A.functor.map (k d).inv ⊗ₘ 𝟙 X) ≫
            colimit.ι J (norm d : ActionCategory H E)
          naturality := by
            intro d e q
            have hc : (A.functor.map q.left ⊗ₘ 𝟙 X) ≫
                (A.functor.map (k e).inv ⊗ₘ 𝟙 X) =
              (A.functor.map (k d).inv ⊗ₘ 𝟙 X) ≫
                (A.functor.map (a q).asIso.hom ⊗ₘ 𝟙 X) := by
              rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
                ← A.functor.map_comp, ← A.functor.map_comp, hcoeff q]
            have hw := colimit.w J
              (show (norm d : ActionCategory H E) ⟶ (norm e : ActionCategory H E) from
                Functor.Elements.homMk (a q) (ha q))
            change (A.functor.map (a q).asIso.hom ⊗ₘ 𝟙 X) ≫
              colimit.ι J (norm e : ActionCategory H E) =
              colimit.ι J (norm d : ActionCategory H E) at hw
            change (A.functor.map q.left ▷ X) ≫
                ((A.functor.map (k e).inv ⊗ₘ 𝟙 X) ≫
                  colimit.ι J (norm e : ActionCategory H E)) =
              ((A.functor.map (k d).inv ⊗ₘ 𝟙 X) ≫
                colimit.ι J (norm d : ActionCategory H E)) ≫ 𝟙 (colimit J)
            rw [← tensorHom_id]
            exact (Category.assoc _ _ _).symm.trans
              ((congrArg (fun f => f ≫ colimit.ι J (norm e : ActionCategory H E)) hc).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun f => (A.functor.map (k d).inv ⊗ₘ 𝟙 X) ≫ f) hw).trans
                    (Category.comp_id _).symm))) } }

end NormalizedCocone

end CategoryTheory.Mod

namespace CategoryTheory.Mod

open Operad SmallFinBijGroupoid

universe v u

variable {W : Type u} [Category.{v} W] [MonoidalCategory W]

/-- The complement-first decomposition colimit is the complete induced
complement-action functor for every Day coefficient. No monoid structure
on that coefficient is used by the original normalization construction. -/
noncomputable def cardComponentInducedIso
    [HasColimitsOfSize.{0, 0} W]
    (A : DayFunctor SmallFinBijGroupoid W)
    {n m : ℕ} (h : n ≤ m) :
    dayFreeAtComponentFunctor A (card n) (card m) ≅
      cardInducedFunctor A n m h := by
  let r : ℕ := m - n
  let R : SmallFinBijGroupoid := card r
  let N : SmallFinBijGroupoid := card n
  let M : SmallFinBijGroupoid := card m
  let H : Type := Aut R
  let E : Type := R ⊗ N ≅ M
  let F : SmallFinBijGroupoid ⥤ SmallFinBijGroupoid := tensorRight N
  let blockAct : MulAction H E := blockMulAction R N M
  letI : MulAction H E := blockAct
  let J (X : W) : ActionCategory H E ⥤ W :=
    ActionCategory.coefficientDiagram H E (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
  let D (X : W) : BlockDecomposition N M ⥤ W :=
    CostructuredArrow.proj F M ⋙ A.functor ⋙ tensorRight X
  let κ (d : BlockDecomposition N M) : R ≅ d.left :=
    cardComplementIso h d
  let norm (d : BlockDecomposition N M) : E :=
    cardNormalizedBlock h d
  let forward (X : W) : colimit (D X) ⟶ colimit (J X) :=
    colimit.desc (D X) (cardInducedForwardCocone A h X)
  have action_triangle {x y : ActionCategory H E} (f : x ⟶ y) :
      F.map f.hom.asIso.hom ≫ y.back.hom = x.back.hom := by
    have hmap := congrArg Iso.hom f.map_val
    change
      (F.mapIso (show R ≅ R from f.hom.asIso).symm ≪≫
          x.back).hom =
        y.back.hom at hmap
    change F.map (show R ⟶ R from f.hom.asIso.hom) ≫
        y.back.hom = x.back.hom
    calc
      F.map f.hom.asIso.hom ≫ y.back.hom =
          F.map f.hom.asIso.hom ≫
            (F.mapIso (show R ≅ R from f.hom.asIso).symm ≪≫
              x.back).hom := by
        rw [← hmap]
      _ = x.back.hom := by
        rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
          ← Category.assoc, ← F.map_comp,
          (show R ≅ R from f.hom.asIso).hom_inv_id,
          F.map_id, Category.id_comp]
  let decompArrow {x y : ActionCategory H E} (f : x ⟶ y) :
      (CostructuredArrow.mk x.back.hom :
          CostructuredArrow F M) ⟶
        (CostructuredArrow.mk y.back.hom :
          CostructuredArrow F M) :=
    CostructuredArrow.homMk
      (S := F) (T := M)
      (f := CostructuredArrow.mk x.back.hom)
      (f' := CostructuredArrow.mk y.back.hom)
      f.hom.asIso.hom (action_triangle f)
  let backwardCocone (X : W) : Cocone (J X) :=
    { pt := colimit (D X)
      ι :=
        { app := fun x =>
            colimit.ι (D X) (CostructuredArrow.mk x.back.hom)
          naturality := by
            intro x y f
            have hw := colimit.w (D X) (decompArrow f)
            change
              (A.functor.map f.hom.asIso.hom ▷ X) ≫
                  colimit.ι (D X)
                    (CostructuredArrow.mk y.back.hom) =
                colimit.ι (D X)
                  (CostructuredArrow.mk x.back.hom) at hw
            change
              (A.functor.map f.hom.asIso.hom ⊗ₘ 𝟙 X) ≫
                  colimit.ι (D X)
                    (CostructuredArrow.mk y.back.hom) =
                colimit.ι (D X)
                    (CostructuredArrow.mk x.back.hom) ≫
                  𝟙 (colimit (D X))
            rw [tensorHom_id, Category.comp_id]
            exact hw } }
  let backward (X : W) : colimit (J X) ⟶ colimit (D X) :=
    colimit.desc (J X) (backwardCocone X)
  let normTo (d : BlockDecomposition N M) :
      CostructuredArrow.mk (norm d).hom ⟶ d :=
    CostructuredArrow.homMk (κ d).hom (by rfl)
  let dx (x : ActionCategory H E) : BlockDecomposition N M :=
    CostructuredArrow.mk x.back.hom
  let scalar (x : ActionCategory H E) : H := Aut.of ((κ (dx x)).symm)
  have scalar_action (x : ActionCategory H E) :
      scalar x • x.back = norm (dx x) := by
    apply Iso.ext
    rfl
  let scalarArrow {x : ActionCategory H E} :
      x ⟶ (norm (dx x) : ActionCategory H E) :=
    Functor.Elements.homMk (scalar x) (scalar_action x)
  let Dmap {X Y : W} (f : X ⟶ Y) : D X ⟶ D Y :=
    { app := fun d => 𝟙 (A.functor.obj d.left) ⊗ₘ f
      naturality := by
        intro d e q
        change
          (A.functor.map q.left ▷ X) ≫
              (𝟙 (A.functor.obj e.left) ⊗ₘ f) =
            (𝟙 (A.functor.obj d.left) ⊗ₘ f) ≫
              (A.functor.map q.left ▷ Y)
        simpa only [id_tensorHom] using
          (whisker_exchange (A.functor.map q.left) f).symm }
  let Jmap {X Y : W} (f : X ⟶ Y) : J X ⟶ J Y :=
    ActionCategory.coefficientNatTrans H E (A.functor.obj R ⊗ X) (A.functor.obj R ⊗ Y)
      (blockCoefficientAction A R X) (blockCoefficientAction A R Y)
      (𝟙 (A.functor.obj R) ⊗ₘ f) (blockCoefficientAction_naturality A R f)
  let componentInducedIso :
      dayFreeAtComponentFunctor A N M ≅
        cardInducedFunctor A n m h :=
    { hom :=
        { app := fun X => forward X
          naturality := by
            intro X Y f
            change colim.map (Dmap f) ≫ forward Y =
              forward X ≫ colim.map (Jmap f)
            have hTensor (d : BlockDecomposition N M) :
                (Dmap f).app d ≫
                    (A.functor.map (κ d).inv ⊗ₘ 𝟙 Y) =
                  (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                    (Jmap f).app (norm d : ActionCategory H E) := by
              change
                (𝟙 (A.functor.obj d.left) ⊗ₘ f) ≫
                    (A.functor.map (κ d).inv ⊗ₘ 𝟙 Y) =
                  (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                    (𝟙 (A.functor.obj R) ⊗ₘ f)
              simpa only [id_tensorHom, tensorHom_id] using
                whisker_exchange (A.functor.map (κ d).inv) f
            apply colimit.hom_ext
            intro d
            let nd : ActionCategory H E :=
              (norm d : ActionCategory H E)
            have hTensorTyped := hTensor d
            change
              (Dmap f).app d ≫
                  (A.functor.map (κ d).inv ⊗ₘ 𝟙 Y) =
                (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                  (Jmap f).app nd at hTensorTyped
            have hTensorAssoc := congrArg
                (fun z => z ≫
                  colimit.ι (J Y) nd)
                hTensorTyped
            have hJ :
                colimit.ι (J X) nd ≫ colimMap (Jmap f) =
                  (Jmap f).app nd ≫ colimit.ι (J Y) nd :=
              ι_colimMap (Jmap f) nd
            have hJPre :
                ((A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                    colimit.ι (J X) nd) ≫
                      colimMap (Jmap f) =
                  (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                    ((Jmap f).app nd ≫ colimit.ι (J Y) nd) := by
              calc
                _ = (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                      (colimit.ι (J X) nd ≫ colimMap (Jmap f)) :=
                  Category.assoc _ _ _
                _ = _ := congrArg
                  (fun z =>
                    (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫ z) hJ
            change
              colimit.ι (D X) d ≫
                  (colim.map (Dmap f) ≫ forward Y) =
                colimit.ι (D X) d ≫
                  (forward X ≫ colim.map (Jmap f))
            calc
              _ = (Dmap f).app d ≫
                  (cardInducedForwardCocone A h Y).ι.app d := by
                change
                  colimit.ι (D X) d ≫
                      (colimMap (Dmap f) ≫
                        colimit.desc (D Y) (cardInducedForwardCocone A h Y)) =
                    (Dmap f).app d ≫
                      (cardInducedForwardCocone A h Y).ι.app d
                rw [ι_colimMap_assoc, colimit.ι_desc]
              _ = ((cardInducedForwardCocone A h X).ι.app d :
                    (D X).obj d ⟶ colimit (J X)) ≫
                  colimMap (Jmap f) := by
                dsimp only [cardInducedForwardCocone]
                change
                  (Dmap f).app d ≫
                      ((A.functor.map (κ d).inv ⊗ₘ 𝟙 Y) ≫
                        colimit.ι (J Y) nd) =
                    ((A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
                        colimit.ι (J X) nd) ≫
                      colimMap (Jmap f)
                exact (Category.assoc _ _ _).symm.trans
                  (hTensorAssoc.trans ((Category.assoc _ _ _).trans hJPre.symm))
              _ = _ := by
                symm
                rw [← Category.assoc, colimit.ι_desc]
                rfl }
      inv :=
        { app := fun X => backward X
          naturality := by
            intro X Y f
            change colim.map (Jmap f) ≫ backward Y =
              backward X ≫ colim.map (Dmap f)
            apply colimit.hom_ext
            intro x
            let d : BlockDecomposition N M := dx x
            change colimit.ι (J X) x ≫ (colim.map (Jmap f) ≫ backward Y) =
              colimit.ι (J X) x ≫ (backward X ≫ colim.map (Dmap f))
            calc
              _ = (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ colimit.ι (D Y) d := by
                change colimit.ι (J X) x ≫
                    (colimMap (Jmap f) ≫ colimit.desc (J Y) (backwardCocone Y)) =
                  (Jmap f).app x ≫ (backwardCocone Y).ι.app x
                rw [ι_colimMap_assoc, colimit.ι_desc]
              _ = (Dmap f).app d ≫ colimit.ι (D Y) d := rfl
              _ = colimit.ι (D X) d ≫ colim.map (Dmap f) :=
                (ι_colimMap (Dmap f) d).symm
              _ = _ := by
                change colimit.ι (D X) d ≫ colim.map (Dmap f) =
                  colimit.ι (J X) x ≫
                    (colimit.desc (J X) (backwardCocone X) ≫ colimMap (Dmap f))
                rw [← Category.assoc, colimit.ι_desc]
                rfl }
      hom_inv_id := by
        ext X
        change forward X ≫ backward X = 𝟙 (colimit (D X))
        apply colimit.hom_ext
        intro d
        dsimp only [forward]
        rw [colimit.ι_desc_assoc]
        let nd : ActionCategory H E :=
          (norm d : ActionCategory H E)
        change
          ((A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
              colimit.ι (J X) nd) ≫
                colimit.desc (J X) (backwardCocone X) =
            colimit.ι (D X) d ≫ 𝟙 (colimit (D X))
        refine (Category.assoc _ _ _).trans ?_
        have hLeg : colimit.ι (J X) nd ≫
            colimit.desc (J X) (backwardCocone X) =
            (backwardCocone X).ι.app nd :=
          colimit.ι_desc (backwardCocone X) nd
        refine (congrArg
          (fun z => (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫ z) hLeg).trans ?_
        change
          (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
              colimit.ι (D X)
                (CostructuredArrow.mk (norm d).hom) =
            colimit.ι (D X) d ≫ 𝟙 (colimit (D X))
        have hw := colimit.w (D X) (normTo d)
        change
          (A.functor.map (κ d).hom ▷ X) ≫
              colimit.ι (D X) d =
            colimit.ι (D X)
              (CostructuredArrow.mk (norm d).hom) at hw
        rw [← tensorHom_id] at hw
        rw [← hw, ← Category.assoc,
          tensorHom_comp_tensorHom, ← A.functor.map_comp,
          (κ d).inv_hom_id, A.functor.map_id,
          Category.id_comp, id_tensorHom_id,
          Category.id_comp, Category.comp_id]
      inv_hom_id := by
        ext X
        change backward X ≫ forward X = 𝟙 (colimit (J X))
        apply colimit.hom_ext
        intro x
        let d : BlockDecomposition N M := dx x
        let nx : ActionCategory H E :=
          (norm d : ActionCategory H E)
        rw [colimit.ι_desc_assoc]
        change colimit.ι (D X) d ≫ colimit.desc (D X) (cardInducedForwardCocone A h X) =
          colimit.ι (J X) x ≫ 𝟙 (colimit (J X))
        rw [colimit.ι_desc]
        have hw := colimit.w (J X) (scalarArrow (x := x))
        change
          (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
              colimit.ι (J X) nx =
            colimit.ι (J X) x at hw
        change
          (A.functor.map (κ d).inv ⊗ₘ 𝟙 X) ≫
              colimit.ι (J X) nx =
            colimit.ι (J X) x ≫ 𝟙 (colimit (J X))
        rw [Category.comp_id]
        exact hw }
  exact componentInducedIso

/-- The canonical-card component of a free Day module is the induced
complement-action functor. -/
noncomputable def dayFreeAtCardInducedIso
    [HasColimitsOfSize.{0, 0} W]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]
    {n m : ℕ} (h : n ≤ m) :
    dayFreeAt A (card n) ⋙ dayEvaluation A (card m) ≅
      cardInducedFunctor A n m h := by
  exact dayFreeAtComponentIso A (card n) (card m) ≪≫
    cardComponentInducedIso A h

end CategoryTheory.Mod

namespace CategoryTheory.Operad.SmallFinBijGroupoid

universe v u

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The fixed-complement induced functor is noncanonically a copower indexed
by complement-action orbits. -/
noncomputable def cardInducedCosetCopowerIso
    [HasColimitsOfSize.{0, 0} V]
    (A : DayFunctor SmallFinBijGroupoid V)
    {n m : ℕ} (h : n ≤ m) :
    cardInducedFunctor A n m h ≅
      tensorLeft (A.functor.obj (card (m - n))) ⋙
        Limits.sigmaConst ⋙
          (CategoryTheory.evaluation (Type 0) V).obj
            (cardCosetIndex n m h) := by
  let R : SmallFinBijGroupoid := card (m - n)
  let N : SmallFinBijGroupoid := card n
  let M : SmallFinBijGroupoid := card m
  let H : Type := Aut R
  let E : Type := R ⊗ N ≅ M
  letI : MulAction H E := blockMulAction R N M
  let Q : Type := MulAction.orbitRel.Quotient H E
  let hfree : ∀ e : E, Function.Injective (fun a : H => a • e) := blockMulAction_free R N M
  refine NatIso.ofComponents (fun X => ?_) ?_
  · change colimit (ActionCategory.coefficientDiagram H E (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X)) ≅ ∐ (fun _ : Q => A.functor.obj R ⊗ X)
    exact ActionCategory.freeActionColimitCopowerIso H E (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X) hfree
  · intro X Y f
    change
      colimMap (ActionCategory.coefficientNatTrans H E (A.functor.obj R ⊗ X)
          (A.functor.obj R ⊗ Y) (blockCoefficientAction A R X) (blockCoefficientAction A R Y)
          (𝟙 (A.functor.obj R) ⊗ₘ f) (blockCoefficientAction_naturality A R f)) ≫
        (ActionCategory.freeActionColimitCopowerIso H E (A.functor.obj R ⊗ Y)
          (blockCoefficientAction A R Y) hfree).hom =
      (ActionCategory.freeActionColimitCopowerIso H E (A.functor.obj R ⊗ X)
          (blockCoefficientAction A R X) hfree).hom ≫
        Limits.Sigma.map (fun _ : Q => A.functor.obj R ◁ f)
    have hfam : (fun _ : Q => A.functor.obj R ◁ f) =
        (fun _ : Q => 𝟙 (A.functor.obj R) ⊗ₘ f) := by
      funext q
      exact (id_tensorHom (A.functor.obj R) f).symm
    rw [hfam]
    exact ActionCategory.freeActionColimitCopowerIso_naturality H E (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X) hfree (A.functor.obj R ⊗ Y) (blockCoefficientAction A R Y)
      (𝟙 (A.functor.obj R) ⊗ₘ f) (blockCoefficientAction_naturality A R f)

end CategoryTheory.Operad.SmallFinBijGroupoid


-- Characteristics of the shared cardinal component comparison.


namespace CategoryTheory.Mod

open Operad SmallFinBijGroupoid

universe v u

variable {W : Type u} [Category.{v} W] [MonoidalCategory W]
variable [HasColimitsOfSize.{0, 0} W]


variable [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
variable [∀ Z : W, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
variable (A : DayFunctor SmallFinBijGroupoid W) [MonObj A]

/-- The selected original cardinal comparison retains its actual forward descent map. -/
theorem dayFreeAtCardInducedIso_forward {n m : ℕ} (h : n ≤ m) (X : W) :
    (dayFreeAtComponentIso A (card n) (card m)).inv.app X ≫
      (dayFreeAtCardInducedIso A h).hom.app X =
    colimit.desc (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
      A.functor ⋙ tensorRight X) (cardInducedForwardCocone A h X) := by
  let D := CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
    A.functor ⋙ tensorRight X
  let cmp : ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) ≅ colimit D :=
    (dayFreeAtComponentIso A (card n) (card m)).app X
  let f : colimit D ⟶ (cardInducedFunctor A n m h).obj X :=
    colimit.desc D (cardInducedForwardCocone A h X)
  have hdata : (dayFreeAtCardInducedIso A h).hom.app X = cmp.hom ≫ f := by
    change cmp.hom ≫ colimit.desc D (cardInducedForwardCocone A h X) = cmp.hom ≫ f
    rfl
  have hcancel : cmp.inv ≫ (cmp.hom ≫ f) = f :=
    (Category.assoc cmp.inv cmp.hom f).symm.trans
      ((congrArg (fun q => q ≫ f) cmp.inv_hom_id).trans (Category.id_comp f))
  change cmp.inv ≫ (dayFreeAtCardInducedIso A h).hom.app X = f
  exact (congrArg (fun q => cmp.inv ≫ q) hdata).trans hcancel

/-- The original cardinal comparison sends each original decomposition leg to its normalized leg. -/
theorem dayFreeAtCardInducedIso_decomposition_generator {n m : ℕ} (h : n ≤ m)
    (X : W) (d : BlockDecomposition (card n) (card m)) :
    letI := blockMulAction (card (m - n)) (card n) (card m)
    colimit.ι (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
        A.functor ⋙ tensorRight X) d ≫
      (dayFreeAtComponentIso A (card n) (card m)).inv.app X ≫
        (dayFreeAtCardInducedIso A h).hom.app X =
    (A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X) ≫
      colimit.ι (ActionCategory.coefficientDiagram
        (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)
        (A.functor.obj (card (m - n)) ⊗ X)
        (blockCoefficientAction A (card (m - n)) X))
        (cardNormalizedBlock h d :
          ActionCategory (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)) := by
  let _ := blockMulAction (card (m - n)) (card n) (card m)
  have hc := dayFreeAtCardInducedIso_forward A h X
  have hg := colimit.ι_desc (cardInducedForwardCocone A h X) d
  exact (congrArg (fun f => colimit.ι
    (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
      A.functor ⋙ tensorRight X) d ≫ f) hc).trans hg

/-- The literal original Day free generator is the same normalized coefficient leg. -/
theorem dayFreeAtCardInducedIso_generator {n m : ℕ} (h : n ≤ m)
    (X : W) (d : BlockDecomposition (card n) (card m)) :
    letI := blockMulAction (card (m - n)) (card n) (card m)
    let G := (DayFunctor.equiv SmallFinBijGroupoid W).symm.functor.obj
      ((evaluationLeftAdjoint W (card n)).obj X)
    (((𝟙 (A.functor.obj d.left) ⊗ₘ
            Sigma.ι (fun _ : card n ⟶ card n => X) (𝟙 (card n))) ≫
          (DayFunctor.η A G).app (d.left, card n) ≫
          (A ⊗ G).functor.map d.hom ≫
          (eqToHom (free_obj A G).symm).natTrans.app (card m)) ≫
        (dayFreeAtCardInducedIso A h).hom.app X) =
      (A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X) ≫
        colimit.ι (ActionCategory.coefficientDiagram
          (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)
          (A.functor.obj (card (m - n)) ⊗ X)
          (blockCoefficientAction A (card (m - n)) X))
          (cardNormalizedBlock h d :
            ActionCategory (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)) := by
  let _ := blockMulAction (card (m - n)) (card n) (card m)
  let G := (DayFunctor.equiv SmallFinBijGroupoid W).symm.functor.obj
    ((evaluationLeftAdjoint W (card n)).obj X)
  let D := CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
    A.functor ⋙ tensorRight X
  let cmp : ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) ≅ colimit D :=
    (dayFreeAtComponentIso A (card n) (card m)).app X
  let cardCmp : ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) ≅
      (cardInducedFunctor A n m h).obj X := (dayFreeAtCardInducedIso A h).app X
  let gen : A.functor.obj d.left ⊗ X ⟶
      ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) :=
    (𝟙 (A.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : card n ⟶ card n => X) (𝟙 (card n))) ≫
    (DayFunctor.η A G).app (d.left, card n) ≫
    (A ⊗ G).functor.map d.hom ≫
    (eqToHom (free_obj A G).symm).natTrans.app (card m)
  have hgen : gen ≫ cmp.hom = colimit.ι D d :=
    dayFreeAtComponentIso_generator A (card n) (card m) X d
  have hcancel : (gen ≫ cmp.hom) ≫ cmp.inv = gen :=
    (Category.assoc gen cmp.hom cmp.inv).trans
      ((congrArg (fun q => gen ≫ q) cmp.hom_inv_id).trans (Category.comp_id gen))
  have hback : (colimit.ι D d) ≫ cmp.inv = gen :=
    (congrArg (fun f => f ≫ cmp.inv) hgen.symm).trans hcancel
  have hnorm := dayFreeAtCardInducedIso_decomposition_generator A h X d
  change gen ≫ cardCmp.hom = _
  exact (congrArg (fun f => f ≫ cardCmp.hom) hback.symm).trans
    ((Category.assoc (colimit.ι D d) cmp.inv cardCmp.hom).trans hnorm)

/-- The full target action of the original free module is the actual normalized
postcomposition leg. -/
theorem dayFreeAtCardInducedIso_target_generator {n m : ℕ} (h : n ≤ m)
    (X : W) (d : BlockDecomposition (card n) (card m)) (k : Aut (card m)) :
    letI := blockMulAction (card (m - n)) (card n) (card m)
    colimit.ι (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
        A.functor ⋙ tensorRight X) d ≫
      (dayFreeAtComponentIso A (card n) (card m)).inv.app X ≫
        ((dayFreeAt A (card n)).obj X).X.functor.map k.asIso.hom ≫
          (dayFreeAtCardInducedIso A h).hom.app X =
    (A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X) ≫
      colimit.ι (ActionCategory.coefficientDiagram
        (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)
        (A.functor.obj (card (m - n)) ⊗ X)
        (blockCoefficientAction A (card (m - n)) X))
        (cardNormalizedBlock h d ≪≫ k.asIso :
          ActionCategory (Aut (card (m - n))) (card (m - n) ⊗ card n ≅ card m)) := by
  let _ := blockMulAction (card (m - n)) (card n) (card m)
  let d' : BlockDecomposition (card n) (card m) :=
    CostructuredArrow.mk (d.hom ≫ k.asIso.hom)
  have ht := dayFreeAtComponentIso_target A (card n) k.asIso.hom X d
  have hg := dayFreeAtCardInducedIso_decomposition_generator A h X d'
  let D := CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
    A.functor ⋙ tensorRight X
  let cmp : ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) ≅ colimit D :=
    (dayFreeAtComponentIso A (card n) (card m)).app X
  let cardCmp : ((dayFreeAt A (card n)).obj X).X.functor.obj (card m) ≅
      (cardInducedFunctor A n m h).obj X := (dayFreeAtCardInducedIso A h).app X
  let ld : A.functor.obj d.left ⊗ X ⟶ colimit D := colimit.ι D d
  let ld' : A.functor.obj d.left ⊗ X ⟶ colimit D := colimit.ι D d'
  let km := ((dayFreeAt A (card n)).obj X).X.functor.map k.asIso.hom
  have ht' : ld ≫ cmp.inv ≫ km ≫ cmp.hom = ld' := ht
  have hc : (ld ≫ cmp.inv ≫ km ≫ cmp.hom) ≫ cmp.inv ≫ cardCmp.hom =
      ld' ≫ cmp.inv ≫ cardCmp.hom :=
    congrArg (fun f => f ≫ cmp.inv ≫ cardCmp.hom) ht'
  have hcc : cmp.hom ≫ cmp.inv ≫ cardCmp.hom = cardCmp.hom :=
    (Category.assoc cmp.hom cmp.inv cardCmp.hom).symm.trans
      ((congrArg (fun q => q ≫ cardCmp.hom) cmp.hom_inv_id).trans
        (Category.id_comp cardCmp.hom))
  have hcancel : (ld ≫ cmp.inv ≫ km ≫ cmp.hom) ≫ cmp.inv ≫ cardCmp.hom =
      ld ≫ cmp.inv ≫ km ≫ cardCmp.hom := by
    simpa only [Category.assoc] using
      congrArg (fun q => ld ≫ cmp.inv ≫ km ≫ q) hcc
  have hnormalized := hg
  rw [cardComplementIso_postcompose, cardNormalizedBlock_postcompose] at hnormalized
  exact hcancel.symm.trans (hc.trans hnormalized)

end CategoryTheory.Mod
