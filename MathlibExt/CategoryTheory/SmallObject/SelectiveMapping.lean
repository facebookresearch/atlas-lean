/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Cell mapping using preservation of only the given diagrams

The given cell indices, mapped arrows and cocones are retained. Coproduct
preservation uses Mathlib's cofan comparison; transfinite composition uses
the actual endpoint and principal-segment cocones from the given diagram.
The size-preservation constructor `AttachCells.map` of `FullyFaithful` is
`AttachCells.mapOfPreserves` under preservation of all colimits of size `w`.
-/

@[expose] public section

noncomputable section

universe w a t vC vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.AttachCells

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Map an attachment using preservation of its actual two coproduct diagrams
and pushout span. -/
noncomputable def mapOfPreserves
    {alpha : Type a} {A B : alpha → C} {g : ∀ i, A i ⟶ B i}
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) (F : C ⥤ D)
    [PreservesColimit (Discrete.functor (fun i : c.ι => A (c.π i))) F]
    [PreservesColimit (Discrete.functor (fun i : c.ι => B (c.π i))) F]
    [PreservesColimit (span c.g₁ c.m) F] :
    AttachCells.{w} (fun i => F.map (g i)) (F.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (F.obj c.cofan₁.pt) (fun i => F.map (c.cofan₁.inj i))
  cofan₂ := Cofan.mk (F.obj c.cofan₂.pt) (fun i => F.map (c.cofan₂.inj i))
  isColimit₁ := isColimitCofanMkObjOfIsColimit F _ c.cofan₁.inj
    (IsColimit.ofIsoColimit c.isColimit₁
      (Cofan.ext (Iso.refl _) (fun i => Category.comp_id _)))
  isColimit₂ := isColimitCofanMkObjOfIsColimit F _ c.cofan₂.inj
    (IsColimit.ofIsoColimit c.isColimit₂
      (Cofan.ext (Iso.refl _) (fun i => Category.comp_id _)))
  m := F.map c.m
  hm i := by
    change F.map (c.cofan₁.inj i) ≫ F.map c.m =
      F.map (g (c.π i)) ≫ F.map (c.cofan₂.inj i)
    simpa only [Functor.map_comp] using congrArg F.map (c.hm i)
  g₁ := F.map c.g₁
  g₂ := F.map c.g₂
  isPushout := F.map_isPushout c.isPushout

end HomotopicalAlgebra.AttachCells

namespace CategoryTheory.TransfiniteCompositionOfShape

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Map the given transfinite composition using only preservation of its
endpoint diagram and its actual principal-segment diagrams. -/
noncomputable def mapOfPreserves
    {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape T f) (F : C ⥤ D)
    [PreservesColimit c.F F]
    (hLimit : ∀ (k : T), Order.IsSuccLimit k →
      PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F) :
    TransfiniteCompositionOfShape T (F.map f) where
  F := c.F ⋙ F
  isoBot := F.mapIso c.isoBot
  isWellOrderContinuous :=
    { nonempty_isColimit k hk := ⟨by
        let _ := hLimit k hk
        exact IsColimit.ofIsoColimit
          (isColimitOfPreserves F (c.F.isColimitOfIsWellOrderContinuous k hk))
          (Cocone.ext (Iso.refl _) (fun i => by
            simp only [Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app,
              Functor.comp_map, Iso.refl_hom, Category.comp_id]))⟩ }
  incl := Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves F c.isColimit)
      (Cocone.ext (Iso.refl _))
  fac := by simp [← Functor.map_comp]

end CategoryTheory.TransfiniteCompositionOfShape

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Map a relative complex using preservation only of its actual endpoint,
principal segments, coproducts and pushout spans. -/
noncomputable def mapOfPreserves
    {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {alpha : T → Type a} {A B : ∀ k, alpha k → C}
    {cell : ∀ k i, A k i ⟶ B k i} {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} cell f) (F : C ⥤ D)
    [PreservesColimit c.F F]
    (hLimit : ∀ (k : T), Order.IsSuccLimit k →
      PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)
    (hSource : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (Discrete.functor (fun i : (c.attachCells k hk).ι => A k ((c.attachCells k hk).π i))) F)
    (hTarget : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (Discrete.functor (fun i : (c.attachCells k hk).ι => B k ((c.attachCells k hk).π i))) F)
    (hPushout : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (span (c.attachCells k hk).g₁ (c.attachCells k hk).m) F) :
    RelativeCellComplex.{w} (fun k i => F.map (cell k i)) (F.map f) where
  __ := c.toTransfiniteCompositionOfShape.mapOfPreserves F hLimit
  attachCells k hk := by
    let _ := hSource k hk
    let _ := hTarget k hk
    let _ := hPushout k hk
    exact (c.attachCells k hk).mapOfPreserves F

/-- Reindex the actual selectively mapped P-cells into Q using the given
mapped-arrow inclusion. -/
noncomputable def mapOfLEOfPreserves
    (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F)
    {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f)
    [PreservesColimit c.F F]
    (hLimit : ∀ (k : T), Order.IsSuccLimit k →
      PreservesColimit ((Set.principalSegIio k).monotone.functor ⋙ c.F) F)
    (hSource : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (Discrete.functor (fun i : (c.attachCells k hk).ι => ((c.attachCells k hk).π i).1.left)) F)
    (hTarget : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (Discrete.functor (fun i : (c.attachCells k hk).ι => ((c.attachCells k hk).π i).1.right)) F)
    (hPushout : ∀ (k : T) (hk : ¬ IsMax k), PreservesColimit
      (span (c.attachCells k hk).g₁ (c.attachCells k hk).m) F) :
    RelativeCellComplex.{w} (fun (_ : T) => Q.homFamily) (F.map f) where
  __ := (c.mapOfPreserves F hLimit hSource hTarget hPushout).toTransfiniteCompositionOfShape
  attachCells k hk := by
    let _ := hSource k hk
    let _ := hTarget k hk
    let _ := hPushout k hk
    exact ((c.attachCells k hk).mapOfPreserves F).reindexCellTypes Q.homFamily
      (fun i => ⟨Arrow.mk (F.map i.1.hom), hPQ _ i.2⟩) (fun _ => Iso.refl _)

end HomotopicalAlgebra.RelativeCellComplex
