/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.CategoryTheory.NerveCommonHom
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# Common-universe left-comma source augmentation

The original left-comma nerves and source projection define the canonical
Bousfield–Kan augmentation in the maximum object and morphism universe.
The cross-universe nerve map keeps the original source category and chains.

This is the contravariant mirror of the right-comma source augmentation:
for `F : C ⥤ D`, the diagram `d ↦ nerve (StructuredArrow d F)` is a
`Dᵒᵖ`-diagram via `StructuredArrow.functor`, and it projects naturally to
the constant diagram on `nerve C`.

This is a strictly model-independent comparison layer. It makes no
contractibility, homotopy, weak-equivalence, Quillen-Theorem-A, or
homotopy-fiber claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe u v uD

section Diagram

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{v} D]

/-- The contravariant diagram of left-comma nerves associated to `F : C ⥤ D`. -/
def leftCommaNerveDiagram (F : C ⥤ D) : Dᵒᵖ ⥤ SSet.{max u v} :=
  StructuredArrow.functor F ⋙ CategoryTheory.nerveFunctor

@[simp]
theorem leftCommaNerveDiagram_obj (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaNerveDiagram F).obj d = nerve (StructuredArrow d.unop F) :=
  rfl

@[simp]
theorem leftCommaNerveDiagram_map (F : C ⥤ D) {d d' : Dᵒᵖ}
    (g : d ⟶ d') :
    (leftCommaNerveDiagram F).map g =
      nerveMap (StructuredArrow.map g.unop) :=
  rfl

@[simp↓]
theorem leftCommaNerveDiagram_map_app_mk (F : C ⥤ D)
    {d d' : Dᵒᵖ} (g : d ⟶ d') (n : ℕ)
    (X : ComposableArrows (StructuredArrow d.unop F) n) :
    ((leftCommaNerveDiagram F).map g).app (op ⦋n⦌) X =
      X ⋙ StructuredArrow.map g.unop :=
  rfl

end Diagram

section SourceProjection

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{v} D]

/-- The comma projection, retyped on the exact bundled category used by
`StructuredArrow.functor`. -/
abbrev leftCommaProjectionFunctor (F : C ⥤ D) (d : Dᵒᵖ) :
    ((StructuredArrow.functor F).obj d : Type (max u v)) ⥤ C := by
  change StructuredArrow d.unop F ⥤ C
  exact StructuredArrow.proj _ _

/-- The left-comma diagram projects naturally to the constant diagram on
`nerve C`. -/
def leftCommaProjection (F : C ⥤ D) :
    leftCommaNerveDiagram.{u, v, uD} F ⟶ (Functor.const Dᵒᵖ).obj (nerve C) where
  app d := nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d)
  naturality d d' g := by
    change (leftCommaNerveDiagram.{u, v, uD} F).map g ≫
        nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d') =
      nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d) ≫ 𝟙 _
    rw [Category.comp_id]
    ext Δ X
    rfl

@[simp]
theorem leftCommaProjection_app (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaProjection.{u, v, uD} F).app d =
      nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d) :=
  rfl

@[simp↓]
theorem leftCommaProjection_app_apply (F : C ⥤ D) (d : Dᵒᵖ)
    (n : ℕ)
    (X : ComposableArrows ((StructuredArrow.functor F).obj d) n) :
    ((leftCommaProjection.{u, v, uD} F).app d).app (op ⦋n⦌) X =
      X ⋙ leftCommaProjectionFunctor.{u, v, uD} F d :=
  rfl

/-- Simplified naturality square for the left-comma projection. -/
theorem leftCommaProjection_naturality (F : C ⥤ D)
    {d d' : Dᵒᵖ} (g : d ⟶ d') :
    (leftCommaNerveDiagram.{u, v, uD} F).map g ≫
        nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d') =
      nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d) := by
  have h := (leftCommaProjection.{u, v, uD} F).naturality g
  change (leftCommaNerveDiagram.{u, v, uD} F).map g ≫
      nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d') =
    nerveMapCommonHom.{u, v, 0} (leftCommaProjectionFunctor.{u, v, uD} F d) ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

end SourceProjection

section NativeTotal

universe w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The original native weighted total uses its actual maximum-value projection cocone. -/
def leftCommaTotalToSourceNative (F : C ⥤ D) :
    bkHocolim (leftCommaNerveDiagram.{max u w, max v w, u} F) ⟶ nerve C :=
  bkAugmentation (leftCommaProjection.{max u w, max v w, u} F)

end NativeTotal

section LegacyTotal

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The original common-object source augmentation keeps its former `.{u, v}` API. -/
def leftCommaTotalToSource (F : C ⥤ D) :
    bkHocolim (leftCommaNerveDiagram.{u, v, u} F) ⟶ nerve C :=
  leftCommaTotalToSourceNative.{u, v, 0} F

@[simp]
theorem leftCommaTotalToSource_app_mk (F : C ⥤ D) (n : ℕ) :
    (leftCommaTotalToSource.{u, v} F).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit Dᵒᵖ) (leftCommaNerveDiagram.{u, v, u} F) n
          (fun p => (leftCommaProjection.{u, v, u} F).app p.1.left)).app (op ⦋n⦌) :=
  bkAugmentation_app_mk (leftCommaProjection.{u, v, u} F) n

/-- On a weighted summand, the left-comma total projection retains the original chain map. -/
theorem leftCommaTotalToSource_app_mk_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx Dᵒᵖ (CategoryBar.replUnit Dᵒᵖ) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Dᵒᵖ) (leftCommaNerveDiagram.{u, v, u} F) n p).app
          (op ⦋n⦌) ≫
      (leftCommaTotalToSource.{u, v} F).app (op ⦋n⦌) =
    (nerveMapCommonHom.{u, v, 0}
      (leftCommaProjectionFunctor.{u, v, u} F p.1.left)).app (op ⦋n⦌) := by
  exact bkAugmentation_app_mk_ι (leftCommaProjection.{u, v, u} F) n p

end LegacyTotal

end SSet
