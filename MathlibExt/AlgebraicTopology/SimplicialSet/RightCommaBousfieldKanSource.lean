/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# Common-universe right-comma source augmentation

The right-comma diagram retains independent source and target object levels.
For the source projection, source objects lie in `max u w`, target objects in `u`,
and both Hom levels in `max v w`; their native nerves have the same value universe.
Setting `w = 0` recovers the original common-object interface. The projection and
Bousfield–Kan augmentation keep the original categories, functor and chains.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe uC h uD u v w

section Diagram

variable {C : Type uC} {D : Type uD} [Category.{h} C] [Category.{h} D]

/-- The covariant diagram of right-comma nerves associated to `F : C ⥤ D`. -/
def rightCommaNerveDiagram (F : C ⥤ D) : D ⥤ SSet.{max uC h} :=
  CostructuredArrow.functor F ⋙ CategoryTheory.nerveFunctor

@[simp]
theorem rightCommaNerveDiagram_obj (F : C ⥤ D) (d : D) :
    (rightCommaNerveDiagram F).obj d = nerve (CostructuredArrow F d) :=
  rfl

@[simp]
theorem rightCommaNerveDiagram_map (F : C ⥤ D) {d d' : D}
    (g : d ⟶ d') :
    (rightCommaNerveDiagram F).map g =
      nerveMap (CostructuredArrow.map g) :=
  rfl

@[simp↓]
theorem rightCommaNerveDiagram_map_app_mk (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') (n : ℕ)
    (X : ComposableArrows (CostructuredArrow F d) n) :
    ((rightCommaNerveDiagram F).map g).app (op ⦋n⦌) X =
      X ⋙ CostructuredArrow.map g :=
  rfl

end Diagram

section CommonNativeUniverse

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The comma projection, retyped on the exact bundled category used by
`CostructuredArrow.functor`. -/
abbrev rightCommaProjectionFunctor (F : C ⥤ D) (d : D) :
    ((CostructuredArrow.functor F).obj d : Type (max u v w)) ⥤ C := by
  change CostructuredArrow F d ⥤ C
  exact CostructuredArrow.proj F d

/-- The right-comma diagram projects naturally to the constant diagram on
`nerve C`. -/
def rightCommaProjection (F : C ⥤ D) :
    rightCommaNerveDiagram F ⟶ (Functor.const D).obj (nerve C) where
  app d := nerveMapCross (rightCommaProjectionFunctor F d)
  naturality d d' g := by
    change (rightCommaNerveDiagram F).map g ≫
        nerveMapCross (rightCommaProjectionFunctor F d') =
      nerveMapCross (rightCommaProjectionFunctor F d) ≫ 𝟙 _
    rw [Category.comp_id]
    ext Δ X
    rfl

@[simp]
theorem rightCommaProjection_app (F : C ⥤ D) (d : D) :
    (rightCommaProjection F).app d =
      nerveMapCross (rightCommaProjectionFunctor F d) :=
  rfl

@[simp↓]
theorem rightCommaProjection_app_apply (F : C ⥤ D) (d : D)
    (n : ℕ)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj d) n) :
    ((rightCommaProjection F).app d).app (op ⦋n⦌) X =
      X ⋙ rightCommaProjectionFunctor F d :=
  rfl

/-- Simplified naturality square for the right-comma projection. -/
theorem rightCommaProjection_naturality (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (rightCommaNerveDiagram F).map g ≫
        nerveMapCross (rightCommaProjectionFunctor F d') =
      nerveMapCross (rightCommaProjectionFunctor F d) := by
  have h := (rightCommaProjection F).naturality g
  change (rightCommaNerveDiagram F).map g ≫
      nerveMapCross (rightCommaProjectionFunctor F d') =
    nerveMapCross (rightCommaProjectionFunctor F d) ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

/-- The Bousfield--Kan total of the right-comma nerve diagram maps to
`nerve C` through its projection cocone. -/
def rightCommaTotalToSource (F : C ⥤ D) :
    bkHocolim (rightCommaNerveDiagram F) ⟶ nerve C :=
  bkAugmentation (rightCommaProjection F)

@[simp]
theorem rightCommaTotalToSource_app_mk (F : C ⥤ D) (n : ℕ) :
    (rightCommaTotalToSource F).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n
          (fun p => (rightCommaProjection F).app p.1.left)).app (op ⦋n⦌) :=
  bkAugmentation_app_mk (rightCommaProjection F) n

/-- On a weighted summand, the right-comma total projection is the nerve of
the corresponding comma projection. -/
theorem rightCommaTotalToSource_app_mk_ι (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram F) n p).app
          (op ⦋n⦌) ≫
      (rightCommaTotalToSource F).app (op ⦋n⦌) =
    (nerveMapCross (rightCommaProjectionFunctor F p.1.left)).app (op ⦋n⦌) := by
  exact bkAugmentation_app_mk_ι (rightCommaProjection F) n p

end CommonNativeUniverse

end SSet
