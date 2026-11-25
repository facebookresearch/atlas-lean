/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Closed.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Closed
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic

/-!
# Day convolution is closed

Let `C` be a monoidal category and `V` a monoidal closed category in which every functor
`Cᵒᵖ ⥤ C ⥤ V` has an end. Then the Day convolution monoidal structure on `C ⊛⥤ V` is closed: the
internal hom `[F, G]` is the functor
`c ↦ ∫_j [F j, G (j ⊗ c)]`.

Mathlib's `DayConvolutionInternalHom F G H` records that `H` is such an end, and constructs from it
the evaluation `F ⊛ H ⟶ G`, the coevaluation `G ⟶ [F, F ⊛ G]` and their triangle identities. We
choose the ends functorially through `endFunctor`, so that `[F, -]` is a functor, check that it
satisfies `DayConvolutionInternalHom`, and assemble the evaluation and coevaluation into an
adjunction `tensorLeft F ⊣ [F, -]`. This turns the construction of Mathlib's
`CategoryTheory.MonoidalCategory.DayConvolution.Closed` into an actual `MonoidalClosed` instance on
`C ⊛⥤ V`.

## Main definitions

* `DayFunctor.internalHom F`: the internal hom functor `[F, -]` for Day convolution.
* `DayFunctor.dayConvolutionInternalHom F G`: `[F, G]` is an internal hom of `F` and `G` in the
  sense of `DayConvolutionInternalHom`.
* `DayFunctor.internalHomAdjunction F`: the adjunction `tensorLeft F ⊣ [F, -]`.
* `DayFunctor.monoidalClosed`: the `MonoidalClosed` instance on `C ⊛⥤ V`.

## Main statements

* `DayFunctor.η_app_comp_ev_natTrans_app`: the evaluation `F ⊗ [F, G] ⟶ G`, restricted along the
  Day convolution unit, is the uncurried end projection.
* `DayFunctor.coev_natTrans_app_comp_π`: the coevaluation `G ⟶ [F, F ⊗ G]`, followed by an end
  projection, is the curried Day convolution unit.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Math. 137 (1970), 1–38.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory.DayFunctor

open scoped ExternalProduct
open Limits Opposite LawfulDayConvolutionMonoidalCategoryStruct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]
    [∀ F : Cᵒᵖ ⥤ C ⥤ V, HasEnd F]

/-- The internal hom functor `[F, -]` for the Day convolution product: the functor `G ↦ [F, G]`
with `[F, G].obj c = ∫_j [F j, G (j ⊗ c)]`. -/
def internalHom (F : C ⊛⥤ V) : (C ⊛⥤ V) ⥤ (C ⊛⥤ V) where
  obj G := .mk ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor ⋙
    endFunctor C V)
  map g := .mk (Functor.whiskerRight
    ((dayConvolutionInternalHomDiagramFunctor F.functor).map g.natTrans) (endFunctor C V))
  map_id G := by
    ext : 1
    simp only [id_natTrans, Functor.map_id, Functor.whiskerRight_id']
  map_comp f g := by
    ext : 1
    simp only [comp_natTrans, Functor.map_comp, Functor.whiskerRight_comp]

variable (F : C ⊛⥤ V)

/-- The value of `[F, G]` at `c` is the end `∫_j [F j, G (j ⊗ c)]`. -/
lemma internalHom_obj_functor_obj (G : C ⊛⥤ V) (c : C) :
    ((internalHom F).obj G).functor.obj c =
      end_ ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) :=
  (rfl)

/-- The projection `[F, G].obj c ⟶ [F j, G (j ⊗ c)]` from the end. -/
def π (G : C ⊛⥤ V) (c j : C) :
    ((internalHom F).obj G).functor.obj c ⟶ (ihom (F.functor.obj j)).obj (G.functor.obj (j ⊗ c)) :=
  end_.π _ j

variable {F} in
/-- Morphisms into `[F, G].obj c` are determined by their composites with the projections. -/
@[ext]
lemma π_hom_ext {G : C ⊛⥤ V} {c : C} {X : V} {f g : X ⟶ ((internalHom F).obj G).functor.obj c}
    (h : ∀ j, f ≫ π F G c j = g ≫ π F G c j) : f = g :=
  end_.hom_ext h

/-- The projections out of `[F, G].obj c` form a wedge. -/
@[reassoc]
lemma π_comp_ihom_map (G : C ⊛⥤ V) (c : C) {i j : C} (f : i ⟶ j) :
    π F G c i ≫ (ihom (F.functor.obj i)).map (G.functor.map (f ▷ c)) =
      π F G c j ≫ (MonoidalClosed.pre (F.functor.map f)).app (G.functor.obj (j ⊗ c)) :=
  end_.condition _ f

/-- The functoriality of `[F, G]` in the variable `c`, along the projections. -/
@[reassoc (attr := simp)]
lemma map_natTrans_app_comp_π (G : C ⊛⥤ V) {c c' : C} (f : c ⟶ c') (j : C) :
    ((internalHom F).obj G).functor.map f ≫ π F G c' j =
      π F G c j ≫ (ihom (F.functor.obj j)).map (G.functor.map (j ◁ f)) :=
  end_.map_π _ j

/-- The functoriality of `[F, -]`, along the projections. -/
@[reassoc (attr := simp)]
lemma internalHom_map_natTrans_app_comp_π {G G' : C ⊛⥤ V} (g : G ⟶ G') (c j : C) :
    ((internalHom F).map g).natTrans.app c ≫ π F G' c j =
      π F G c j ≫ (ihom (F.functor.obj j)).map (g.natTrans.app (j ⊗ c)) :=
  end_.map_π _ j

/-- `[F, G]` is an internal hom of `F` and `G` for Day convolution in the sense of Mathlib's
`DayConvolutionInternalHom`: its values are ends, with the projections `π`. -/
def dayConvolutionInternalHom (G : C ⊛⥤ V) :
    DayConvolutionInternalHom F.functor G.functor ((internalHom F).obj G).functor where
  π := π F G
  hπ := π_comp_ihom_map F G
  isLimitWedge _ := (limit.isLimit _).ofIsoLimit (Multifork.isoOfι _)
  map_comp_π := map_natTrans_app_comp_π F G

variable {F} in
/-- The projections of `dayConvolutionInternalHom F G` are the end projections `π`. -/
@[simp]
lemma dayConvolutionInternalHom_π (G : C ⊛⥤ V) (c j : C) :
    (dayConvolutionInternalHom F G).π c j = π F G c j :=
  (rfl)

/-- The morphism of internal homs that Mathlib's `DayConvolutionInternalHom.map` induces from a
morphism `g : G ⟶ G'` is the image of `g` under the functor `[F, -]`. -/
lemma dayConvolutionInternalHom_map {G G' : C ⊛⥤ V} (g : G ⟶ G') :
    (dayConvolutionInternalHom F G).map g.natTrans (dayConvolutionInternalHom F G') =
      ((internalHom F).map g).natTrans := by
  ext c j
  rw [internalHom_map_natTrans_app_comp_π, ← dayConvolutionInternalHom_π,
    DayConvolutionInternalHom.map_app_comp_π, dayConvolutionInternalHom_π]

variable
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-- The Day convolution of the underlying functors of two Day functors, as the chosen
`DayConvolution` structure of the lawful Day convolution structure on `C ⊛⥤ V`. -/
@[instance_reducible]
private def dayConvolution (F G : C ⊛⥤ V) : DayConvolution F.functor G.functor :=
  convolution C V (C ⊛⥤ V) F G

attribute [local instance] dayConvolution

/-- The evaluation `F ⊗ [F, G] ⟶ G` of the Day convolution internal hom. -/
def ev (G : C ⊛⥤ V) : F ⊗ (internalHom F).obj G ⟶ G :=
  .mk (dayConvolutionInternalHom F G).ev_app

/-- The coevaluation `G ⟶ [F, F ⊗ G]` of the Day convolution internal hom. -/
def coev (G : C ⊛⥤ V) : G ⟶ (internalHom F).obj (F ⊗ G) :=
  .mk (dayConvolutionInternalHom F (F ⊗ G)).coev_app

/-- The evaluation `F ⊗ [F, G] ⟶ G`, restricted along the Day convolution unit, is the uncurried
projection from the end. -/
@[reassoc (attr := simp)]
lemma η_app_comp_ev_natTrans_app (G : C ⊛⥤ V) (x y : C) :
    (η F ((internalHom F).obj G)).app (x, y) ≫ (ev F G).natTrans.app (x ⊗ y) =
      MonoidalClosed.uncurry (π F G y x) :=
  (dayConvolutionInternalHom F G).unit_app_ev_app_app x y

/-- The coevaluation `G ⟶ [F, F ⊗ G]`, followed by a projection from the end, is the curried
Day convolution unit. -/
@[reassoc (attr := simp)]
lemma coev_natTrans_app_comp_π (G : C ⊛⥤ V) (c j : C) :
    (coev F G).natTrans.app c ≫ π F (F ⊗ G) c j = MonoidalClosed.curry ((η F G).app (j, c)) :=
  DayConvolutionInternalHom.coev_app_π (G := G.functor) (dayConvolutionInternalHom F (F ⊗ G)) c j

omit [∀ F : Cᵒᵖ ⥤ C ⥤ V, HasEnd F] [MonoidalClosed V] in
/-- Under the identification of `F ⊗ G` with the chosen Day convolution of the underlying
functors, a left whiskering is the Day convolution of an identity with a morphism. -/
private lemma whiskerLeft_natTrans {G G' : C ⊛⥤ V} (g : G ⟶ G') :
    (F ◁ g).natTrans = DayConvolution.map (𝟙 F.functor) g.natTrans :=
  ι_map_whiskerLeft_eq_tensorHom C V (C ⊛⥤ V) F g

/-- The coevaluation `G ⟶ [F, F ⊗ G]` is natural in `G`. -/
@[reassoc]
lemma coev_naturality {G G' : C ⊛⥤ V} (g : G ⟶ G') :
    g ≫ coev F G' = coev F G ≫ (internalHom F).map (F ◁ g) := by
  ext1
  rw [comp_natTrans, comp_natTrans, ← dayConvolutionInternalHom_map, whiskerLeft_natTrans]
  exact DayConvolutionInternalHom.coev_naturality_app (G := G.functor) _ g.natTrans _

/-- The evaluation `F ⊗ [F, G] ⟶ G` is natural in `G`. -/
@[reassoc]
lemma ev_naturality {G G' : C ⊛⥤ V} (g : G ⟶ G') :
    F ◁ (internalHom F).map g ≫ ev F G' = ev F G ≫ g := by
  ext1
  rw [comp_natTrans, comp_natTrans, whiskerLeft_natTrans, ← dayConvolutionInternalHom_map]
  exact DayConvolutionInternalHom.ev_naturality_app _ _ g.natTrans

/-- The first triangle identity: `F ⊗ G ⟶ F ⊗ [F, F ⊗ G] ⟶ F ⊗ G` is the identity. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_coev_comp_ev (G : C ⊛⥤ V) : F ◁ coev F G ≫ ev F (F ⊗ G) = 𝟙 (F ⊗ G) := by
  ext1
  rw [comp_natTrans, whiskerLeft_natTrans]
  exact DayConvolutionInternalHom.left_triangle_components G.functor _

/-- The second triangle identity: `[F, G] ⟶ [F, F ⊗ [F, G]] ⟶ [F, G]` is the identity. -/
@[reassoc (attr := simp)]
lemma coev_comp_internalHom_map_ev (G : C ⊛⥤ V) :
    coev F ((internalHom F).obj G) ≫ (internalHom F).map (ev F G) =
      𝟙 ((internalHom F).obj G) := by
  ext1
  rw [comp_natTrans, ← dayConvolutionInternalHom_map]
  exact DayConvolutionInternalHom.right_triangle_components G.functor _ _

/-- The Day convolution product with `F` is left adjoint to the internal hom functor `[F, -]`. -/
def internalHomAdjunction : tensorLeft F ⊣ internalHom F :=
  Adjunction.mkOfUnitCounit
    { unit := { app := coev F, naturality _ _ g := coev_naturality F g }
      counit := { app := ev F, naturality _ _ g := ev_naturality F g }
      left_triangle := by
        ext G : 2
        simp
      right_triangle := by
        ext G : 2
        simp }

/-- Day convolution with values in a monoidal closed category with ends is monoidal closed, with
internal hom `[F, G].obj c = ∫_j [F j, G (j ⊗ c)]`. -/
instance monoidalClosed : MonoidalClosed (C ⊛⥤ V) where
  closed F := { rightAdj := internalHom F, adj := internalHomAdjunction F }

/-- The internal hom of `C ⊛⥤ V` is `internalHom`. -/
lemma ihom_eq_internalHom : ihom F = internalHom F :=
  (rfl)

/-- The evaluation of the monoidal closed structure on `C ⊛⥤ V` is `ev`. -/
@[simp]
lemma ihom_ev_app (G : C ⊛⥤ V) : (ihom.ev F).app G = ev F G :=
  (rfl)

/-- The coevaluation of the monoidal closed structure on `C ⊛⥤ V` is `coev`. -/
@[simp]
lemma ihom_coev_app (G : C ⊛⥤ V) : (ihom.coev F).app G = coev F G :=
  (rfl)

/-- The curried morphism `G ⟶ [F, H]` of `f : F ⊗ G ⟶ H`, followed by a projection from the end,
is the curried restriction of `f` along the Day convolution unit. -/
@[simp, reassoc]
lemma curry_natTrans_app_comp_π {G H : C ⊛⥤ V} (f : F ⊗ G ⟶ H) (c j : C) :
    (MonoidalClosed.curry f).natTrans.app c ≫ π F H c j =
      MonoidalClosed.curry ((η F G).app (j, c) ≫ f.natTrans.app (j ⊗ c)) := by
  -- `MonoidalClosed.curry f` is `coev F G ≫ (internalHom F).map f`, but its target is
  -- `(ihom F).obj H` rather than `(internalHom F).obj H`, which are only definitionally equal.
  -- The first step therefore closes by `exact` after the rewrite, not by `rw`.
  calc (MonoidalClosed.curry f).natTrans.app c ≫ π F H c j
      = (coev F G).natTrans.app c ≫ ((internalHom F).map f).natTrans.app c ≫ π F H c j := by
        rw [MonoidalClosed.curry_eq f]
        exact Category.assoc _ _ _
    _ = MonoidalClosed.curry ((η F G).app (j, c) ≫ f.natTrans.app (j ⊗ c)) := by
        rw [internalHom_map_natTrans_app_comp_π, coev_natTrans_app_comp_π_assoc,
          MonoidalClosed.curry_natural_right]

/-- The uncurried morphism `F ⊗ G ⟶ H` of `g : G ⟶ [F, H]`, restricted along the Day convolution
unit, is the uncurried composite of `g` with a projection from the end. -/
@[reassoc (attr := simp)]
lemma η_app_comp_uncurry_natTrans_app {G H : C ⊛⥤ V} (g : G ⟶ (internalHom F).obj H) (x y : C) :
    (η F G).app (x, y) ≫ (MonoidalClosed.uncurry g).natTrans.app (x ⊗ y) =
      MonoidalClosed.uncurry (g.natTrans.app y ≫ π F H y x) := by
  -- `g` is typed with target `(internalHom F).obj H`, definitionally equal to `(ihom F).obj H`,
  -- so that `F ◁ g` composes with `ev F H` syntactically.
  calc (η F G).app (x, y) ≫ (MonoidalClosed.uncurry g).natTrans.app (x ⊗ y)
      = (η F G).app (x, y) ≫ (F ◁ g).natTrans.app (x ⊗ y) ≫ (ev F H).natTrans.app (x ⊗ y) := by
        rw [MonoidalClosed.uncurry_eq g, comp_natTrans, NatTrans.comp_app, ihom_ev_app]
        -- The two sides agree up to the implicit object `(ihom F).obj H = (internalHom F).obj H`.
        rfl
    _ = MonoidalClosed.uncurry (g.natTrans.app y ≫ π F H y x) := by
        rw [η_app_comp_whiskerLeft_natTrans_app_assoc, η_app_comp_ev_natTrans_app,
          MonoidalClosed.uncurry_natural_left]

end

end CategoryTheory.MonoidalCategory.DayFunctor
