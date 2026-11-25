/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Retract

/-!
# Chosen splittings and original colimit cocones

A chosen splitting retains both objects, its inclusion and retraction,
and the splitting on its source. Maps retain both component squares.
The actual universal-property maps on two supplied colimit cocones give
their chosen colimit splitting and its source-identity endpoint Arrow retract.
The category and arbitrary diagram index have independent object and Hom
universes. This implements the coherent-colimit construction used in
Hovey, *Model Categories*, Proposition 2.1.16, printed pp. 33–34.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uJ vJ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallObject.CoherentRetracts

section OriginalCocones

variable {J : Type uJ} [Category.{vJ} J] {C : Type u} [Category.{v} C]
  {F G : J ⥤ C}

/-- The actual universal-property maps on two original colimit cocones
preserve a supplied coherent splitting of their diagrams. No choice of new
colimit objects, endpoint maps or colimit-preservation instance is needed. -/
@[simps i r]
def retractOfColimitCocones (cF : Cocone F) (cG : Cocone G)
    (hF : IsColimit cF) (hG : IsColimit cG)
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F) :
    Retract cF.pt cG.pt where
  i := hF.map cG i
  r := hG.map cF r
  retract := by
    apply hF.hom_ext
    intro j
    have hj := congrArg (fun s : F ⟶ F => s.app j) hir
    simp only [NatTrans.comp_app, NatTrans.id_app] at hj
    rw [hF.ι_map_assoc, hG.ι_map, ← Category.assoc, hj]
    simp

/-- The endpoint arrow retract retains the original source and its two
original legs. This applies at any chosen stage and, in particular, to
the bottom or any limit of a continuous transfinite diagram. -/
@[simps! i_left i_right r_left r_right]
def retractArrowOfColimitCocones (cF : Cocone F) (cG : Cocone G)
    (hF : IsColimit cF) (hG : IsColimit cG)
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F)
    {A : C} (j : J) (sF : A ⟶ F.obj j) (sG : A ⟶ G.obj j)
    (hi : sF ≫ i.app j = sG) (hr : sG ≫ r.app j = sF) :
    RetractArrow (sF ≫ cF.ι.app j) (sG ≫ cG.ι.app j) where
  i := Arrow.homMk (𝟙 A) (hF.map cG i) (by
    change 𝟙 A ≫ (sG ≫ cG.ι.app j) = (sF ≫ cF.ι.app j) ≫ hF.map cG i
    rw [Category.id_comp, Category.assoc, hF.ι_map, ← Category.assoc, hi])
  r := Arrow.homMk (𝟙 A) (hG.map cF r) (by
    change 𝟙 A ≫ (sF ≫ cF.ι.app j) = (sG ≫ cG.ι.app j) ≫ hG.map cF r
    rw [Category.id_comp, Category.assoc, hG.ι_map, ← Category.assoc, hr])
  retract := by
    ext
    · simp
    · exact (retractOfColimitCocones cF cG hF hG i r hir).retract

end OriginalCocones

/-- An actual pair of objects with its chosen inclusion, retraction and splitting. -/
structure SplitObject (C : Type u) [Category.{v} C] where
  /-- The original retract object. -/
  source : C
  /-- The object into which the original source is split. -/
  target : C
  /-- The chosen original inclusion. -/
  inclusion : source ⟶ target
  /-- The chosen original retraction. -/
  retraction : target ⟶ source
  /-- The splitting equation on the original source. -/
  splitting : inclusion ≫ retraction = 𝟙 source

namespace SplitObject

variable {C : Type u} [Category.{v} C]

/-- A map between chosen splittings retains both component maps and both squares. -/
structure Hom (X Y : SplitObject C) where
  /-- The actual map of the source objects. -/
  left : X.source ⟶ Y.source
  /-- The actual map of the target objects. -/
  right : X.target ⟶ Y.target
  /-- The original inclusion square commutes. -/
  inclusion_naturality : X.inclusion ≫ right = left ≫ Y.inclusion
  /-- The original retraction square commutes. -/
  retraction_naturality : X.retraction ≫ left = right ≫ Y.retraction

/-- Maps of chosen splittings are determined by their two actual components. -/
@[ext]
theorem Hom.ext {X Y : SplitObject C} {f g : Hom X Y}
    (hleft : f.left = g.left) (hright : f.right = g.right) : f = g := by
  cases f
  cases g
  cases hleft
  cases hright
  rfl

/-- The identity preserves both original squares. -/
@[simps]
def identity (X : SplitObject C) : Hom X X where
  left := 𝟙 X.source
  right := 𝟙 X.target
  inclusion_naturality := by simp
  retraction_naturality := by simp

/-- Composition preserves both actual component squares. -/
@[simps]
def composition {X Y Z : SplitObject C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  inclusion_naturality := by
    rw [← Category.assoc, f.inclusion_naturality, Category.assoc,
      g.inclusion_naturality, ← Category.assoc]
  retraction_naturality := by
    rw [← Category.assoc, f.retraction_naturality, Category.assoc,
      g.retraction_naturality, ← Category.assoc]

instance : Category.{v} (SplitObject C) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp f := by ext <;> simp [identity, composition]
  comp_id f := by ext <;> simp [identity, composition]
  assoc f g h := by ext <;> simp [composition, Category.assoc]

/-- Projection retains the actual original source object and map. -/
@[simps]
def sourceFunctor : SplitObject C ⥤ C where
  obj X := X.source
  map f := f.left

/-- Projection retains the actual constructed target object and map. -/
@[simps]
def targetFunctor : SplitObject C ⥤ C where
  obj X := X.target
  map f := f.right

/-- The initial state has both actual source maps equal to the identity. -/
@[simps]
def identityObject (X : C) : SplitObject C where
  source := X
  target := X
  inclusion := 𝟙 X
  retraction := 𝟙 X
  splitting := Category.id_comp _

/-- The complete original diagram can be viewed as identity splittings. -/
@[simps]
def identityFunctor : C ⥤ SplitObject C where
  obj := identityObject
  map f :=
    { left := f
      right := f
      inclusion_naturality := by simp [identityObject]
      retraction_naturality := by simp [identityObject] }

variable {J : Type uJ} [Category.{vJ} J] (D : J ⥤ SplitObject C)

/-- The entire diagram of original inclusion maps. -/
@[simps]
def inclusionNatTrans : D ⋙ sourceFunctor ⟶ D ⋙ targetFunctor where
  app j := (D.obj j).inclusion
  naturality _j _k f := (D.map f).inclusion_naturality.symm

/-- The entire diagram of original retraction maps. -/
@[simps]
def retractionNatTrans : D ⋙ targetFunctor ⟶ D ⋙ sourceFunctor where
  app j := (D.obj j).retraction
  naturality _j _k f := (D.map f).retraction_naturality.symm

/-- The splitting is literal on the whole original source diagram. -/
theorem inclusion_retraction : inclusionNatTrans D ≫ retractionNatTrans D =
    𝟙 (D ⋙ sourceFunctor) := by
  ext j
  exact (D.obj j).splitting

variable (cF : Cocone (D ⋙ sourceFunctor)) (cG : Cocone (D ⋙ targetFunctor))
  (hF : IsColimit cF) (hG : IsColimit cG)

/-- Colimits use the two actual supplied cocone points and universal-property maps. -/
@[simps source target inclusion retraction]
def colimitObject : SplitObject C where
  source := cF.pt
  target := cG.pt
  inclusion := hF.map cG (inclusionNatTrans D)
  retraction := hG.map cF (retractionNatTrans D)
  splitting := (retractOfColimitCocones cF cG hF hG
    (inclusionNatTrans D) (retractionNatTrans D) (inclusion_retraction D)).retract

/-- The actual source and target legs form the colimit splitting cocone. -/
@[simps!]
def colimitCocone : Cocone D where
  pt := colimitObject D cF cG hF hG
  ι :=
    { app j :=
        { left := cF.ι.app j
          right := cG.ι.app j
          inclusion_naturality := (hF.ι_map cG (inclusionNatTrans D) j).symm
          retraction_naturality := (hG.ι_map cF (retractionNatTrans D) j).symm }
      naturality j k f := by
        apply Hom.ext
        · exact cF.ι.naturality f
        · exact cG.ι.naturality f }

/-- The induced map keeps both actual colimit universal properties and both squares. -/
@[simps]
def colimitDesc (t : Cocone D) : (colimitCocone D cF cG hF hG).pt ⟶ t.pt := by
  let l : cF.pt ⟶ t.pt.source := hF.desc (sourceFunctor.mapCocone t)
  let r : cG.pt ⟶ t.pt.target := hG.desc (targetFunctor.mapCocone t)
  refine { left := l, right := r, inclusion_naturality := ?_, retraction_naturality := ?_ }
  · apply hF.hom_ext
    intro j
    have hl : cF.ι.app j ≫ l = (t.ι.app j).left := hF.fac _ j
    have hr : cG.ι.app j ≫ r = (t.ι.app j).right := hG.fac _ j
    change cF.ι.app j ≫ (hF.map cG (inclusionNatTrans D) ≫ r) =
      cF.ι.app j ≫ (l ≫ t.pt.inclusion)
    rw [hF.ι_map_assoc, hr, ← Category.assoc, hl]
    exact (t.ι.app j).inclusion_naturality
  · apply hG.hom_ext
    intro j
    have hl : cF.ι.app j ≫ l = (t.ι.app j).left := hF.fac _ j
    have hr : cG.ι.app j ≫ r = (t.ι.app j).right := hG.fac _ j
    change cG.ι.app j ≫ (hG.map cF (retractionNatTrans D) ≫ l) =
      cG.ι.app j ≫ (r ≫ t.pt.retraction)
    rw [hG.ι_map_assoc, hl, ← Category.assoc, hr]
    exact (t.ι.app j).retraction_naturality

/-- The whole splitting cocone is a colimit, with no alternate source point selected. -/
def colimitIsColimit : IsColimit (colimitCocone D cF cG hF hG) where
  desc := colimitDesc D cF cG hF hG
  fac t j := by
    apply Hom.ext
    · exact hF.fac (sourceFunctor.mapCocone t) j
    · exact hG.fac (targetFunctor.mapCocone t) j
  uniq t m hm := by
    apply Hom.ext
    · apply hF.hom_ext
      intro j
      exact (congrArg Hom.left (hm j)).trans (hF.fac (sourceFunctor.mapCocone t) j).symm
    · apply hG.hom_ext
      intro j
      exact (congrArg Hom.right (hm j)).trans (hG.fac (targetFunctor.mapCocone t) j).symm

end SplitObject

end CategoryTheory.SmallObject.CoherentRetracts
