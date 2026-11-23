/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SplitHomotopyEquivOver
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# The nerve of the category of isomorphism arrows

For a category `D`, `IsomorphismArrow D` is the category whose objects are
isomorphisms in `D` and whose morphisms are arbitrary commutative squares.  Its
source projection has a strict identity-arrow section.  The square
`(𝟙 _, e.hom)` deforms the identity-arrow section back to an isomorphism arrow,
and its source component is the identity.  Consequently the source map on
nerves is a split simplicial homotopy equivalence over `nerve D`, as is every
base change of that map.

The source map uses `nerveMapCross` in its large-object-to-small-object
direction.  The identity-arrow section is defined directly degreewise; this
file introduces no second generic cross-universe nerve API, full-arrow,
category-bar, Theorem A/B, Quillen, pointed, or loop-space claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
  CartesianMonoidalCategory
open scoped Simplicial

universe v u

namespace CategoryTheory

/-- The category of isomorphisms in `D` and arbitrary commutative squares. -/
abbrev IsomorphismArrow (D : Type u) [Category.{v} D] :=
  (MorphismProperty.isomorphisms D).Arrow
    (⊤ : MorphismProperty D) (⊤ : MorphismProperty D)

variable (D : Type u) [Category.{v} D]

/-- Projection of an isomorphism arrow to its source. -/
def isomorphismArrowSource : IsomorphismArrow D ⥤ D where
  obj e := e.left
  map f := f.left
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem isomorphismArrowSource_obj (e : IsomorphismArrow D) :
    (isomorphismArrowSource D).obj e = e.left :=
  rfl

@[simp]
theorem isomorphismArrowSource_map {e e' : IsomorphismArrow D}
    (f : e ⟶ e') :
    (isomorphismArrowSource D).map f = f.left :=
  rfl

/-- Projection of an isomorphism arrow to its target. -/
def isomorphismArrowTarget : IsomorphismArrow D ⥤ D where
  obj e := e.right
  map f := f.right
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem isomorphismArrowTarget_obj (e : IsomorphismArrow D) :
    (isomorphismArrowTarget D).obj e = e.right :=
  rfl

@[simp]
theorem isomorphismArrowTarget_map {e e' : IsomorphismArrow D}
    (f : e ⟶ e') :
    (isomorphismArrowTarget D).map f = f.right :=
  rfl

/-- The identity-arrow section of the source projection. -/
def isomorphismArrowIdentity : D ⥤ IsomorphismArrow D where
  obj X :=
    { left := X
      right := X
      hom := 𝟙 X
      prop := (inferInstance : IsIso (𝟙 X)) }
  map f :=
    { left := f
      right := f
      w := by simp
      prop_hom_left := trivial
      prop_hom_right := trivial }
  map_id X := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

@[simp]
theorem isomorphismArrowIdentity_obj_hom (X : D) :
    ((isomorphismArrowIdentity D).obj X).hom = 𝟙 X :=
  rfl

@[simp]
theorem isomorphismArrowIdentity_map_left {X Y : D} (f : X ⟶ Y) :
    ((isomorphismArrowIdentity D).map f).left = f :=
  rfl

@[simp]
theorem isomorphismArrowIdentity_map_right {X Y : D} (f : X ⟶ Y) :
    ((isomorphismArrowIdentity D).map f).right = f :=
  rfl

/-- The identity-arrow functor is a strict section of source projection. -/
@[simp]
theorem isomorphismArrowIdentity_comp_source :
    isomorphismArrowIdentity D ⋙ isomorphismArrowSource D =
      Functor.id D := by
  rfl

/-- At `e : x ≅ y`, the square `(id_x, e.hom)` runs from the identity
arrow at `x` to `e`. -/
noncomputable def isomorphismArrowSourceToIdentity :
    isomorphismArrowSource D ⋙ isomorphismArrowIdentity D ⟶
      Functor.id (IsomorphismArrow D) where
  app e :=
    { left := 𝟙 e.left
      right := e.hom
      w := by
        change 𝟙 e.left ≫ e.hom = 𝟙 e.left ≫ e.hom
        rfl
      prop_hom_left := trivial
      prop_hom_right := trivial }
  naturality {e e'} f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.left ≫ 𝟙 e'.left = 𝟙 e.left ≫ f.left
      simp
    · change f.left ≫ e'.hom = e.hom ≫ f.right
      exact MorphismProperty.Arrow.w f

@[simp]
theorem isomorphismArrowSourceToIdentity_app_left
    (e : IsomorphismArrow D) :
    ((isomorphismArrowSourceToIdentity (D := D)).app e).left = 𝟙 e.left :=
  rfl

@[simp]
theorem isomorphismArrowSourceToIdentity_app_right
    (e : IsomorphismArrow D) :
    ((isomorphismArrowSourceToIdentity (D := D)).app e).right = e.hom :=
  rfl

/-- The source projection on nerves.  The object universe drops from
`max u v` to `u`, while the hom universe remains `v`. -/
def isomorphismArrowNerveSource :
    nerve (IsomorphismArrow D) ⟶ nerve D :=
  nerveMapCross (isomorphismArrowSource D)

/-- The identity-arrow section on nerves, defined directly in the
small-object-to-large-object direction. -/
def isomorphismArrowNerveIdentity :
    nerve D ⟶ nerve (IsomorphismArrow D) where
  app _ := ↾fun X ↦
    ((isomorphismArrowIdentity D).mapComposableArrows _).obj X

@[simp]
theorem isomorphismArrowNerveSource_app_mk₀
    (e : IsomorphismArrow D) :
    (isomorphismArrowNerveSource D).app (op ⦋0⦌)
        (ComposableArrows.mk₀ e) =
      ComposableArrows.mk₀ e.left :=
  nerveMapCross_app_mk₀ _ _

@[simp]
theorem isomorphismArrowNerveIdentity_app_mk₀ (X : D) :
    (isomorphismArrowNerveIdentity D).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((isomorphismArrowIdentity D).obj X) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem isomorphismArrowNerveSource_app_mk₁
    {e e' : IsomorphismArrow D} (f : e ⟶ e') :
    (isomorphismArrowNerveSource D).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ f.left :=
  nerveMapCross_app_mk₁ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem isomorphismArrowNerveIdentity_app_mk₁ {X Y : D} (f : X ⟶ Y) :
    (isomorphismArrowNerveIdentity D).app (op ⦋1⦌)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((isomorphismArrowIdentity D).map f) :=
  ComposableArrows.ext₁ rfl rfl
    (by simp [isomorphismArrowNerveIdentity])

/-- The identity-arrow nerve map is a strict section of the source nerve map. -/
@[simp]
theorem isomorphismArrowNerveIdentity_comp_source :
    isomorphismArrowNerveIdentity D ≫
      isomorphismArrowNerveSource D = 𝟙 (nerve D) := by
  ext a X
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

private theorem isomorphismArrowCylinder_comp_source :
    NatTrans.nerveCylinderFunctorCross
        (isomorphismArrowSourceToIdentity (D := D)) ⋙
        isomorphismArrowSource D =
      Prod.fst (IsomorphismArrow D) (Fin 2) ⋙
        isomorphismArrowSource D := by
  apply Functor.hext
  · rintro ⟨e, i⟩
    fin_cases i <;> rfl
  · rintro ⟨e, i⟩ ⟨e', j⟩ f
    rcases f with ⟨f, g⟩
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctorCross,
          isomorphismArrowSourceToIdentity, isomorphismArrowIdentity,
          isomorphismArrowSource, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctorCross,
          isomorphismArrowSourceToIdentity, isomorphismArrowIdentity,
          isomorphismArrowSource, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
        omega
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctorCross,
          isomorphismArrowSourceToIdentity, isomorphismArrowIdentity,
          isomorphismArrowSource, ComposableArrows.mk₁]

private theorem isomorphismArrowNerveHomotopyMap_comp_source :
    NatTrans.nerveHomotopyMapCross
        (isomorphismArrowSourceToIdentity (D := D)) ≫
        isomorphismArrowNerveSource D =
      fst (nerve (IsomorphismArrow D))
          (Δ[1] : SSet.{max u v}) ≫
        isomorphismArrowNerveSource D := by
  ext a Z
  change
    (((NatTrans.nerveCylinderFunctorCross
          (isomorphismArrowSourceToIdentity (D := D)) ⋙
        isomorphismArrowSource D).mapComposableArrows _).obj
      (Z.1.prod' (SSet.stdSimplex.asOrderHom Z.2).toFunctor)) =
      ((isomorphismArrowSource D).mapComposableArrows _).obj Z.1
  rw [isomorphismArrowCylinder_comp_source]
  rfl

private theorem isomorphismArrowNerveSource_comp_identity :
    isomorphismArrowNerveSource D ≫
        isomorphismArrowNerveIdentity D =
      nerveMapCross
        (isomorphismArrowSource D ⋙ isomorphismArrowIdentity D) := by
  ext a X
  rfl

private theorem nerveMapCross_isomorphismArrow_id :
    nerveMapCross (Functor.id (IsomorphismArrow D)) =
      𝟙 (nerve (IsomorphismArrow D)) := by
  ext a X
  rfl

/-- The identity-arrow contraction is a homotopy over the source nerve map. -/
noncomputable def isomorphismArrowNerveSourceHomotopyOver :
    SSet.HomotopyRelOver (isomorphismArrowNerveSource D)
      (isomorphismArrowNerveSource D ≫
        isomorphismArrowNerveIdentity D)
      (𝟙 (nerve (IsomorphismArrow D)))
      (⊥ : (nerve (IsomorphismArrow D)).Subcomplex) where
  toHomotopyRel :=
    { h := NatTrans.nerveHomotopyMapCross
        (isomorphismArrowSourceToIdentity (D := D))
      h₀ := by
        exact
          (NatTrans.nerveHomotopyCross
            (isomorphismArrowSourceToIdentity (D := D))).h₀.trans
              (isomorphismArrowNerveSource_comp_identity (D := D)).symm
      h₁ := by
        exact
          (NatTrans.nerveHomotopyCross
            (isomorphismArrowSourceToIdentity (D := D))).h₁.trans
              (nerveMapCross_isomorphismArrow_id (D := D))
      stationary := by
        intro n x hx t
        cases hx }
  over := by
    rw [isomorphismArrowNerveHomotopyMap_comp_source]
    simp only [Category.assoc, isomorphismArrowNerveIdentity_comp_source,
      Category.comp_id]

/-- The source nerve map is a split simplicial homotopy equivalence over
`nerve D`. -/
noncomputable def isomorphismArrowNerveSourceSplitHomotopyEquivOver :
    SSet.SplitHomotopyEquivOver (isomorphismArrowNerveSource D) where
  section_ := isomorphismArrowNerveIdentity D
  section_comp := isomorphismArrowNerveIdentity_comp_source (D := D)
  homotopyOver := isomorphismArrowNerveSourceHomotopyOver (D := D)

/-- Every base change of the source map from the isomorphism-arrow nerve is a
realization weak equivalence. -/
theorem isomorphismArrowNerveSource_baseChange_mem_realizationWeakEquivalences
    {X : SSet.{max u v}} (f : X ⟶ nerve D) :
    SSet.realizationWeakEquivalences
      (pullback.fst f (isomorphismArrowNerveSource D)) :=
  SSet.SplitHomotopyEquivOver.baseChange_fst_mem_realizationWeakEquivalences
    (isomorphismArrowNerveSourceSplitHomotopyEquivOver (D := D)) f

/-- The source and target chains of a chain of isomorphism arrows are
naturally isomorphic. -/
noncomputable def isomorphismArrowComposableIso
    {n : ℕ} (Z : ComposableArrows (IsomorphismArrow D) n) :
    ((isomorphismArrowSource D).mapComposableArrows n).obj Z ≅
      ((isomorphismArrowTarget D).mapComposableArrows n).obj Z :=
  ComposableArrows.isoMk
    (fun i ↦ @asIso _ _ _ _ (Z.obj i).hom (Z.obj i).prop)
    (fun i hi ↦ MorphismProperty.Arrow.w
      (Z.map' i (i + 1)))

/-- Assemble a chain of isomorphism arrows from two chains and an isomorphism
between them. -/
def isomorphismArrowComposableOfIso
    {n : ℕ} (X Y : ComposableArrows D n) (e : X ≅ Y) :
    ComposableArrows (IsomorphismArrow D) n where
  obj i :=
    { left := X.obj i
      right := Y.obj i
      hom := e.hom.app i
      prop := by infer_instance }
  map f :=
    { left := X.map f
      right := Y.map f
      w := e.hom.naturality f
      prop_hom_left := trivial
      prop_hom_right := trivial }
  map_id i := by
    apply MorphismProperty.Arrow.Hom.ext <;> simp
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext <;> simp

/-- An `n`-simplex in the nerve of the isomorphism-arrow category is exactly
two `n`-simplices in `nerve D` and a natural isomorphism between them. -/
noncomputable def isomorphismArrowNerveObjEquiv
    (a : SimplexCategoryᵒᵖ) :
    (nerve (IsomorphismArrow D)).obj a ≃
      Σ X Y : ComposableArrows D a.unop.len, X ≅ Y where
  toFun Z :=
    ⟨((isomorphismArrowSource D).mapComposableArrows a.unop.len).obj Z,
      ((isomorphismArrowTarget D).mapComposableArrows a.unop.len).obj Z,
      isomorphismArrowComposableIso D Z⟩
  invFun Z := isomorphismArrowComposableOfIso D Z.1 Z.2.1 Z.2.2
  left_inv Z := by
    rfl
  right_inv Z := by
    rcases Z with ⟨X, Y, e⟩
    let Z := isomorphismArrowComposableOfIso D X Y e
    have hX :
        ((isomorphismArrowSource D).mapComposableArrows a.unop.len).obj Z = X := by
      apply Functor.hext
      · intro i
        rfl
      · intro i j f
        rfl
    have hY :
        ((isomorphismArrowTarget D).mapComposableArrows a.unop.len).obj Z = Y := by
      apply Functor.hext
      · intro i
        rfl
      · intro i j f
        rfl
    apply Sigma.ext hX
    cases hX
    apply heq_of_eq
    apply Sigma.ext hY
    cases hY
    apply heq_of_eq
    apply Iso.ext
    ext i
    rfl

/-- The first chain extracted by `isomorphismArrowNerveObjEquiv` is the
source chain. -/
@[simp]
theorem isomorphismArrowNerveObjEquiv_source
    (a : SimplexCategoryᵒᵖ)
    (Z : (nerve (IsomorphismArrow D)).obj a) :
    (isomorphismArrowNerveObjEquiv (D := D) a Z).1 =
      ((isomorphismArrowSource D).mapComposableArrows a.unop.len).obj Z :=
  rfl

/-- The second chain extracted by `isomorphismArrowNerveObjEquiv` is the
target chain. -/
@[simp]
theorem isomorphismArrowNerveObjEquiv_target
    (a : SimplexCategoryᵒᵖ)
    (Z : (nerve (IsomorphismArrow D)).obj a) :
    (isomorphismArrowNerveObjEquiv (D := D) a Z).2.1 =
      ((isomorphismArrowTarget D).mapComposableArrows a.unop.len).obj Z :=
  rfl

section

-- The original qualified constructor name refers to the same canonical definition.
open CategoryTheory renaming
  isomorphismArrowNerveSourceSplitHomotopyEquivOver → isomorphismArrowNerveSource_splitHomotopyEquivOver
export _root_ (isomorphismArrowNerveSource_splitHomotopyEquivOver)

end

end CategoryTheory

end
