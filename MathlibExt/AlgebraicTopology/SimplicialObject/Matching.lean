/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Functorial matching objects of simplicial objects

The matching index in degree `n` consists of proper monomorphisms into `[n]`. Its structured-arrow
orientation makes a simplicial object covariant on the matching diagram. Matching objects, matching
maps, and matching arrows are functorial in the simplicial object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The matching index in degree `n`: proper monomorphisms `[m] ⟶ [n]`, with the
structured-arrow orientation covariant for simplicial objects. -/
abbrev matchingIndex (n : ℕ) : Type :=
  ObjectProperty.FullSubcategory
    (fun θ : StructuredArrow (op ⦋n⦌) (𝟭 SimplexCategoryᵒᵖ) =>
      Mono θ.hom.unop ∧ θ.right.unop.len < n)

/-- The matching index has finitely many objects. -/
noncomputable instance (n : ℕ) : Finite (matchingIndex n) := by
  let bound (a : matchingIndex n) :
      a.obj.right.unop.len + 1 ≤ n + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt a.property.2)
  let extend (a : matchingIndex n) (j : Fin (n + 1)) : Fin (n + 1) :=
    if h : j.val < a.obj.right.unop.len + 1 then
      a.obj.hom.unop.toOrderHom ⟨j.val, h⟩
    else
      0
  let encode (a : matchingIndex n) :
      Fin n × (Fin (n + 1) → Fin (n + 1)) :=
    (⟨a.obj.right.unop.len, a.property.2⟩, extend a)
  have encode_apply (a : matchingIndex n)
      (i : Fin (a.obj.right.unop.len + 1)) :
      (encode a).2 (Fin.castLE (bound a) i) =
        a.obj.hom.unop.toOrderHom i := by
    simp [encode, extend, Fin.val_castLE, i.isLt]
  have encode_injective : Function.Injective encode := by
    intro a b h
    have hlen : a.obj.right.unop.len = b.obj.right.unop.len :=
      congrArg (fun z => z.1.val) h
    have hright : a.obj.right = b.obj.right := by
      exact unop_injective (SimplexCategory.ext hlen)
    apply ObjectProperty.FullSubcategory.ext
    apply StructuredArrow.obj_ext a.obj b.obj hright
    apply Quiver.Hom.unop_inj
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    let ia : Fin (a.obj.right.unop.len + 1) :=
      ((eqToHom hright).unop).toOrderHom i
    have hcast : Fin.castLE (bound a) ia = Fin.castLE (bound b) i := by
      apply Fin.ext
      simp [ia, SimplexCategory.eqToHom_toOrderHom]
    have hfun := congrFun (congrArg (fun z => z.2) h)
      (Fin.castLE (bound b) i)
    change a.obj.hom.unop.toOrderHom ia =
      b.obj.hom.unop.toOrderHom i
    rw [← encode_apply a ia, hcast, hfun, encode_apply b i]
  exact Finite.of_injective encode encode_injective

/-- A morphism of the matching index is determined by its simplex map, so there are finitely
many morphisms between two objects. -/
instance (n : ℕ) (a b : matchingIndex n) : Finite (a ⟶ b) := by
  let projection : (a ⟶ b) →
      (Fin (b.obj.right.unop.len + 1) → Fin (a.obj.right.unop.len + 1)) :=
    fun f => f.hom.right.unop.toOrderHom
  apply Finite.of_injective projection
  intro f g h
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  exact h

/-- The matching index is a finite category, so matching objects exist in every category with
finite limits. -/
noncomputable instance matchingIndexFinCategory (n : ℕ) : FinCategory (matchingIndex n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- In degree `n`, the matching diagram is functorial in the simplicial object. -/
def matchingDiagramFunctor (n : ℕ) :
    SimplicialObject C ⥤ (matchingIndex n ⥤ C) where
  obj X :=
    { obj := fun a => X.obj a.obj.right
      map := fun {_ _} g => X.map g.hom.right
      map_id := by intro; simp
      map_comp := by intros; simp }
  map f :=
    { app := fun a => f.app a.obj.right
      naturality := by
        intro a b g
        exact f.naturality g.hom.right }
  map_id X := by
    apply NatTrans.ext
    funext a
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext a
    rfl

/-- The matching diagram of `X` in degree `n`. -/
abbrev matchingDiagram (X : SimplicialObject C) (n : ℕ) :
    matchingIndex n ⥤ C :=
  (matchingDiagramFunctor n).obj X

/-- A simplicial morphism acts on a matching diagram by its component at the source degree of the
indexing monomorphism. -/
@[simp]
theorem matchingDiagramFunctor_map_app (n : ℕ)
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (a : matchingIndex n) :
    ((matchingDiagramFunctor (C := C) n).map f).app a =
      f.app a.obj.right :=
  rfl

/-- The canonical cone from `X` in degree `n` to its matching diagram. -/
def matchingCone (X : SimplicialObject C) (n : ℕ) :
    Cone (matchingDiagram X n) where
  pt := X.obj (op ⦋n⦌)
  π :=
    { app := fun a => X.map a.obj.hom
      naturality := by
        intro a b g
        change 𝟙 _ ≫ X.map b.obj.hom =
          X.map a.obj.hom ≫ X.map g.hom.right
        rw [Category.id_comp, ← X.map_comp]
        apply X.congr_map
        exact (StructuredArrow.w g.hom).symm }

/-- The matching object in degree `n`, functorial in the simplicial object. -/
noncomputable def matchingObjectFunctor (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    SimplicialObject C ⥤ C :=
  matchingDiagramFunctor n ⋙ lim

/-- The matching object of `X` in degree `n`. -/
noncomputable abbrev matchingObject (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] : C :=
  (matchingObjectFunctor n).obj X

/-- The canonical projection from the matching object to a lower simplicial degree. -/
noncomputable def matchingπ (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] (a : matchingIndex n) :
    matchingObject X n ⟶ X.obj a.obj.right :=
  limit.π (matchingDiagram X n) a

set_option backward.isDefEq.respectTransparency false in
/-- Matching projections commute with a simplicial morphism. -/
@[reassoc]
theorem matchingObjectFunctor_map_π (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (a : matchingIndex n) :
    (matchingObjectFunctor n).map f ≫ matchingπ Y n a =
      matchingπ X n a ≫ f.app a.obj.right := by
  simpa only [matchingObjectFunctor, matchingπ, Functor.comp_map,
    matchingDiagramFunctor_map_app] using
    limit.map_π ((matchingDiagramFunctor n).map f) a

/-- The matching map of `X` in degree `n`. -/
noncomputable def matchingMap (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    X.obj (op ⦋n⦌) ⟶ matchingObject X n :=
  limit.lift (matchingDiagram X n) (matchingCone X n)

set_option backward.isDefEq.respectTransparency false in
/-- The matching map followed by a canonical projection is the corresponding simplicial structure
map. -/
@[reassoc]
theorem matchingMap_π (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] (a : matchingIndex n) :
    matchingMap X n ≫ matchingπ X n a = X.map a.obj.hom := by
  simpa only [matchingMap, matchingπ, matchingCone] using
    limit.lift_π (matchingCone X n) a

set_option backward.isDefEq.respectTransparency false in
/-- Matching maps form a natural transformation from evaluation in degree `n` to matching
objects. -/
noncomputable def matchingMapNatTrans (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋n⦌) ⟶
      matchingObjectFunctor n where
  app X := matchingMap X n
  naturality X Y f := by
    apply limit.hom_ext
    intro a
    change (f.app (op ⦋n⦌) ≫ matchingMap Y n) ≫
        matchingπ Y n a =
      (matchingMap X n ≫
          (matchingObjectFunctor n).map f) ≫ matchingπ Y n a
    rw [Category.assoc, matchingMap_π, Category.assoc,
      matchingObjectFunctor_map_π, ← Category.assoc, matchingMap_π]
    exact (f.naturality a.obj.hom).symm

/-- Naturality of matching maps. -/
@[reassoc]
theorem matchingMap_naturality (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ matchingMap Y n =
      matchingMap X n ≫ (matchingObjectFunctor n).map f :=
  (matchingMapNatTrans n).naturality f

/-- Matching maps form a functor to the arrow category. -/
noncomputable def matchingMapArrowFunctor (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    SimplicialObject C ⥤ Arrow C where
  obj X := Arrow.mk (matchingMap X n)
  map f := Arrow.homMk (f.app (op ⦋n⦌))
    ((matchingObjectFunctor n).map f) (matchingMap_naturality n f)
  map_id X := by
    apply Arrow.hom_ext
    · rfl
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · simp

/-- The object of the matching-arrow functor is the matching map. -/
@[simp]
theorem matchingMapArrowFunctor_obj (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    (X : SimplicialObject C) :
    (matchingMapArrowFunctor n).obj X =
      Arrow.mk (matchingMap X n) :=
  rfl

/-- A simplicial isomorphism induces the canonical isomorphism of matching arrows. -/
noncomputable def matchingMapArrowIso (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {X Y : SimplicialObject C} (e : X ≅ Y) :
    Arrow.mk (matchingMap X n) ≅ Arrow.mk (matchingMap Y n) :=
  (matchingMapArrowFunctor n).mapIso e

/-- In degree zero, the matching object is terminal. -/
noncomputable def matchingObjectZeroIso
    [HasTerminal C]
    [HasLimitsOfShape (matchingIndex 0) C]
    (X : SimplicialObject C) :
    matchingObject X 0 ≅ ⊤_ C := by
  let _ : IsEmpty (matchingIndex 0) :=
    ⟨fun a => (Nat.not_lt_zero _ a.property.2).elim⟩
  let emptyCone (Y : C) : Cone (matchingDiagram X 0) :=
    { pt := Y
      π :=
        { app := fun a => isEmptyElim a
          naturality := by
            intro a
            exact isEmptyElim a } }
  let hM : IsTerminal (matchingObject X 0) :=
    IsTerminal.ofUniqueHom
      (fun Y => limit.lift (matchingDiagram X 0) (emptyCone Y))
      (fun _ _ => by
        apply limit.hom_ext
        intro a
        exact isEmptyElim a)
  exact hM.uniqueUpToIso terminalIsTerminal

/-- In degree zero, the matching arrow is the canonical map to the terminal object. -/
noncomputable def matchingMapZeroArrowIso
    [HasTerminal C]
    [HasLimitsOfShape (matchingIndex 0) C]
    (X : SimplicialObject C) :
    (matchingMapArrowFunctor 0).obj X ≅
      Arrow.mk (terminal.from (X.obj (op ⦋0⦌))) := by
  change Arrow.mk (matchingMap X 0) ≅
    Arrow.mk (terminal.from (X.obj (op ⦋0⦌)))
  exact Arrow.isoMk (Iso.refl _) (matchingObjectZeroIso X)
    (terminalIsTerminal.hom_ext _ _)

end CategoryTheory.SimplicialObject
