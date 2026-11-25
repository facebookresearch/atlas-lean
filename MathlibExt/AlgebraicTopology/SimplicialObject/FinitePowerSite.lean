/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The ordered finite simplex-power site

The pointwise opposite of a finite simplex family is equivalent to the opposite of its
source category. The resulting diagram equivalence precomposes with the inverse. Its native
unit and counit compare whole original arrows and their squares.

The zero and one coordinate cases, ordered head/tail split, and product with an arbitrary
category retain their original operator actions. The constructions work in any coefficient
category, in particular in simplicial sets of an arbitrary fixed universe.

The source conventions are those of Johnson-Freyd–Scheimbauer, Examples A.10–A.11,
printed pp. 55–56. The finite-Pi opposite and currying constructions use native Mathlib kernels.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe v u vG uG

open Opposite
open scoped CategoryTheory.Prod Simplicial

namespace CategoryTheory.FinitePowerSite

/-- The ordered, unopposited finite simplex source. -/
abbrev Source (n : ℕ) := Fin n → SimplexCategory

/-- The ordered, pointwise-opposited diagram index. -/
abbrev Index (n : ℕ) := Fin n → SimplexCategoryᵒᵖ

/-- The all-zero source object, including the empty tuple at height zero. -/
def zeroTuple (n : ℕ) : Source n := fun _ => ⦋0⦌

/-- The canonical family of original simplex operators to the all-zero object. -/
def toZero {n : ℕ} (a : Source n) : a ⟶ zeroTuple n :=
  fun i => SimplexCategory.isTerminalZero.from (a i)

/-- The all-zero object is terminal at every finite height. -/
def zeroIsTerminal (n : ℕ) : Limits.IsTerminal (zeroTuple n) :=
  Limits.IsTerminal.ofUniqueHom toZero (by
    intro a f
    funext i
    exact SimplexCategory.isTerminalZero.hom_ext _ _)

/-- The original source opposite is equivalent to pointwise opposite coordinates. -/
def sourceOpEquiv (n : ℕ) : (Source n)ᵒᵖ ≌ Index n :=
  (((piEquivalenceFunctorDiscrete (Fin n) SimplexCategory).op.trans
    (Functor.opUnopEquiv (Discrete (Fin n)) SimplexCategory)).trans
    (((Discrete.opposite (Fin n)).symm.congrLeft).symm)).trans
    (piEquivalenceFunctorDiscrete (Fin n) SimplexCategoryᵒᵖ).symm

theorem sourceOpEquiv_functor_obj (n : ℕ) (a : Source n) :
    (sourceOpEquiv n).functor.obj (op a) = fun i => op (a i) := rfl

theorem sourceOpEquiv_functor_map (n : ℕ) {a b : Source n} (f : op a ⟶ op b) :
    HEq ((sourceOpEquiv n).functor.map f) (fun i => (f.unop i).op) := by
  cases sourceOpEquiv_functor_obj n a
  cases sourceOpEquiv_functor_obj n b
  exact heq_of_eq (by funext i; rfl)

theorem sourceOpEquiv_inverse_obj (n : ℕ) (x : Index n) :
    (sourceOpEquiv n).inverse.obj x = op (fun i => (x i).unop) := rfl

/-- The inverse takes the opposite of the whole original family of unopposited maps. -/
theorem sourceOpEquiv_inverse_map (n : ℕ) {x y : Index n} (f : x ⟶ y) :
    HEq ((sourceOpEquiv n).inverse.map f)
      (Quiver.Hom.op (X := fun i => (y i).unop) (Y := fun i => (x i).unop)
        (fun i => (f i).unop)) := by
  cases sourceOpEquiv_inverse_obj n x
  cases sourceOpEquiv_inverse_obj n y
  rfl

theorem sourceOpEquiv_unit_hom (n : ℕ) (a : (Source n)ᵒᵖ) :
    (sourceOpEquiv n).unitIso.hom.app a = 𝟙 a := by
  ext i
  rfl

theorem sourceOpEquiv_unit_inv (n : ℕ) (a : (Source n)ᵒᵖ) :
    (sourceOpEquiv n).unitIso.inv.app a = 𝟙 a := by
  ext i
  rfl

theorem sourceOpEquiv_counit_hom (n : ℕ) (x : Index n) :
    (sourceOpEquiv n).counitIso.hom.app x = 𝟙 x := by
  ext i
  rfl

theorem sourceOpEquiv_counit_inv (n : ℕ) (x : Index n) :
    (sourceOpEquiv n).counitIso.inv.app x = 𝟙 x := by
  ext i
  rfl

/-- Transport from original source presheaves to diagrams precomposes with the inverse. -/
def diagramEquiv (n : ℕ) (C : Type u) [Category.{v} C] :
    ((Source n)ᵒᵖ ⥤ C) ≌ (Index n ⥤ C) :=
  (sourceOpEquiv n).congrLeft

section Diagrams

variable {C : Type u} [Category.{v} C]

theorem diagramEquiv_functor_obj (n : ℕ) (X : (Source n)ᵒᵖ ⥤ C) (x : Index n) :
    ((diagramEquiv n C).functor.obj X).obj x = X.obj ((sourceOpEquiv n).inverse.obj x) := rfl

theorem diagramEquiv_functor_obj_map (n : ℕ) (X : (Source n)ᵒᵖ ⥤ C)
    {x y : Index n} (f : x ⟶ y) :
    ((diagramEquiv n C).functor.obj X).map f = X.map ((sourceOpEquiv n).inverse.map f) := rfl

theorem diagramEquiv_functor_map_app (n : ℕ) {X Y : (Source n)ᵒᵖ ⥤ C}
    (f : X ⟶ Y) (x : Index n) :
    ((diagramEquiv n C).functor.map f).app x = f.app ((sourceOpEquiv n).inverse.obj x) := rfl

theorem diagramEquiv_inverse_obj (n : ℕ) (X : Index n ⥤ C) (a : (Source n)ᵒᵖ) :
    ((diagramEquiv n C).inverse.obj X).obj a = X.obj ((sourceOpEquiv n).functor.obj a) := rfl

theorem diagramEquiv_inverse_obj_map (n : ℕ) (X : Index n ⥤ C)
    {a b : (Source n)ᵒᵖ} (f : a ⟶ b) :
    ((diagramEquiv n C).inverse.obj X).map f = X.map ((sourceOpEquiv n).functor.map f) := rfl

theorem diagramEquiv_inverse_map_app (n : ℕ) {X Y : Index n ⥤ C}
    (f : X ⟶ Y) (a : (Source n)ᵒᵖ) :
    ((diagramEquiv n C).inverse.map f).app a = f.app ((sourceOpEquiv n).functor.obj a) := rfl

theorem diagramEquiv_unit_hom_app (n : ℕ) (X : (Source n)ᵒᵖ ⥤ C) (a : (Source n)ᵒᵖ) :
    ((diagramEquiv n C).unitIso.hom.app X).app a =
      X.map ((sourceOpEquiv n).unitIso.hom.app a) := by
  change ((sourceOpEquiv n).funInvIdAssoc X).inv.app a =
    X.map ((sourceOpEquiv n).unit.app a)
  exact Equivalence.funInvIdAssoc_inv_app (sourceOpEquiv n) X a

theorem diagramEquiv_unit_inv_app (n : ℕ) (X : (Source n)ᵒᵖ ⥤ C) (a : (Source n)ᵒᵖ) :
    ((diagramEquiv n C).unitIso.inv.app X).app a =
      X.map ((sourceOpEquiv n).unitIso.inv.app a) := by
  change ((sourceOpEquiv n).funInvIdAssoc X).hom.app a =
    X.map ((sourceOpEquiv n).unitInv.app a)
  exact Equivalence.funInvIdAssoc_hom_app (sourceOpEquiv n) X a

theorem diagramEquiv_counit_hom_app (n : ℕ) (X : Index n ⥤ C) (x : Index n) :
    ((diagramEquiv n C).counitIso.hom.app X).app x =
      X.map ((sourceOpEquiv n).counitIso.hom.app x) := by
  change ((sourceOpEquiv n).invFunIdAssoc X).hom.app x =
    X.map ((sourceOpEquiv n).counit.app x)
  exact Equivalence.invFunIdAssoc_hom_app (sourceOpEquiv n) X x

theorem diagramEquiv_counit_inv_app (n : ℕ) (X : Index n ⥤ C) (x : Index n) :
    ((diagramEquiv n C).counitIso.inv.app X).app x =
      X.map ((sourceOpEquiv n).counitIso.inv.app x) := by
  change ((sourceOpEquiv n).invFunIdAssoc X).inv.app x =
    X.map ((sourceOpEquiv n).counitInv.app x)
  exact Equivalence.invFunIdAssoc_inv_app (sourceOpEquiv n) X x

/-- The source unit compares the same original arrow, including both endpoints. -/
def sourceArrowUnitIso (n : ℕ) (a : Arrow ((Source n)ᵒᵖ ⥤ C)) :
    a ≅ (diagramEquiv n C).inverse.mapArrow.obj
      ((diagramEquiv n C).functor.mapArrow.obj a) :=
  (Functor.mapArrowEquivalence (diagramEquiv n C)).unitIso.app a

/-- The target counit recovers the same original arrow and its original maps. -/
def targetArrowCounitIso (n : ℕ) (a : Arrow (Index n ⥤ C)) :
    (diagramEquiv n C).functor.mapArrow.obj
      ((diagramEquiv n C).inverse.mapArrow.obj a) ≅ a :=
  (Functor.mapArrowEquivalence (diagramEquiv n C)).counitIso.app a

theorem sourceArrowUnitIso_hom_fields (n : ℕ) (a : Arrow ((Source n)ᵒᵖ ⥤ C)) :
    (sourceArrowUnitIso n a).hom.left = (diagramEquiv n C).unitIso.hom.app a.left ∧
    (sourceArrowUnitIso n a).hom.right = (diagramEquiv n C).unitIso.hom.app a.right := ⟨rfl, rfl⟩

theorem sourceArrowUnitIso_inv_fields (n : ℕ) (a : Arrow ((Source n)ᵒᵖ ⥤ C)) :
    (sourceArrowUnitIso n a).inv.left = (diagramEquiv n C).unitIso.inv.app a.left ∧
    (sourceArrowUnitIso n a).inv.right = (diagramEquiv n C).unitIso.inv.app a.right := ⟨rfl, rfl⟩

theorem targetArrowCounitIso_hom_fields (n : ℕ) (a : Arrow (Index n ⥤ C)) :
    (targetArrowCounitIso n a).hom.left = (diagramEquiv n C).counitIso.hom.app a.left ∧
    (targetArrowCounitIso n a).hom.right =
        (diagramEquiv n C).counitIso.hom.app a.right := ⟨rfl, rfl⟩

theorem targetArrowCounitIso_inv_fields (n : ℕ) (a : Arrow (Index n ⥤ C)) :
    (targetArrowCounitIso n a).inv.left = (diagramEquiv n C).counitIso.inv.app a.left ∧
    (targetArrowCounitIso n a).inv.right =
        (diagramEquiv n C).counitIso.inv.app a.right := ⟨rfl, rfl⟩

theorem sourceArrowUnitIso_hom_square (n : ℕ) (a : Arrow ((Source n)ᵒᵖ ⥤ C)) :
    a.hom ≫ (sourceArrowUnitIso n a).hom.right =
      (sourceArrowUnitIso n a).hom.left ≫
        (diagramEquiv n C).inverse.map ((diagramEquiv n C).functor.map a.hom) :=
  (sourceArrowUnitIso n a).hom.w.symm

theorem sourceArrowUnitIso_inv_square (n : ℕ) (a : Arrow ((Source n)ᵒᵖ ⥤ C)) :
    (diagramEquiv n C).inverse.map ((diagramEquiv n C).functor.map a.hom) ≫
      (sourceArrowUnitIso n a).inv.right = (sourceArrowUnitIso n a).inv.left ≫ a.hom :=
  (sourceArrowUnitIso n a).inv.w.symm

theorem targetArrowCounitIso_hom_square (n : ℕ) (a : Arrow (Index n ⥤ C)) :
    (diagramEquiv n C).functor.map ((diagramEquiv n C).inverse.map a.hom) ≫
      (targetArrowCounitIso n a).hom.right = (targetArrowCounitIso n a).hom.left ≫ a.hom :=
  (targetArrowCounitIso n a).hom.w.symm

theorem targetArrowCounitIso_inv_square (n : ℕ) (a : Arrow (Index n ⥤ C)) :
    a.hom ≫ (targetArrowCounitIso n a).inv.right =
      (targetArrowCounitIso n a).inv.left ≫
        (diagramEquiv n C).functor.map ((diagramEquiv n C).inverse.map a.hom) :=
  (targetArrowCounitIso n a).inv.w.symm

theorem sourceArrowUnitIso_naturality (n : ℕ) {a b : Arrow ((Source n)ᵒᵖ ⥤ C)} (f : a ⟶ b) :
    f ≫ (sourceArrowUnitIso n b).hom = (sourceArrowUnitIso n a).hom ≫
      (diagramEquiv n C).inverse.mapArrow.map ((diagramEquiv n C).functor.mapArrow.map f) :=
  (Functor.mapArrowEquivalence (diagramEquiv n C)).unitIso.hom.naturality f

theorem targetArrowCounitIso_naturality (n : ℕ) {a b : Arrow (Index n ⥤ C)} (f : a ⟶ b) :
    (diagramEquiv n C).functor.mapArrow.map ((diagramEquiv n C).inverse.mapArrow.map f) ≫
      (targetArrowCounitIso n b).hom = (targetArrowCounitIso n a).hom ≫ f :=
  (Functor.mapArrowEquivalence (diagramEquiv n C)).counitIso.hom.naturality f

end Diagrams

/-- The empty finite index is a terminal category, with its unique empty coordinate family. -/
def zeroIndexEquiv : Index 0 ≌ Discrete PUnit.{1} where
  functor :=
    { obj := fun _ => ⟨PUnit.unit⟩
      map := fun _ => 𝟙 _ }
  inverse :=
    { obj := fun _ i => Fin.elim0 i
      map := fun _ i => Fin.elim0 i
      map_id := fun _ => by funext i; exact Fin.elim0 i
      map_comp := fun _ _ => by funext i; exact Fin.elim0 i }
  unitIso := NatIso.ofComponents (fun a => eqToIso (Subsingleton.elim a _))
    (by intro a b f; funext i; exact Fin.elim0 i)
  counitIso := NatIso.ofComponents (fun x => eqToIso (Subsingleton.elim _ x))
    (by intro a b f; exact Subsingleton.elim _ _)
  functor_unitIso_comp := fun _ => Subsingleton.elim _ _

/-- The single coordinate is evaluated at zero, with the constant family as inverse. -/
def oneIndexEquiv : Index 1 ≌ SimplexCategoryᵒᵖ :=
  (piEquivalenceFunctorDiscrete (Fin 1) SimplexCategoryᵒᵖ).trans
    (((Discrete.equivalence finOneEquiv).congrLeft).trans
      (Functor.equiv (C := SimplexCategoryᵒᵖ)))

theorem oneIndexEquiv_functor_obj (a : Index 1) : oneIndexEquiv.functor.obj a = a 0 := rfl

theorem oneIndexEquiv_inverse_obj (x : SimplexCategoryᵒᵖ) :
    oneIndexEquiv.inverse.obj x = fun _ => x := rfl

theorem oneIndexEquiv_functor_map {a b : Index 1} (f : a ⟶ b) :
    HEq (oneIndexEquiv.functor.map f) (f 0) := by rfl

theorem oneIndexEquiv_inverse_map {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    HEq (oneIndexEquiv.inverse.map f) (fun _ : Fin 1 => f) := by rfl

/-- The first coordinate precedes its finite ordered tail. -/
def orderedSplitIndex (n : ℕ) : Index (n + 1) ≌ SimplexCategoryᵒᵖ × Index n :=
  (Pi.equivalenceOfEquiv (C := fun _ : Option (Fin n) => SimplexCategoryᵒᵖ)
    (finSuccEquiv n)).trans
    (Pi.optionEquivalence (fun _ : Option (Fin n) => SimplexCategoryᵒᵖ))

theorem orderedSplitIndex_functor_obj (n : ℕ) (a : Index (n + 1)) :
    (orderedSplitIndex n).functor.obj a = (a 0, fun i => a i.succ) := by
  simp only [orderedSplitIndex, Pi.equivalenceOfEquiv, Pi.eqToEquivalence, Functor.pi'_eval,
    Pi.optionEquivalence, Equivalence.trans_functor, eq_rec_constant, Equivalence.refl_functor,
    Functor.comp_obj, Functor.prod'_obj, Pi.eval_obj, Functor.pi'_obj, finSuccEquiv_symm_none,
    Functor.id_obj, Prod.mk.injEq, true_and]
  funext i
  change a ((finSuccEquiv n).symm (some i)) = a i.succ
  rw [finSuccEquiv_symm_some]

theorem orderedSplitIndex_inverse_obj (n : ℕ) (x : SimplexCategoryᵒᵖ) (a : Index n) :
    (orderedSplitIndex n).inverse.obj (x, a) = Fin.cases x a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [orderedSplitIndex, Pi.equivalenceOfEquiv, Pi.optionEquivalence]
  · simp [orderedSplitIndex, Pi.equivalenceOfEquiv, Pi.optionEquivalence]

theorem orderedSplitIndex_functor_map (n : ℕ) {a b : Index (n + 1)} (f : a ⟶ b) :
    HEq ((orderedSplitIndex n).functor.map f)
      (Prod.mkHom (C := SimplexCategoryᵒᵖ) (D := Index n)
        (f 0) (fun i : Fin n => f i.succ)) := by
  cases orderedSplitIndex_functor_obj n a
  cases orderedSplitIndex_functor_obj n b
  apply heq_of_eq
  apply Prod.hom_ext
  · apply eq_of_heq
    change HEq (f ((finSuccEquiv n).symm none)) (f 0)
    rw [finSuccEquiv_symm_none]
  · funext i
    apply eq_of_heq
    change HEq (f ((finSuccEquiv n).symm (some i))) (f i.succ)
    rw [finSuccEquiv_symm_some]

/-- The inverse ordered split uses the given head map at coordinate zero and
the given tail maps at their original successor coordinates. -/
theorem orderedSplitIndex_inverse_map (n : ℕ) {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y)
    {a b : Index n} (g : a ⟶ b) :
    HEq ((orderedSplitIndex n).inverse.map (f ×ₘ g))
      (show (Fin.cases X a : Index (n + 1)) ⟶
        (Fin.cases Y b : Index (n + 1)) from fun i => Fin.cases f g i) := by
  apply Function.hfunext rfl
  intro i j h
  cases h
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change HEq
      (((Pi.optionEquivalence (fun _ : Option (Fin n) => SimplexCategoryᵒᵖ)).inverse.map
        (f ×ₘ g)) ((finSuccEquiv n) j.succ)) (g j)
    rw [finSuccEquiv_succ]
    rfl

theorem orderedSplitTwo_first (x y : SimplexCategoryᵒᵖ) :
    ((orderedSplitIndex 1).functor.obj (Fin.cases x (fun _ : Fin 1 => y))).1 = x := by
  rw [orderedSplitIndex_functor_obj]
  rfl

theorem orderedSplitTwo_second (x y : SimplexCategoryᵒᵖ) :
    ((orderedSplitIndex 1).functor.obj (Fin.cases x (fun _ : Fin 1 => y))).2 0 = y := by
  rw [orderedSplitIndex_functor_obj]
  rfl

/-- Empty-index diagrams are the coefficient category itself. -/
def zeroDiagramEquiv (C : Type u) [Category.{v} C] : (Index 0 ⥤ C) ≌ C :=
  zeroIndexEquiv.congrLeft.trans Functor.equiv

/-- One-coordinate diagrams are simplicial objects in the coefficient category. -/
def oneDiagramEquiv (C : Type u) [Category.{v} C] :
    (Index 1 ⥤ C) ≌ (SimplexCategoryᵒᵖ ⥤ C) := oneIndexEquiv.congrLeft

/-- Ordered currying takes the first categorical direction as the outer coordinate. -/
def orderedSplitDiagram (n : ℕ) (C : Type u) [Category.{v} C] :
    (Index (n + 1) ⥤ C) ≌ (SimplexCategoryᵒᵖ ⥤ Index n ⥤ C) :=
  (orderedSplitIndex n).congrLeft.trans
    (Functor.currying (C := SimplexCategoryᵒᵖ) (D := Index n) (E := C)).symm

section LowDimensionalDiagrams

variable {C : Type u} [Category.{v} C]

theorem zeroDiagramEquiv_functor_obj (X : Index 0 ⥤ C) :
    (zeroDiagramEquiv C).functor.obj X = X.obj (fun i => Fin.elim0 i) := rfl

theorem zeroDiagramEquiv_functor_map {X Y : Index 0 ⥤ C} (f : X ⟶ Y) :
    (zeroDiagramEquiv C).functor.map f = f.app (fun i => Fin.elim0 i) := rfl

theorem zeroDiagramEquiv_inverse_obj (X : C) (a : Index 0) :
    ((zeroDiagramEquiv C).inverse.obj X).obj a = X := rfl

theorem zeroDiagramEquiv_inverse_obj_map (X : C) {a b : Index 0} (f : a ⟶ b) :
    ((zeroDiagramEquiv C).inverse.obj X).map f = 𝟙 X := rfl

theorem zeroDiagramEquiv_inverse_map_app {X Y : C} (f : X ⟶ Y) (a : Index 0) :
    ((zeroDiagramEquiv C).inverse.map f).app a = f := rfl

theorem oneDiagramEquiv_functor_obj (X : Index 1 ⥤ C) (a : SimplexCategoryᵒᵖ) :
    ((oneDiagramEquiv C).functor.obj X).obj a = X.obj (fun _ => a) := rfl

theorem oneDiagramEquiv_functor_obj_map (X : Index 1 ⥤ C)
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((oneDiagramEquiv C).functor.obj X).map f = X.map (fun _ : Fin 1 => f) := rfl

theorem oneDiagramEquiv_functor_map_app {X Y : Index 1 ⥤ C} (f : X ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    ((oneDiagramEquiv C).functor.map f).app a = f.app (fun _ => a) := rfl

theorem oneDiagramEquiv_inverse_obj (X : SimplexCategoryᵒᵖ ⥤ C) (a : Index 1) :
    ((oneDiagramEquiv C).inverse.obj X).obj a = X.obj (a 0) := rfl

theorem oneDiagramEquiv_inverse_obj_map (X : SimplexCategoryᵒᵖ ⥤ C)
    {a b : Index 1} (f : a ⟶ b) :
    ((oneDiagramEquiv C).inverse.obj X).map f = X.map (f 0) := rfl

theorem oneDiagramEquiv_inverse_map_app {X Y : SimplexCategoryᵒᵖ ⥤ C}
    (f : X ⟶ Y) (a : Index 1) :
    ((oneDiagramEquiv C).inverse.map f).app a = f.app (a 0) := rfl

theorem orderedSplitDiagram_functor_obj (n : ℕ) (X : Index (n + 1) ⥤ C)
    (x : SimplexCategoryᵒᵖ) (a : Index n) :
    (((orderedSplitDiagram n C).functor.obj X).obj x).obj a =
      X.obj ((orderedSplitIndex n).inverse.obj (x, a)) := rfl

theorem orderedSplitDiagram_functor_inner_map (n : ℕ) (X : Index (n + 1) ⥤ C)
    (x : SimplexCategoryᵒᵖ) {a b : Index n} (f : a ⟶ b) :
    (((orderedSplitDiagram n C).functor.obj X).obj x).map f =
      X.map ((orderedSplitIndex n).inverse.map (𝟙 x ×ₘ f)) := rfl

theorem orderedSplitDiagram_functor_outer_map (n : ℕ) (X : Index (n + 1) ⥤ C)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (a : Index n) :
    (((orderedSplitDiagram n C).functor.obj X).map f).app a =
      X.map ((orderedSplitIndex n).inverse.map (f ×ₘ 𝟙 a)) := rfl

theorem orderedSplitDiagram_functor_map_app (n : ℕ) {X Y : Index (n + 1) ⥤ C}
    (f : X ⟶ Y) (x : SimplexCategoryᵒᵖ) (a : Index n) :
    (((orderedSplitDiagram n C).functor.map f).app x).app a =
      f.app ((orderedSplitIndex n).inverse.obj (x, a)) := rfl

theorem orderedSplitDiagram_inverse_obj (n : ℕ) (X : SimplexCategoryᵒᵖ ⥤ Index n ⥤ C)
    (a : Index (n + 1)) :
    ((orderedSplitDiagram n C).inverse.obj X).obj a =
      (X.obj (a 0)).obj (fun i => a i.succ) := by
  change (X.obj ((orderedSplitIndex n).functor.obj a).1).obj
    ((orderedSplitIndex n).functor.obj a).2 = _
  rw [orderedSplitIndex_functor_obj]

theorem orderedSplitDiagram_inverse_obj_map (n : ℕ)
    (X : SimplexCategoryᵒᵖ ⥤ Index n ⥤ C) {a b : Index (n + 1)} (f : a ⟶ b) :
    ((orderedSplitDiagram n C).inverse.obj X).map f =
      (X.map ((orderedSplitIndex n).functor.map f).1).app
        ((orderedSplitIndex n).functor.obj a).2 ≫
      (X.obj ((orderedSplitIndex n).functor.obj b).1).map
        ((orderedSplitIndex n).functor.map f).2 := rfl

theorem orderedSplitDiagram_inverse_map_app (n : ℕ)
    {X Y : SimplexCategoryᵒᵖ ⥤ Index n ⥤ C} (f : X ⟶ Y) (a : Index (n + 1)) :
    HEq (((orderedSplitDiagram n C).inverse.map f).app a)
      ((f.app (a 0)).app (fun i => a i.succ)) := by
  change HEq ((f.app ((orderedSplitIndex n).functor.obj a).1).app
    ((orderedSplitIndex n).functor.obj a).2) _
  rw [orderedSplitIndex_functor_obj]

end LowDimensionalDiagrams

/-- The single-opposite product transport for an arbitrary actual covariant factor. -/
def productSourceOpEquiv (n : ℕ) (G : Type uG) [Category.{vG} G] :
    (Gᵒᵖ × Source n)ᵒᵖ ≌ G × Index n :=
  (prodOpEquiv Gᵒᵖ (D := Source n)).trans ((opOpEquivalence G).prod (sourceOpEquiv n))

/-- The same original product site transport in any coefficient universe. -/
def productDiagramEquiv (n : ℕ) (G : Type uG) [Category.{vG} G]
    (C : Type u) [Category.{v} C] :
    ((Gᵒᵖ × Source n)ᵒᵖ ⥤ C) ≌ ((G × Index n) ⥤ C) :=
  (productSourceOpEquiv n G).congrLeft

section Product

variable {G : Type uG} [Category.{vG} G] {C : Type u} [Category.{v} C]

theorem productSourceOpEquiv_functor_obj (n : ℕ) (g : G) (a : Source n) :
    (productSourceOpEquiv n G).functor.obj (op (op g, a)) = (g, fun i => op (a i)) := rfl

theorem productSourceOpEquiv_inverse_obj (n : ℕ) (g : G) (a : Index n) :
    (productSourceOpEquiv n G).inverse.obj (g, a) = op (op g, fun i => (a i).unop) := rfl

theorem productSourceOpEquiv_functor_map (n : ℕ) {g h : G} {a b : Source n}
    (f : op (op g, a) ⟶ op (op h, b)) :
    HEq ((productSourceOpEquiv n G).functor.map f)
      (Prod.mkHom (C := G) (D := Index n)
        f.unop.1.unop (fun i : Fin n => (f.unop.2 i).op)) := by rfl

/-- The inverse takes one outer opposite of the original factor map and coordinate family. -/
theorem productSourceOpEquiv_inverse_map (n : ℕ) {g h : G} (f : g ⟶ h)
    {a b : Index n} (k : a ⟶ b) :
    HEq ((productSourceOpEquiv n G).inverse.map (f ×ₘ k))
      (Quiver.Hom.op (X := (op h, fun i => (b i).unop))
        (Y := (op g, fun i => (a i).unop)) (f.op ×ₘ (fun i => (k i).unop))) := by rfl

theorem productDiagramEquiv_functor_obj (n : ℕ) (X : (Gᵒᵖ × Source n)ᵒᵖ ⥤ C)
    (x : G × Index n) :
    ((productDiagramEquiv n G C).functor.obj X).obj x =
      X.obj ((productSourceOpEquiv n G).inverse.obj x) := rfl

theorem productDiagramEquiv_functor_obj_map (n : ℕ) (X : (Gᵒᵖ × Source n)ᵒᵖ ⥤ C)
    {x y : G × Index n} (f : x ⟶ y) :
    ((productDiagramEquiv n G C).functor.obj X).map f =
      X.map ((productSourceOpEquiv n G).inverse.map f) := rfl

theorem productDiagramEquiv_functor_map_app (n : ℕ)
    {X Y : (Gᵒᵖ × Source n)ᵒᵖ ⥤ C} (f : X ⟶ Y) (x : G × Index n) :
    ((productDiagramEquiv n G C).functor.map f).app x =
      f.app ((productSourceOpEquiv n G).inverse.obj x) := rfl

theorem productDiagramEquiv_inverse_obj (n : ℕ) (X : (G × Index n) ⥤ C)
    (x : (Gᵒᵖ × Source n)ᵒᵖ) :
    ((productDiagramEquiv n G C).inverse.obj X).obj x =
      X.obj ((productSourceOpEquiv n G).functor.obj x) := rfl

theorem productDiagramEquiv_inverse_obj_map (n : ℕ) (X : (G × Index n) ⥤ C)
    {x y : (Gᵒᵖ × Source n)ᵒᵖ} (f : x ⟶ y) :
    ((productDiagramEquiv n G C).inverse.obj X).map f =
      X.map ((productSourceOpEquiv n G).functor.map f) := rfl

theorem productDiagramEquiv_inverse_map_app (n : ℕ) {X Y : (G × Index n) ⥤ C}
    (f : X ⟶ Y) (x : (Gᵒᵖ × Source n)ᵒᵖ) :
    ((productDiagramEquiv n G C).inverse.map f).app x =
      f.app ((productSourceOpEquiv n G).functor.obj x) := rfl

theorem productDiagramEquiv_unit_hom_app (n : ℕ) (X : (Gᵒᵖ × Source n)ᵒᵖ ⥤ C)
    (x : (Gᵒᵖ × Source n)ᵒᵖ) :
    ((productDiagramEquiv n G C).unitIso.hom.app X).app x =
      X.map ((productSourceOpEquiv n G).unitIso.hom.app x) := by
  change ((productSourceOpEquiv n G).funInvIdAssoc X).inv.app x =
    X.map ((productSourceOpEquiv n G).unit.app x)
  exact Equivalence.funInvIdAssoc_inv_app (productSourceOpEquiv n G) X x

theorem productDiagramEquiv_unit_inv_app (n : ℕ) (X : (Gᵒᵖ × Source n)ᵒᵖ ⥤ C)
    (x : (Gᵒᵖ × Source n)ᵒᵖ) :
    ((productDiagramEquiv n G C).unitIso.inv.app X).app x =
      X.map ((productSourceOpEquiv n G).unitIso.inv.app x) := by
  change ((productSourceOpEquiv n G).funInvIdAssoc X).hom.app x =
    X.map ((productSourceOpEquiv n G).unitInv.app x)
  exact Equivalence.funInvIdAssoc_hom_app (productSourceOpEquiv n G) X x

theorem productDiagramEquiv_counit_hom_app (n : ℕ) (X : (G × Index n) ⥤ C)
    (x : G × Index n) :
    ((productDiagramEquiv n G C).counitIso.hom.app X).app x =
      X.map ((productSourceOpEquiv n G).counitIso.hom.app x) := by
  change ((productSourceOpEquiv n G).invFunIdAssoc X).hom.app x =
    X.map ((productSourceOpEquiv n G).counit.app x)
  exact Equivalence.invFunIdAssoc_hom_app (productSourceOpEquiv n G) X x

theorem productDiagramEquiv_counit_inv_app (n : ℕ) (X : (G × Index n) ⥤ C)
    (x : G × Index n) :
    ((productDiagramEquiv n G C).counitIso.inv.app X).app x =
      X.map ((productSourceOpEquiv n G).counitIso.inv.app x) := by
  change ((productSourceOpEquiv n G).invFunIdAssoc X).inv.app x =
    X.map ((productSourceOpEquiv n G).counitInv.app x)
  exact Equivalence.invFunIdAssoc_inv_app (productSourceOpEquiv n G) X x

end Product

end CategoryTheory.FinitePowerSite
