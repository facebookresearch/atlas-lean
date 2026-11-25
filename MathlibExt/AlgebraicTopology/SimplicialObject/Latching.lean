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
# Functorial latching objects of simplicial objects

The latching index in degree `n` consists of proper epimorphisms out of
`[n]`.  Its comma orientation is chosen so a simplicial object gives a
covariant latching diagram.  Latching objects, latching maps, and latching
arrows are functorial in the simplicial object.
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

/-- The ambient comma category of incoming simplicial arrows in degree `n`. -/
abbrev latchingIndexComma (n : ℕ) : Type :=
  CostructuredArrow (𝟭 SimplexCategoryᵒᵖ) (op ⦋n⦌)

/-- The latching index in degree `n`: proper epimorphisms `[n] ⟶ [m]`,
with the comma orientation covariant for simplicial objects. -/
abbrev latchingIndex (n : ℕ) : Type :=
  ObjectProperty.FullSubcategory
    (fun θ : latchingIndexComma n =>
      Epi θ.hom.unop ∧ θ.left.unop.len < n)

private def latchingIndexHomEquiv {n : ℕ}
    (a b : latchingIndex n) :
    (a ⟶ b) ≃
      { β : b.obj.left.unop ⟶ a.obj.left.unop //
        b.obj.hom.unop ≫ β = a.obj.hom.unop } where
  toFun f := ⟨f.hom.left.unop, by
    apply Quiver.Hom.op_inj
    simp⟩
  invFun β := ObjectProperty.homMk
    (CostructuredArrow.homMk β.1.op (by
      apply Quiver.Hom.unop_inj
      simpa using β.2))
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    rfl
  right_inv β := by
    apply Subtype.ext
    rfl

private abbrev latchingIndexFiniteData (n : ℕ) :=
  ⦋n⦌ ⟶ ⦋n⦌

/-- The latching index has finitely many objects, without installing any
global decidability data. -/
noncomputable instance (n : ℕ) : Finite (latchingIndex n) := by
  let bound (a : latchingIndex n) :
      a.obj.left.unop.len + 1 ≤ n + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt a.property.2)
  let inclusion (a : latchingIndex n) :
      a.obj.left.unop ⟶ ⦋n⦌ :=
    SimplexCategory.mkHom
      { toFun := fun i => Fin.castLE (bound a) i
        monotone' := fun _ _ h => by
          exact h }
  let encode : latchingIndex n → latchingIndexFiniteData n := fun a =>
    a.obj.hom.unop ≫ inclusion a
  apply Finite.of_injective encode
  intro a b h
  have degree_le (x y : latchingIndex n)
      (hxy : encode x = encode y) :
      x.obj.left.unop.len ≤ y.obj.left.unop.len := by
    have hx := (SimplexCategory.epi_iff_surjective).mp x.property.1
    obtain ⟨i, hi⟩ := hx (Fin.last x.obj.left.unop.len)
    have hvalue := SimplexCategory.congr_toOrderHom_apply hxy i
    dsimp [encode, inclusion] at hvalue
    change Fin.castLE (bound x) (x.obj.hom.unop.toOrderHom i) =
      Fin.castLE (bound y) (y.obj.hom.unop.toOrderHom i) at hvalue
    rw [hi] at hvalue
    have hval := congrArg Fin.val hvalue
    have heq : x.obj.left.unop.len =
        (y.obj.hom.unop.toOrderHom i).val := by
      change x.obj.left.unop.len =
        (y.obj.hom.unop.toOrderHom i).val at hval
      exact hval
    rw [heq]
    exact (y.obj.hom.unop.toOrderHom i).is_le
  have hlen : a.obj.left.unop.len = b.obj.left.unop.len :=
    le_antisymm (degree_le a b h) (degree_le b a h.symm)
  have hleft : a.obj.left = b.obj.left := by
    apply unop_injective
    apply SimplexCategory.ext
    exact hlen
  have hIncl : (eqToHom hleft).unop ≫ inclusion a = inclusion b := by
    apply SimplexCategory.Hom.ext
    ext i
    simp [inclusion, SimplexCategory.eqToHom_toOrderHom]
    rfl
  apply ObjectProperty.FullSubcategory.ext
  apply CostructuredArrow.obj_ext a.obj b.obj hleft
  apply Quiver.Hom.unop_inj
  change b.obj.hom.unop ≫ (eqToHom hleft).unop =
    a.obj.hom.unop
  let _ : Mono (inclusion a) := by
    apply (SimplexCategory.mono_iff_injective).2
    dsimp [inclusion]
    change Function.Injective (Fin.castLE (bound a))
    exact Fin.castLE_injective (bound a)
  apply (cancel_mono (inclusion a)).1
  rw [Category.assoc, hIncl]
  simpa [encode] using h.symm

/-- A morphism of the latching index is determined by its simplex map, so there are finitely
many morphisms between two objects. -/
instance (n : ℕ) (a b : latchingIndex n) : Finite (a ⟶ b) := by
  let projection : (a ⟶ b) →
      (Fin (b.obj.left.unop.len + 1) → Fin (a.obj.left.unop.len + 1)) :=
    fun f => f.hom.left.unop.toOrderHom
  apply Finite.of_injective projection
  intro f g h
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  exact h

/-- The latching index is a finite category, so latching objects exist in every category with
finite colimits. -/
noncomputable instance latchingIndexFinCategory (n : ℕ) : FinCategory (latchingIndex n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- Restrict a simplicial transformation to every latching-index coefficient. -/
def latchingDiagramMap (n : ℕ)
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    ({ obj := fun a => X.obj a.obj.left
       map := fun {_ _} g => X.map g.hom.left
       map_id := by intro; simp
       map_comp := by intros; simp } : latchingIndex n ⥤ C) ⟶
      ({ obj := fun a => Y.obj a.obj.left
         map := fun {_ _} g => Y.map g.hom.left
         map_id := by intro; simp
         map_comp := by intros; simp } : latchingIndex n ⥤ C) where
  app a := f.app a.obj.left
  naturality _ _ g := f.naturality g.hom.left

private theorem latchingDiagramMap_id (n : ℕ)
    (X : SimplicialObject C) :
    latchingDiagramMap n (𝟙 X) = 𝟙 _ := by
  apply NatTrans.ext
  funext a
  rfl

private theorem latchingDiagramMap_comp (n : ℕ)
    {X Y Z : SimplicialObject C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    latchingDiagramMap n (f ≫ g) =
      latchingDiagramMap n f ≫ latchingDiagramMap n g := by
  apply NatTrans.ext
  funext a
  rfl

/-- In degree `n`, the latching diagram is functorial in the simplicial
object. -/
def latchingDiagramFunctor (n : ℕ) :
    SimplicialObject C ⥤ (latchingIndex n ⥤ C) where
  obj X :=
    { obj := fun a => X.obj a.obj.left
      map := fun {_ _} g => X.map g.hom.left
      map_id := by intro; simp
      map_comp := by intros; simp }
  map f := latchingDiagramMap n f
  map_id X := by exact latchingDiagramMap_id n X
  map_comp f g := by exact latchingDiagramMap_comp n f g

/-- The latching diagram of `X` in degree `n`. -/
abbrev latchingDiagram (X : SimplicialObject C) (n : ℕ) :
    latchingIndex n ⥤ C :=
  (latchingDiagramFunctor (C := C) n).obj X

/-- A simplicial morphism acts on a latching diagram by its component at
the target degree of the indexing epi. -/
@[simp]
theorem latchingDiagramFunctor_map_app (n : ℕ)
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (a : latchingIndex n) :
    ((latchingDiagramFunctor (C := C) n).map f).app a =
      f.app a.obj.left :=
  rfl

private theorem latchingCocone_w (X : SimplicialObject C) {n : ℕ}
    {a b : latchingIndex n} (f : a ⟶ b) :
    X.map f.hom.left ≫ X.map b.obj.hom = X.map a.obj.hom := by
  rw [← X.map_comp]
  apply X.congr_map
  simp

/-- The canonical cocone from the latching diagram to `X` in degree `n`. -/
def latchingCocone (X : SimplicialObject C) (n : ℕ) :
    Cocone (latchingDiagram X n) where
  pt := X.obj (op ⦋n⦌)
  ι :=
    { app := fun a => X.map a.obj.hom
      naturality := by
        intro a b f
        change X.map f.hom.left ≫ X.map b.obj.hom =
          X.map a.obj.hom ≫ 𝟙 _
        rw [Category.comp_id]
        exact latchingCocone_w X f }

/-- The latching object in degree `n`, functorial in the simplicial object. -/
noncomputable def latchingObjectFunctor (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    SimplicialObject C ⥤ C :=
  latchingDiagramFunctor n ⋙ colim

/-- The latching object of `X` in degree `n`. -/
noncomputable abbrev latchingObject (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] : C :=
  (latchingObjectFunctor n).obj X

/-- The canonical leg from a lower simplicial degree into the latching
object. -/
noncomputable def latchingι (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] (a : latchingIndex n) :
    X.obj a.obj.left ⟶ latchingObject X n :=
  colimit.ι (latchingDiagram X n) a

/-- The canonical latching legs commute with a simplicial morphism. -/
@[reassoc]
theorem latchingObjectFunctor_map_ι (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (a : latchingIndex n) :
    latchingι X n a ≫ (latchingObjectFunctor n).map f =
      f.app a.obj.left ≫ latchingι Y n a := by
  exact ι_colimMap ((latchingDiagramFunctor n).map f) a

set_option backward.isDefEq.respectTransparency false in
private theorem latchingObjectFunctor_map_desc (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (c : Cocone (latchingDiagram Y n)) :
    (latchingObjectFunctor n).map f ≫
        colimit.desc (latchingDiagram Y n) c =
      colimit.desc (latchingDiagram X n)
        ((Cocone.precompose
          ((latchingDiagramFunctor n).map f)).obj c) := by
  apply colimit.hom_ext
  intro a
  change colimit.ι (latchingDiagram X n) a ≫
        colimMap ((latchingDiagramFunctor n).map f) ≫
          colimit.desc (latchingDiagram Y n) c =
    colimit.ι (latchingDiagram X n) a ≫
      colimit.desc (latchingDiagram X n)
        ((Cocone.precompose
          ((latchingDiagramFunctor n).map f)).obj c)
  rw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem latchingMapNatTrans_w (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (latchingObjectFunctor n).map f ≫
        colimit.desc (latchingDiagram Y n) (latchingCocone Y n) =
      colimit.desc (latchingDiagram X n) (latchingCocone X n) ≫
        f.app (op ⦋n⦌) := by
  rw [latchingObjectFunctor_map_desc]
  apply colimit.hom_ext
  intro a
  rw [colimit.ι_desc_assoc, colimit.ι_desc]
  change f.app a.obj.left ≫ Y.map a.obj.hom =
    X.map a.obj.hom ≫ f.app (op ⦋n⦌)
  exact (f.naturality a.obj.hom).symm

/-- The latching maps form a natural transformation from latching objects
to evaluation in degree `n`. -/
noncomputable def latchingMapNatTrans (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    latchingObjectFunctor n ⟶
      (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋n⦌) where
  app X := colimit.desc (latchingDiagram X n) (latchingCocone X n)
  naturality _ _ f := by exact latchingMapNatTrans_w n f

/-- The latching map of `X` in degree `n`. -/
noncomputable abbrev latchingMap (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    latchingObject X n ⟶ X.obj (op ⦋n⦌) :=
  (latchingMapNatTrans n).app X

/-- A canonical latching leg followed by the latching map is the
corresponding simplicial structure map. -/
@[reassoc]
theorem latchingMap_ι (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] (a : latchingIndex n) :
    latchingι X n a ≫ latchingMap X n = X.map a.obj.hom := by
  change colimit.ι (latchingDiagram X n) a ≫
      colimit.desc (latchingDiagram X n) (latchingCocone X n) =
    X.map a.obj.hom
  exact colimit.ι_desc (latchingCocone X n) a

/-- Naturality of latching maps. -/
@[reassoc]
theorem latchingMap_naturality (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (latchingObjectFunctor n).map f ≫ latchingMap Y n =
      latchingMap X n ≫ f.app (op ⦋n⦌) :=
  (latchingMapNatTrans n).naturality f

/-- The full latching Arrow map induced by a simplicial transformation. -/
noncomputable def latchingMapArrowFunctorMap (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    Arrow.mk (latchingMap X n) ⟶ Arrow.mk (latchingMap Y n) :=
  Arrow.homMk ((latchingObjectFunctor n).map f)
    (f.app (op ⦋n⦌)) (latchingMap_naturality n f)

/-- Latching maps form a functor to the arrow category. -/
noncomputable def latchingMapArrowFunctor (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    SimplicialObject C ⥤ Arrow C where
  obj X := Arrow.mk (latchingMap X n)
  map f := latchingMapArrowFunctorMap n f
  map_id X := by
    apply Arrow.hom_ext <;>
      simp [latchingMapArrowFunctorMap]
  map_comp f g := by
    apply Arrow.hom_ext <;>
      simp [latchingMapArrowFunctorMap]

/-- The object of the latching-arrow functor is the latching map. -/
@[simp]
theorem latchingMapArrowFunctor_obj (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    (X : SimplicialObject C) :
    (latchingMapArrowFunctor n).obj X =
      Arrow.mk (latchingMap X n) :=
  rfl

/-- A simplicial isomorphism induces the canonical isomorphism of latching
arrows. -/
noncomputable def latchingMapArrowIso (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {X Y : SimplicialObject C} (e : X ≅ Y) :
    Arrow.mk (latchingMap X n) ≅ Arrow.mk (latchingMap Y n) :=
  (latchingMapArrowFunctor n).mapIso e

private theorem latchingIndexZero_isEmpty : IsEmpty (latchingIndex 0) :=
  ⟨fun a => (Nat.not_lt_zero _ a.property.2).elim⟩

/-- In degree zero, the latching object is initial. -/
noncomputable def latchingObjectZeroIso
    [HasInitial C]
    [HasColimitsOfShape (latchingIndex 0) C]
    (X : SimplicialObject C) :
    latchingObject X 0 ≅ ⊥_ C := by
  let _ : IsEmpty (latchingIndex 0) := by exact latchingIndexZero_isEmpty
  let emptyCocone (Y : C) : Cocone (latchingDiagram X 0) :=
    { pt := Y
      ι :=
        { app := fun a => isEmptyElim a
          naturality := by
            intro a
            exact isEmptyElim a } }
  let hL : IsInitial (latchingObject X 0) :=
    IsInitial.ofUniqueHom
      (fun Y => colimit.desc (latchingDiagram X 0) (emptyCocone Y))
      (fun _ _ => by
        apply colimit.hom_ext
        intro a
        exact isEmptyElim a)
  exact hL.uniqueUpToIso initialIsInitial

/-- In degree zero, the latching arrow is the canonical map from the
initial object. -/
noncomputable def latchingMapZeroArrowIso
    [HasInitial C]
    [HasColimitsOfShape (latchingIndex 0) C]
    (X : SimplicialObject C) :
    (latchingMapArrowFunctor 0).obj X ≅
      Arrow.mk (initial.to (X.obj (op ⦋0⦌))) := by
  change Arrow.mk (latchingMap X 0) ≅
    Arrow.mk (initial.to (X.obj (op ⦋0⦌)))
  let hL : IsInitial (latchingObject X 0) :=
    initialIsInitial.ofIso (latchingObjectZeroIso X).symm
  exact Arrow.isoMk (latchingObjectZeroIso X) (Iso.refl _)
    (hL.hom_ext _ _)

/-- A simplicial object has its elementary degeneracies in `W`. -/
def DegeneraciesIn (X : SimplicialObject C)
    (W : MorphismProperty C) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 1)), W (X.σ i)

/-- A simplicial object has all its latching maps in `W`. -/
def LatchingMapsIn (X : SimplicialObject C)
    (W : MorphismProperty C)
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C] : Prop :=
  ∀ n : ℕ, W (latchingMap X n)

end CategoryTheory.SimplicialObject
