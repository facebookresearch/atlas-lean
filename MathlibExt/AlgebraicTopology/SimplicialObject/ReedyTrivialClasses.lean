/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyWeakFactorizationSystem
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Trivial Reedy morphism classes for simplicial objects

In a model category, the Reedy trivial cofibrations are exactly the Reedy cofibrations that are
pointwise weak equivalences, and the Reedy trivial fibrations are exactly the Reedy fibrations that
are pointwise weak equivalences. The proof uses explicit finite latching and matching filtrations;
it does not require properness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits Opposite
open HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

namespace ReedyTrivialClassesLatching

/-- Objects of `latchingIndex n` whose target simplex has degree `< m`. -/
private abbrev latchingIndexBelow (n m : ℕ) :=
  ObjectProperty.FullSubcategory
    (fun a : CategoryTheory.SimplicialObject.latchingIndex n =>
      a.obj.left.unop.len < m)

/-- Forget the filtration bound. -/
private def belowToLatching (n m : ℕ) :
    latchingIndexBelow n m ⥤ CategoryTheory.SimplicialObject.latchingIndex n where
  obj a := a.obj
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Increase the filtration bound. -/
private def belowIncl {n m m' : ℕ} (h : m ≤ m') :
    latchingIndexBelow n m ⥤ latchingIndexBelow n m' where
  obj a := ⟨a.obj, a.property.trans_le h⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def belowToLatchingFullyFaithful (n m : ℕ) :
    (belowToLatching n m).FullyFaithful where
  preimage f := ObjectProperty.homMk f

private instance belowToLatching_full (n m : ℕ) : (belowToLatching n m).Full :=
  (belowToLatchingFullyFaithful n m).full

private instance belowToLatching_faithful (n m : ℕ) : (belowToLatching n m).Faithful :=
  (belowToLatchingFullyFaithful n m).faithful

private def belowInclFullyFaithful {n m m' : ℕ} (h : m ≤ m') :
    (belowIncl (n := n) h).FullyFaithful where
  preimage f := ObjectProperty.homMk f.hom

private instance belowIncl_full {n m m' : ℕ} (h : m ≤ m') : (belowIncl (n := n) h).Full :=
  (belowInclFullyFaithful h).full

private instance belowIncl_faithful {n m m' : ℕ} (h : m ≤ m') :
    (belowIncl (n := n) h).Faithful :=
  (belowInclFullyFaithful h).faithful

@[simp]
private theorem belowToLatching_obj (n m : ℕ) (a : latchingIndexBelow n m) :
    (belowToLatching n m).obj a = a.obj :=
  rfl

@[simp]
private theorem belowToLatching_map (n m : ℕ) {a b : latchingIndexBelow n m} (f : a ⟶ b) :
    (belowToLatching n m).map f = f.hom :=
  rfl

@[simp]
private theorem belowIncl_obj_obj {n m m' : ℕ} (h : m ≤ m') (a : latchingIndexBelow n m) :
    ((belowIncl h).obj a).obj = a.obj :=
  rfl

@[simp]
private theorem belowIncl_map_hom {n m m' : ℕ} (h : m ≤ m')
    {a b : latchingIndexBelow n m} (f : a ⟶ b) :
    ((belowIncl h).map f).hom = f.hom :=
  rfl

private theorem belowIncl_refl (n m : ℕ) :
    belowIncl (n := n) (Nat.le_refl m) = 𝟭 (latchingIndexBelow n m) :=
  rfl

private theorem belowIncl_trans {n m m' m'' : ℕ} (h : m ≤ m') (h' : m' ≤ m'') :
    belowIncl (n := n) h ⋙ belowIncl (n := n) h' =
      belowIncl (n := n) (h.trans h') :=
  rfl

private instance latchingIndexBelow_zero_isEmpty (n : ℕ) : IsEmpty (latchingIndexBelow n 0) where
  false a := (Nat.not_lt_zero _ a.property).elim

private noncomputable instance latchingIndexBelow_finite (n m : ℕ) :
    Finite (latchingIndexBelow n m) :=
  Finite.of_injective (fun a => a.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

/-- The exact degree-`m` stratum in the latching index. -/
private abbrev latchingIndexDegree (n m : ℕ) :=
  ObjectProperty.FullSubcategory
    (fun a : CategoryTheory.SimplicialObject.latchingIndex n =>
      a.obj.left.unop.len = m)

private noncomputable instance latchingIndexDegree_finite (n m : ℕ) :
    Finite (latchingIndexDegree n m) :=
  Finite.of_injective (fun a => a.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

private instance latchingIndexDegree_hom_subsingleton (n m : ℕ)
    (a b : latchingIndexDegree n m) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    let _ : Epi b.obj.obj.hom.unop := b.obj.property.1
    let _ : Mono b.obj.obj.hom := by
      simpa using (inferInstance : Mono b.obj.obj.hom.unop.op)
    apply (cancel_mono b.obj.obj.hom).1
    exact (CostructuredArrow.w f.hom.hom).trans
      (CostructuredArrow.w g.hom.hom).symm

/-- A morphism in one exact-degree stratum forces equality of its endpoints. -/
private theorem eq_of_hom_in_degree {n m : ℕ} {a b : latchingIndexDegree n m} (f : a ⟶ b) :
    a = b := by
  have hfac : b.obj.obj.hom.unop ≫ f.hom.hom.left.unop = a.obj.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simp
  let _ : Epi (b.obj.obj.hom.unop ≫ f.hom.hom.left.unop) := by
    rw [hfac]
    exact a.obj.property.1
  let _ : Epi f.hom.hom.left.unop :=
    CategoryTheory.epi_of_epi b.obj.obj.hom.unop f.hom.hom.left.unop
  have hleftUnop : a.obj.obj.left.unop = b.obj.obj.left.unop := by
    apply SimplexCategory.ext
    exact a.property.trans b.property.symm
  let hleft : a.obj.obj.left = b.obj.obj.left := congrArg op hleftUnop
  let e := (f.hom.hom.left ≫ eqToHom hleft.symm).unop
  let _ : Epi e := by
    dsimp [e]
    infer_instance
  have heUnop : e = 𝟙 _ := SimplexCategory.eq_id_of_epi e
  have he : f.hom.hom.left ≫ eqToHom hleft.symm = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    simpa [e] using heUnop
  have hfleft : f.hom.hom.left = eqToHom hleft := by
    apply (cancel_mono (eqToHom hleft.symm)).1
    rw [he]
    simp
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply CostructuredArrow.obj_ext _ _ hleft
  simpa [hfleft] using CostructuredArrow.w f.hom.hom

/-- The degree-`m` stratum is equivalent to a discrete category on its objects. -/
private noncomputable def latchingIndexDegreeEquivDiscrete (n m : ℕ) :
    latchingIndexDegree n m ≌ Discrete (latchingIndexDegree n m) := by
  let F : latchingIndexDegree n m ⥤ Discrete (latchingIndexDegree n m) :=
    { obj := Discrete.mk
      map := fun f => eqToHom (congrArg Discrete.mk (eq_of_hom_in_degree f))
      map_id := by intro; subsingleton
      map_comp := by intros; subsingleton }
  let G : Discrete (latchingIndexDegree n m) ⥤ latchingIndexDegree n m :=
    Discrete.functor fun a => a
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
      counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

private instance latchingIndex_hom_subsingleton (n : ℕ)
    (a b : CategoryTheory.SimplicialObject.latchingIndex n) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    let _ : Epi b.obj.hom.unop := b.property.1
    let _ : Mono b.obj.hom := by
      simpa using (inferInstance : Mono b.obj.hom.unop.op)
    apply (cancel_mono b.obj.hom).1
    exact (CostructuredArrow.w f.hom).trans (CostructuredArrow.w g.hom).symm

private instance latchingIndexBelow_hom_subsingleton (n m : ℕ)
    (a b : latchingIndexBelow n m) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

/-- The comma category of previously attached objects mapping to a new degree-`m` epi. -/
private abbrev latchingPredecessor (n m : ℕ) (a : latchingIndexDegree n m) :=
  CostructuredArrow (belowToLatching n m) a.obj

private instance latchingPredecessor_hom_subsingleton (n m : ℕ)
    (a : latchingIndexDegree n m) (x y : latchingPredecessor n m a) :
    Subsingleton (x ⟶ y) where
  allEq f g := by
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

private theorem newTargetEq {n m : ℕ} (a : latchingIndexDegree n m) :
    a.obj.obj.left = op ⦋m⦌ := by
  apply unop_injective
  apply SimplexCategory.ext
  simpa using a.property

private def predecessorCanonicalHom {n m : ℕ} {a : latchingIndexDegree n m}
    (x : latchingPredecessor n m a) :
    x.left.obj.obj.left ⟶ op ⦋m⦌ :=
  x.hom.hom.left ≫ eqToHom (newTargetEq a)

private instance predecessorCanonicalHom_epi {n m : ℕ}
    {a : latchingIndexDegree n m} (x : latchingPredecessor n m a) :
    Epi (predecessorCanonicalHom x).unop := by
  have hfac : a.obj.obj.hom.unop ≫ x.hom.hom.left.unop =
      x.left.obj.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simp
  let _ : Epi (a.obj.obj.hom.unop ≫ x.hom.hom.left.unop) := by
    rw [hfac]
    exact x.left.obj.property.1
  let _ : Epi x.hom.hom.left.unop :=
    CategoryTheory.epi_of_epi a.obj.obj.hom.unop x.hom.hom.left.unop
  let _ : Epi (eqToHom (newTargetEq a)).unop := by infer_instance
  change Epi ((eqToHom (newTargetEq a)).unop ≫ x.hom.hom.left.unop)
  infer_instance

private def predecessorToLatchingIndexObj {n m : ℕ}
    {a : latchingIndexDegree n m} (x : latchingPredecessor n m a) :
    CategoryTheory.SimplicialObject.latchingIndex m :=
  ⟨CostructuredArrow.mk (predecessorCanonicalHom x),
    ⟨predecessorCanonicalHom_epi x, x.left.property⟩⟩

private def predecessorToLatchingIndex {n m : ℕ}
    (a : latchingIndexDegree n m) :
    latchingPredecessor n m a ⥤ CategoryTheory.SimplicialObject.latchingIndex m where
  obj := predecessorToLatchingIndexObj
  map {x y} g := ObjectProperty.homMk
    (CostructuredArrow.homMk g.left.hom.hom.left (by
      have hw := congrArg (fun z => z.hom.left) (CostructuredArrow.w g)
      have hw' : g.left.hom.hom.left ≫ y.hom.hom.left = x.hom.hom.left := by
        change g.left.hom.hom.left ≫ y.hom.hom.left = x.hom.hom.left at hw
        exact hw
      change g.left.hom.hom.left ≫ predecessorCanonicalHom y =
        predecessorCanonicalHom x
      dsimp [predecessorCanonicalHom]
      rw [← Category.assoc, hw']))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
private theorem predecessorToLatchingIndex_obj_left {n m : ℕ}
    {a : latchingIndexDegree n m} (x : latchingPredecessor n m a) :
    ((predecessorToLatchingIndex a).obj x).obj.left = x.left.obj.obj.left :=
  rfl

@[simp]
private theorem predecessorToLatchingIndex_obj_hom {n m : ℕ}
    {a : latchingIndexDegree n m} (x : latchingPredecessor n m a) :
    ((predecessorToLatchingIndex a).obj x).obj.hom = predecessorCanonicalHom x :=
  rfl

@[simp]
private theorem predecessorToLatchingIndex_map_left {n m : ℕ}
    {a : latchingIndexDegree n m} {x y : latchingPredecessor n m a} (g : x ⟶ y) :
    ((predecessorToLatchingIndex a).map g).hom.left = g.left.hom.hom.left :=
  rfl

private def liftedHom {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    b.obj.left ⟶ op ⦋n⦌ :=
  b.obj.hom ≫ eqToHom (newTargetEq a).symm ≫ a.obj.obj.hom

private instance liftedHom_epi {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    Epi (liftedHom a b).unop := by
  let _ : Epi b.obj.hom.unop := b.property.1
  let _ : Epi a.obj.obj.hom.unop := a.obj.property.1
  let _ : Epi (eqToHom (newTargetEq a).symm).unop := by infer_instance
  dsimp [liftedHom]
  infer_instance

private def liftedBelowObj {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) : latchingIndexBelow n m :=
  by
    refine ⟨⟨CostructuredArrow.mk (liftedHom a b), ⟨liftedHom_epi a b, ?_⟩⟩,
      b.property.2⟩
    exact b.property.2.trans (by simpa [a.property] using a.obj.property.2)

private def liftedToNew {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    (belowToLatching n m).obj (liftedBelowObj a b) ⟶ a.obj :=
  ObjectProperty.homMk
    (CostructuredArrow.homMk (b.obj.hom ≫ eqToHom (newTargetEq a).symm) (by rfl))

private def latchingIndexToPredecessorObj {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) : latchingPredecessor n m a :=
  CostructuredArrow.mk (liftedToNew a b)

private def liftedMap {n m : ℕ} (a : latchingIndexDegree n m)
    {b c : CategoryTheory.SimplicialObject.latchingIndex m} (g : b ⟶ c) :
    liftedBelowObj a b ⟶ liftedBelowObj a c :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (CostructuredArrow.homMk g.hom.left (by
      have hw := CostructuredArrow.w g.hom
      change g.hom.left ≫ c.obj.hom = b.obj.hom at hw
      change g.hom.left ≫ liftedHom a c = liftedHom a b
      dsimp [liftedHom]
      rw [← Category.assoc, hw])) )

private def latchingIndexToPredecessor {n m : ℕ} (a : latchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.latchingIndex m ⥤ latchingPredecessor n m a where
  obj := latchingIndexToPredecessorObj a
  map g := CostructuredArrow.homMk (liftedMap a g) (by subsingleton)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
private theorem latchingIndexToPredecessor_obj_left_obj_left {n m : ℕ}
    (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    ((latchingIndexToPredecessor a).obj b).left.obj.obj.left = b.obj.left :=
  rfl

@[simp]
private theorem latchingIndexToPredecessor_obj_left_obj_hom {n m : ℕ}
    (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    ((latchingIndexToPredecessor a).obj b).left.obj.obj.hom = liftedHom a b :=
  rfl

@[simp]
private theorem latchingIndexToPredecessor_obj_hom_left {n m : ℕ}
    (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    ((latchingIndexToPredecessor a).obj b).hom.hom.left =
      b.obj.hom ≫ eqToHom (newTargetEq a).symm :=
  rfl

@[simp]
private theorem latchingIndexToPredecessor_map_left_left {n m : ℕ}
    (a : latchingIndexDegree n m)
    {b c : CategoryTheory.SimplicialObject.latchingIndex m} (g : b ⟶ c) :
    ((latchingIndexToPredecessor a).map g).left.hom.hom.left = g.hom.left :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem predecessorCanonicalHom_lifted {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    predecessorCanonicalHom ((latchingIndexToPredecessor a).obj b) = b.obj.hom := by
  dsimp [predecessorCanonicalHom, latchingIndexToPredecessor,
    latchingIndexToPredecessorObj, liftedToNew]
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem liftedHom_predecessor {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    liftedHom a ((predecessorToLatchingIndex a).obj x) = x.left.obj.obj.hom := by
  have hc : eqToHom (newTargetEq a) ≫ eqToHom (newTargetEq a).symm = 𝟙 _ := by
    simp
  calc
    liftedHom a ((predecessorToLatchingIndex a).obj x) =
        x.hom.hom.left ≫
          (eqToHom (newTargetEq a) ≫ eqToHom (newTargetEq a).symm) ≫
            a.obj.obj.hom := by
              simp only [liftedHom, predecessorToLatchingIndex,
                predecessorToLatchingIndexObj, predecessorCanonicalHom,
                CostructuredArrow.mk_hom_eq_self, Category.assoc]
    _ = x.hom.hom.left ≫ a.obj.obj.hom := by rw [hc]; simp
    _ = x.left.obj.obj.hom := CostructuredArrow.w x.hom.hom

set_option backward.isDefEq.respectTransparency false in
private theorem predecessor_counit_obj_eq {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    (predecessorToLatchingIndex a).obj ((latchingIndexToPredecessor a).obj b) = b := by
  apply ObjectProperty.FullSubcategory.ext
  let hleft :
      ((predecessorToLatchingIndex a).obj ((latchingIndexToPredecessor a).obj b)).obj.left =
        b.obj.left := rfl
  apply CostructuredArrow.obj_ext _ _ hleft
  simpa using (predecessorCanonicalHom_lifted a b).symm

set_option backward.isDefEq.respectTransparency false in
private theorem predecessor_unit_left_eq {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    ((latchingIndexToPredecessor a).obj ((predecessorToLatchingIndex a).obj x)).left =
      x.left := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  let hleft :
      (CostructuredArrow.left
        ((latchingIndexToPredecessor a).obj ((predecessorToLatchingIndex a).obj x))).obj.obj.left =
          x.left.obj.obj.left := rfl
  apply CostructuredArrow.obj_ext _ _ hleft
  simpa using (liftedHom_predecessor a x).symm

private theorem predecessor_unit_obj_eq {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    (latchingIndexToPredecessor a).obj ((predecessorToLatchingIndex a).obj x) = x := by
  apply CostructuredArrow.obj_ext _ _ (predecessor_unit_left_eq a x)
  exact Subsingleton.elim _ _

/-- Direct composition/extraction identifies the predecessor category with `latchingIndex m`. -/
private noncomputable def predecessorEquivalence {n m : ℕ} (a : latchingIndexDegree n m) :
    latchingPredecessor n m a ≌ CategoryTheory.SimplicialObject.latchingIndex m where
  functor := predecessorToLatchingIndex a
  inverse := latchingIndexToPredecessor a
  unitIso := NatIso.ofComponents
    (fun x => CategoryTheory.eqToIso (predecessor_unit_obj_eq a x).symm)
  counitIso := NatIso.ofComponents
    (fun b => CategoryTheory.eqToIso (predecessor_counit_obj_eq a b))

private theorem belowIncl_comp_belowToLatching {n m m' : ℕ} (h : m ≤ m') :
    belowIncl (n := n) h ⋙ belowToLatching n m' = belowToLatching n m :=
  rfl

private theorem predecessorCanonicalHom_comp_targetEq {n m : ℕ}
    {a : latchingIndexDegree n m} (x : latchingPredecessor n m a) :
    predecessorCanonicalHom x ≫ eqToHom (newTargetEq a).symm = x.hom.hom.left := by
  dsimp [predecessorCanonicalHom]
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

section DiagramEquations

universe v u

variable {C : Type u} [Category.{v} C] (X : CategoryTheory.SimplicialObject C)

private theorem predecessor_diagram_obj {n m : ℕ} {a : latchingIndexDegree n m}
    (x : latchingPredecessor n m a) :
    (CategoryTheory.SimplicialObject.latchingDiagram X n).obj x.left.obj =
      (CategoryTheory.SimplicialObject.latchingDiagram X m).obj
        ((predecessorToLatchingIndex a).obj x) :=
  rfl

private theorem predecessor_diagram_map {n m : ℕ} {a : latchingIndexDegree n m}
    {x y : latchingPredecessor n m a} (g : x ⟶ y) :
    (CategoryTheory.SimplicialObject.latchingDiagram X n).map g.left.hom =
      (CategoryTheory.SimplicialObject.latchingDiagram X m).map
        ((predecessorToLatchingIndex a).map g) :=
  rfl

private theorem predecessor_structure_map {n m : ℕ} {a : latchingIndexDegree n m}
    (x : latchingPredecessor n m a) :
    X.map (predecessorCanonicalHom x) ≫ X.map (eqToHom (newTargetEq a).symm) =
      X.map x.hom.hom.left := by
  rw [← X.map_comp, predecessorCanonicalHom_comp_targetEq]
  rfl

end DiagramEquations

section FilteredColimits

universe v u

open CategoryTheory.Limits
open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private instance latchingIndex_isThin (n : ℕ) :
    Quiver.IsThin (CategoryTheory.SimplicialObject.latchingIndex n) :=
  fun _ _ => inferInstance

private instance latchingIndexBelow_isThin (n m : ℕ) :
    Quiver.IsThin (latchingIndexBelow n m) :=
  fun _ _ => inferInstance

private noncomputable instance latchingIndexBelow_fintype (n m : ℕ) :
    Fintype (latchingIndexBelow n m) :=
  Fintype.ofFinite _

/-- The degree-`<m` part of the degree-`n` latching diagram. -/
private abbrev filteredLatchingDiagram (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    latchingIndexBelow n m ⥤ C :=
  belowToLatching n m ⋙ CategoryTheory.SimplicialObject.latchingDiagram X n

private def filteredLatchingDiagramMap {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) :
    filteredLatchingDiagram X n m ⟶ filteredLatchingDiagram Y n m :=
  Functor.whiskerLeft (belowToLatching n m)
    ((CategoryTheory.SimplicialObject.latchingDiagramFunctor n).map f)

private noncomputable abbrev filteredLatchingObject
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  colimit (filteredLatchingDiagram X n m)

private noncomputable def filteredLatchingMap {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) :
    filteredLatchingObject X n m ⟶ filteredLatchingObject Y n m :=
  colimMap (filteredLatchingDiagramMap f n m)

/-- The map between two stages of the latching filtration. -/
private noncomputable def filteredLatchingIncl
    (X : CategoryTheory.SimplicialObject C) {n m m' : ℕ} (h : m ≤ m') :
    filteredLatchingObject X n m ⟶ filteredLatchingObject X n m' :=
  colimit.pre (filteredLatchingDiagram X n m') (belowIncl (n := n) h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem filteredLatchingIncl_ι
    (X : CategoryTheory.SimplicialObject C) {n m m' : ℕ} (h : m ≤ m')
    (a : latchingIndexBelow n m) :
    colimit.ι (filteredLatchingDiagram X n m) a ≫ filteredLatchingIncl X h =
      colimit.ι (filteredLatchingDiagram X n m') ((belowIncl h).obj a) := by
  change colimit.ι (belowIncl (n := n) h ⋙ filteredLatchingDiagram X n m') a ≫
    colimit.pre (filteredLatchingDiagram X n m') (belowIncl h) = _
  apply colimit.ι_pre

@[reassoc]
private theorem filteredLatchingMap_ι {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) (a : latchingIndexBelow n m) :
    colimit.ι (filteredLatchingDiagram X n m) a ≫ filteredLatchingMap f n m =
      f.app a.obj.obj.left ≫ colimit.ι (filteredLatchingDiagram Y n m) a := by
  apply ι_colimMap

private noncomputable def belowTotalInverse (n : ℕ) :
    CategoryTheory.SimplicialObject.latchingIndex n ⥤ latchingIndexBelow n n where
  obj a := ⟨a, a.property.2⟩
  map f := ObjectProperty.homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def belowTotalEquivalence (n : ℕ) :
    latchingIndexBelow n n ≌ CategoryTheory.SimplicialObject.latchingIndex n where
  functor := belowToLatching n n
  inverse := belowTotalInverse n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

private noncomputable def filteredTotalObjectIso
    (X : CategoryTheory.SimplicialObject C) (n : ℕ) :
    filteredLatchingObject X n n ≅ CategoryTheory.SimplicialObject.latchingObject X n :=
  HasColimit.isoOfEquivalence (belowTotalEquivalence n) (Iso.refl _)

private def predecessorLiftFunctor {n m : ℕ} (a : latchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.latchingIndex m ⥤ latchingIndexBelow n m :=
  latchingIndexToPredecessor a ⋙
    CostructuredArrow.proj (belowToLatching n m) a.obj

set_option backward.isDefEq.respectTransparency false in
private noncomputable def predecessorDiagramIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.latchingDiagram X m ≅
      predecessorLiftFunctor a ⋙ filteredLatchingDiagram X n m :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {b c} g => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private noncomputable def predecessorBoundaryToOld
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.latchingObject X m ⟶ filteredLatchingObject X n m :=
  (HasColimit.isoOfNatIso (predecessorDiagramIso X a)).hom ≫
    colimit.pre (filteredLatchingDiagram X n m) (predecessorLiftFunctor a)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem predecessorBoundaryToOld_ι
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.latchingIndex m) :
    CategoryTheory.SimplicialObject.latchingι X m b ≫ predecessorBoundaryToOld X a =
      colimit.ι (filteredLatchingDiagram X n m) ((predecessorLiftFunctor a).obj b) := by
  unfold CategoryTheory.SimplicialObject.latchingι predecessorBoundaryToOld
  rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom]
  rw [Category.assoc, colimit.ι_pre]
  change (𝟙 ((predecessorLiftFunctor a ⋙
      filteredLatchingDiagram X n m).obj b)) ≫
        colimit.ι (filteredLatchingDiagram X n m) ((predecessorLiftFunctor a).obj b) = _
  simp

private noncomputable instance latchingIndexDegree_fintype (n m : ℕ) :
    Fintype (latchingIndexDegree n m) :=
  Fintype.ofFinite _

private noncomputable abbrev stratumBoundaries
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∐ fun _ : latchingIndexDegree n m => CategoryTheory.SimplicialObject.latchingObject X m

private noncomputable abbrev stratumObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∐ fun a : latchingIndexDegree n m => X.obj a.obj.obj.left

private noncomputable def stratumBoundaryToOld
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumBoundaries X n m ⟶ filteredLatchingObject X n m :=
  Sigma.desc fun a => predecessorBoundaryToOld X a

private noncomputable def stratumBoundaryToObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumBoundaries X n m ⟶ stratumObjects X n m :=
  CategoryTheory.Limits.Sigma.map fun a =>
    CategoryTheory.SimplicialObject.latchingMap X m ≫
      X.map (eqToHom (newTargetEq a).symm)

private noncomputable abbrev latchingAttachment
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  pushout (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m)

private noncomputable def stratumBoundaryMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumBoundaries X n m ⟶ stratumBoundaries Y n m :=
  CategoryTheory.Limits.Sigma.map fun _ =>
    (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f

private noncomputable def stratumObjectsMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumObjects X n m ⟶ stratumObjects Y n m :=
  CategoryTheory.Limits.Sigma.map fun a => f.app a.obj.obj.left

set_option backward.isDefEq.respectTransparency false in
private theorem stratumBoundaryToOld_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumBoundaryToOld X n m ≫ filteredLatchingMap f n m =
      stratumBoundaryMap f n m ≫ stratumBoundaryToOld Y n m := by
  apply Sigma.hom_ext
  intro a
  unfold stratumBoundaryToOld stratumBoundaryMap
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
  apply colimit.hom_ext
  intro b
  calc
    CategoryTheory.SimplicialObject.latchingι X m b ≫
          (predecessorBoundaryToOld X a ≫ filteredLatchingMap f n m) =
        colimit.ι (filteredLatchingDiagram X n m) ((predecessorLiftFunctor a).obj b) ≫
          filteredLatchingMap f n m := by
            rw [← Category.assoc, predecessorBoundaryToOld_ι]
    _ = f.app ((predecessorLiftFunctor a).obj b).obj.obj.left ≫
        colimit.ι (filteredLatchingDiagram Y n m) ((predecessorLiftFunctor a).obj b) := by
          rw [filteredLatchingMap_ι]
    _ = f.app b.obj.left ≫
        colimit.ι (filteredLatchingDiagram Y n m) ((predecessorLiftFunctor a).obj b) := by
          rfl
    _ = f.app b.obj.left ≫
        (CategoryTheory.SimplicialObject.latchingι Y m b ≫
          predecessorBoundaryToOld Y a) := by rw [predecessorBoundaryToOld_ι]
    _ = (f.app b.obj.left ≫ CategoryTheory.SimplicialObject.latchingι Y m b) ≫
        predecessorBoundaryToOld Y a := by simp only [Category.assoc]
    _ = (CategoryTheory.SimplicialObject.latchingι X m b ≫
          (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f) ≫
        predecessorBoundaryToOld Y a := by
          rw [CategoryTheory.SimplicialObject.latchingObjectFunctor_map_ι]
    _ = (colimit.ι (CategoryTheory.SimplicialObject.latchingDiagram X m) b ≫
          (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f) ≫
        predecessorBoundaryToOld Y a := by rfl
    _ = colimit.ι (CategoryTheory.SimplicialObject.latchingDiagram X m) b ≫
        ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f ≫
          predecessorBoundaryToOld Y a) := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem stratumBoundaryToObjects_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumBoundaryToObjects X n m ≫ stratumObjectsMap f n m =
      stratumBoundaryMap f n m ≫ stratumBoundaryToObjects Y n m := by
  apply Sigma.hom_ext
  intro a
  unfold stratumBoundaryToObjects stratumObjectsMap stratumBoundaryMap
  rw [Sigma.ι_map_assoc, Sigma.ι_map_assoc, Sigma.ι_map, Sigma.ι_map]
  have hbase :
      (CategoryTheory.SimplicialObject.latchingMap X m ≫
            X.map (eqToHom (newTargetEq a).symm)) ≫ f.app a.obj.obj.left =
        (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f ≫
          (CategoryTheory.SimplicialObject.latchingMap Y m ≫
            Y.map (eqToHom (newTargetEq a).symm)) := by
    calc
      (CategoryTheory.SimplicialObject.latchingMap X m ≫
            X.map (eqToHom (newTargetEq a).symm)) ≫ f.app a.obj.obj.left =
        CategoryTheory.SimplicialObject.latchingMap X m ≫
          (X.map (eqToHom (newTargetEq a).symm) ≫ f.app a.obj.obj.left) := by
            simp only [Category.assoc]
      _ = CategoryTheory.SimplicialObject.latchingMap X m ≫
          (f.app (op ⦋m⦌) ≫ Y.map (eqToHom (newTargetEq a).symm)) := by
            rw [f.naturality]
      _ = (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f ≫
          (CategoryTheory.SimplicialObject.latchingMap Y m ≫
            Y.map (eqToHom (newTargetEq a).symm)) := by
              have hn := CategoryTheory.SimplicialObject.latchingMap_naturality m f
              simpa only [Category.assoc] using congrArg
                (fun t => t ≫ Y.map (eqToHom (newTargetEq a).symm)) hn.symm
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ Sigma.ι (fun a : latchingIndexDegree n m => Y.obj a.obj.obj.left) a)
    hbase

private noncomputable def latchingAttachmentMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    latchingAttachment X n m ⟶ latchingAttachment Y n m :=
  pushout.map
    (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m)
    (stratumBoundaryToOld Y n m) (stratumBoundaryToObjects Y n m)
    (filteredLatchingMap f n m) (stratumObjectsMap f n m)
    (stratumBoundaryMap f n m)
    (stratumBoundaryToOld_naturality f n m)
    (stratumBoundaryToObjects_naturality f n m)

private noncomputable instance latchingPredecessor_finite
    {n m : ℕ} (a : latchingIndexDegree n m) : Finite (latchingPredecessor n m a) :=
  Finite.of_injective (fun x => x.left) (fun x y h => by
    apply CostructuredArrow.obj_ext _ _ h
    exact Subsingleton.elim _ _)

private noncomputable instance latchingPredecessor_fintype
    {n m : ℕ} (a : latchingIndexDegree n m) : Fintype (latchingPredecessor n m a) :=
  Fintype.ofFinite _

private instance latchingPredecessor_isThin
    {n m : ℕ} (a : latchingIndexDegree n m) : Quiver.IsThin (latchingPredecessor n m a) :=
  fun _ _ => inferInstance

private abbrev predecessorRestrictedDiagram
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    latchingPredecessor n m a ⥤ C :=
  CostructuredArrow.proj (belowToLatching n m) a.obj ⋙
    filteredLatchingDiagram X n m

private noncomputable abbrev predecessorBoundary
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) : C :=
  colimit (predecessorRestrictedDiagram X a)

private noncomputable abbrev rawStratumBoundaries
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∐ fun a : latchingIndexDegree n m => predecessorBoundary X a

private noncomputable def predecessorRawToOld
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    predecessorBoundary X a ⟶ filteredLatchingObject X n m :=
  colimit.pre (filteredLatchingDiagram X n m)
    (CostructuredArrow.proj (belowToLatching n m) a.obj)

@[reassoc]
private theorem predecessorRawToOld_ι
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    colimit.ι (predecessorRestrictedDiagram X a) x ≫ predecessorRawToOld X a =
      colimit.ι (filteredLatchingDiagram X n m) x.left := by
  apply colimit.ι_pre

set_option backward.isDefEq.respectTransparency false in
private def predecessorToNewCocone
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    Cocone (predecessorRestrictedDiagram X a) where
  pt := X.obj a.obj.obj.left
  ι :=
    { app := fun x => X.map x.hom.hom.left
      naturality := by
        intro x y g
        change X.map g.left.hom.hom.left ≫ X.map y.hom.hom.left =
          X.map x.hom.hom.left ≫ 𝟙 _
        rw [Category.comp_id, ← X.map_comp]
        apply X.congr_map
        have hw := congrArg (fun z => z.hom.left) (CostructuredArrow.w g)
        change g.left.hom.hom.left ≫ y.hom.hom.left = x.hom.hom.left at hw
        exact hw }

private noncomputable def predecessorRawToObject
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    predecessorBoundary X a ⟶ X.obj a.obj.obj.left :=
  colimit.desc (predecessorRestrictedDiagram X a) (predecessorToNewCocone X a)

@[reassoc]
private theorem predecessorRawToObject_ι
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    colimit.ι (predecessorRestrictedDiagram X a) x ≫ predecessorRawToObject X a =
      X.map x.hom.hom.left := by
  apply colimit.ι_desc

private noncomputable def rawBoundaryToOld
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawStratumBoundaries X n m ⟶ filteredLatchingObject X n m :=
  Sigma.desc fun a => predecessorRawToOld X a

private noncomputable def rawBoundaryToObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawStratumBoundaries X n m ⟶ stratumObjects X n m :=
  CategoryTheory.Limits.Sigma.map fun a => predecessorRawToObject X a

private noncomputable abbrev rawLatchingAttachment
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  pushout (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)

private def oldEmbedding (n m : ℕ) :
    latchingIndexBelow n m ⥤ latchingIndexBelow n (m + 1) :=
  belowIncl (n := n) (Nat.le_succ m)

private def newEmbedding (n m : ℕ) :
    latchingIndexDegree n m ⥤ latchingIndexBelow n (m + 1) where
  obj a := ⟨a.obj, by rw [a.property]; exact Nat.lt_succ_self m⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem latching_hom_degree_le {n : ℕ}
    {a b : CategoryTheory.SimplicialObject.latchingIndex n} (g : a ⟶ b) :
    a.obj.left.unop.len ≤ b.obj.left.unop.len := by
  have hfac : b.obj.hom.unop ≫ g.hom.left.unop = a.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simp
  let _ : Epi (b.obj.hom.unop ≫ g.hom.left.unop) := by
    rw [hfac]
    exact a.property.1
  let _ : Epi g.hom.left.unop :=
    CategoryTheory.epi_of_epi b.obj.hom.unop g.hom.left.unop
  exact SimplexCategory.len_le_of_epi g.hom.left.unop

private theorem below_succ_old_or_new {n m : ℕ} (a : latchingIndexBelow n (m + 1)) :
    a.obj.obj.left.unop.len < m ∨ a.obj.obj.left.unop.len = m := by
  exact Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp a.property)

private def oldPart {n m : ℕ} (a : latchingIndexBelow n (m + 1))
    (h : a.obj.obj.left.unop.len < m) : latchingIndexBelow n m :=
  ⟨a.obj, h⟩

private def newPart {n m : ℕ} (a : latchingIndexBelow n (m + 1))
    (h : ¬ a.obj.obj.left.unop.len < m) : latchingIndexDegree n m :=
  ⟨a.obj, le_antisymm (Nat.lt_succ_iff.mp a.property) (Nat.le_of_not_gt h)⟩

private noncomputable def attachmentLeg
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) :
    (filteredLatchingDiagram X n (m + 1)).obj a ⟶ rawLatchingAttachment X n m :=
  if h : a.obj.obj.left.unop.len < m then
    colimit.ι (filteredLatchingDiagram X n m) (oldPart a h) ≫
      pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)
  else
    Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) (newPart a h) ≫
      pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)

@[simp]
private theorem attachmentLeg_old
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) (h : a.obj.obj.left.unop.len < m) :
    attachmentLeg X a =
      colimit.ι (filteredLatchingDiagram X n m) (oldPart a h) ≫
        pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) := by
  simp [attachmentLeg, h]
  congr

@[simp]
private theorem attachmentLeg_new
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) (h : ¬ a.obj.obj.left.unop.len < m) :
    attachmentLeg X a =
      Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) (newPart a h) ≫
        pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) := by
  simp [attachmentLeg, h]
  congr

private theorem oldEmbedding_oldPart_eq {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) (h : a.obj.obj.left.unop.len < m) :
    (oldEmbedding n m).obj (oldPart a h) = a :=
  ObjectProperty.FullSubcategory.ext rfl

private theorem newEmbedding_newPart_eq {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) (h : ¬ a.obj.obj.left.unop.len < m) :
    (newEmbedding n m).obj (newPart a h) = a :=
  ObjectProperty.FullSubcategory.ext rfl

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentLeg_naturality
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    {a b : latchingIndexBelow n (m + 1)} (g : a ⟶ b) :
    (filteredLatchingDiagram X n (m + 1)).map g ≫ attachmentLeg X b =
      attachmentLeg X a := by
  by_cases ha : a.obj.obj.left.unop.len < m
  · by_cases hb : b.obj.obj.left.unop.len < m
    · let gOld : oldPart a ha ⟶ oldPart b hb := ObjectProperty.homMk g.hom
      have hw := colimit.w (filteredLatchingDiagram X n m) gOld
      have hw' := congrArg
        (fun t => t ≫ pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)) hw
      rw [attachmentLeg_old X a ha, attachmentLeg_old X b hb]
      change (filteredLatchingDiagram X n m).map gOld ≫
          colimit.ι (filteredLatchingDiagram X n m) (oldPart b hb) ≫
            pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) = _
      simpa only [Category.assoc] using hw'
    · let bNew := newPart b hb
      let xleft := oldPart a ha
      let xhom : (belowToLatching n m).obj xleft ⟶ bNew.obj :=
        ObjectProperty.homMk g.hom.hom
      let x : latchingPredecessor n m bNew := CostructuredArrow.mk xhom
      let preι := colimit.ι (predecessorRestrictedDiagram X bNew) x ≫
        Sigma.ι (fun c : latchingIndexDegree n m => predecessorBoundary X c) bNew
      have hleft : preι ≫ rawBoundaryToOld X n m =
          colimit.ι (filteredLatchingDiagram X n m) (oldPart a ha) := by
        dsimp [preι, rawBoundaryToOld]
        rw [Category.assoc, Sigma.ι_comp_desc]
        apply predecessorRawToOld_ι
      have hright : preι ≫ rawBoundaryToObjects X n m =
          X.map g.hom.hom.left ≫
            Sigma.ι (fun c : latchingIndexDegree n m => X.obj c.obj.obj.left) bNew := by
        dsimp [preι, rawBoundaryToObjects]
        rw [Category.assoc, Sigma.ι_map]
        have hι := predecessorRawToObject_ι X bNew x
        change colimit.ι (predecessorRestrictedDiagram X bNew) x ≫
          predecessorRawToObject X bNew = X.map g.hom.hom.left at hι
        simpa only [Category.assoc] using congrArg
          (fun t => t ≫
            Sigma.ι (fun c : latchingIndexDegree n m => X.obj c.obj.obj.left) bNew) hι
      have hcondition :
          rawBoundaryToOld X n m ≫
              pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) =
            rawBoundaryToObjects X n m ≫
              pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) :=
        pushout.condition
      have hcond := congrArg (fun t => preι ≫ t)
        hcondition
      have hcond' : (preι ≫ rawBoundaryToOld X n m) ≫
          pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) =
        (preι ≫ rawBoundaryToObjects X n m) ≫
          pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) := by
        simpa only [Category.assoc] using hcond
      rw [hleft, hright] at hcond'
      rw [attachmentLeg_old X a ha, attachmentLeg_new X b hb]
      change X.map g.hom.hom.left ≫
          (Sigma.ι (fun c : latchingIndexDegree n m => X.obj c.obj.obj.left) bNew ≫
            pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)) = _
      simpa only [Category.assoc] using hcond'.symm
  · by_cases hb : b.obj.obj.left.unop.len < m
    · have hle := latching_hom_degree_le g.hom
      have haeq := (newPart a ha).property
      omega
    · let aNew := newPart a ha
      let bNew := newPart b hb
      let gNew : aNew ⟶ bNew := ObjectProperty.homMk g.hom
      have hab : aNew = bNew := eq_of_hom_in_degree gNew
      have habObj : a.obj = b.obj := congrArg (fun z => z.obj) hab
      have habBelow : a = b := ObjectProperty.FullSubcategory.ext habObj
      subst b
      have hg : g = 𝟙 a := Subsingleton.elim _ _
      subst g
      simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def attachmentCocone
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    Cocone (filteredLatchingDiagram X n (m + 1)) where
  pt := rawLatchingAttachment X n m
  ι :=
    { app := attachmentLeg X
      naturality := by
        intro a b g
        change (filteredLatchingDiagram X n (m + 1)).map g ≫ attachmentLeg X b =
          attachmentLeg X a ≫ 𝟙 _
        rw [Category.comp_id]
        exact attachmentLeg_naturality X g }

set_option backward.isDefEq.respectTransparency false in
private def attachmentOldCocone
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1))) :
    Cocone (filteredLatchingDiagram X n m) where
  pt := s.pt
  ι :=
    { app := fun a => s.ι.app ((oldEmbedding n m).obj a)
      naturality := by
        intro a b g
        simpa [filteredLatchingDiagram, oldEmbedding, belowIncl] using
          s.w ((oldEmbedding n m).map g) }

private noncomputable def attachmentOldDesc
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1))) :
    filteredLatchingObject X n m ⟶ s.pt :=
  colimit.desc (filteredLatchingDiagram X n m) (attachmentOldCocone X s)

private noncomputable def attachmentNewDesc
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1))) :
    stratumObjects X n m ⟶ s.pt :=
  Sigma.desc fun a => s.ι.app ((newEmbedding n m).obj a)

private def predecessorStepHom {n m : ℕ} {a : latchingIndexDegree n m}
    (x : latchingPredecessor n m a) :
    (oldEmbedding n m).obj x.left ⟶ (newEmbedding n m).obj a :=
  ObjectProperty.homMk x.hom

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentDesc_compat
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1))) :
    rawBoundaryToOld X n m ≫ attachmentOldDesc X s =
      rawBoundaryToObjects X n m ≫ attachmentNewDesc X s := by
  apply Sigma.hom_ext
  intro a
  unfold rawBoundaryToOld rawBoundaryToObjects attachmentNewDesc
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
  apply colimit.hom_ext
  intro x
  calc
    colimit.ι (predecessorRestrictedDiagram X a) x ≫
          (predecessorRawToOld X a ≫ attachmentOldDesc X s) =
        colimit.ι (filteredLatchingDiagram X n m) x.left ≫
          attachmentOldDesc X s := by
            rw [← Category.assoc, predecessorRawToOld_ι]
    _ = s.ι.app ((oldEmbedding n m).obj x.left) := by
          apply colimit.ι_desc
    _ = (filteredLatchingDiagram X n (m + 1)).map (predecessorStepHom x) ≫
        s.ι.app ((newEmbedding n m).obj a) := by
          rw [s.w (predecessorStepHom x)]
    _ = X.map x.hom.hom.left ≫ s.ι.app ((newEmbedding n m).obj a) := by rfl
    _ = (colimit.ι (predecessorRestrictedDiagram X a) x ≫
          predecessorRawToObject X a) ≫
        s.ι.app ((newEmbedding n m).obj a) := by
          rw [predecessorRawToObject_ι]
    _ = colimit.ι (predecessorRestrictedDiagram X a) x ≫
        (predecessorRawToObject X a ≫ s.ι.app ((newEmbedding n m).obj a)) := by
          simp only [Category.assoc]

private noncomputable def attachmentDesc
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1))) :
    rawLatchingAttachment X n m ⟶ s.pt :=
  pushout.desc (attachmentOldDesc X s) (attachmentNewDesc X s)
    (attachmentDesc_compat X s)

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentDesc_fac
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cocone (filteredLatchingDiagram X n (m + 1)))
    (a : latchingIndexBelow n (m + 1)) :
    attachmentLeg X a ≫ attachmentDesc X s = s.ι.app a := by
  by_cases h : a.obj.obj.left.unop.len < m
  · rw [attachmentLeg_old X a h]
    dsimp [attachmentDesc, attachmentOldDesc]
    rw [Category.assoc, pushout.inl_desc, colimit.ι_desc]
    cases oldEmbedding_oldPart_eq a h
    rfl
  · rw [attachmentLeg_new X a h]
    dsimp [attachmentDesc, attachmentNewDesc]
    rw [Category.assoc, pushout.inr_desc, Sigma.ι_comp_desc]
    cases newEmbedding_newPart_eq a h
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def attachmentIsColimit
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    IsColimit (attachmentCocone X n m) where
  desc s := attachmentDesc X s
  fac s a := attachmentDesc_fac X s a
  uniq s k hk := by
    apply pushout.hom_ext
    · apply colimit.hom_ext
      intro a
      let z := (oldEmbedding n m).obj a
      have h := (hk z).trans (attachmentDesc_fac X s z).symm
      change attachmentLeg X z ≫ k = attachmentLeg X z ≫ attachmentDesc X s at h
      have hz : z.obj.obj.left.unop.len < m := a.property
      rw [attachmentLeg_old X z hz] at h
      have hza : oldPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
      cases hza
      simpa [z, oldPart, oldEmbedding, attachmentCocone, Category.assoc] using h
    · apply Sigma.hom_ext
      intro a
      let z := (newEmbedding n m).obj a
      have h := (hk z).trans (attachmentDesc_fac X s z).symm
      change attachmentLeg X z ≫ k = attachmentLeg X z ≫ attachmentDesc X s at h
      have hz : ¬ z.obj.obj.left.unop.len < m := by
        change ¬ a.obj.obj.left.unop.len < m
        rw [a.property]
        exact Nat.lt_irrefl m
      rw [attachmentLeg_new X z hz] at h
      have hza : newPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
      cases hza
      simpa [z, newPart, newEmbedding, attachmentCocone, Category.assoc] using h

private noncomputable def attachmentColimitCocone
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    ColimitCocone (filteredLatchingDiagram X n (m + 1)) :=
  ⟨attachmentCocone X n m, attachmentIsColimit X n m⟩

/-- The explicit finite-stratum attachment presents the next filtered latching colimit. -/
private noncomputable def latchingAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawLatchingAttachment X n m ≅ filteredLatchingObject X n (m + 1) :=
  (colimit.isoColimitCocone
    (attachmentColimitCocone X n m)).symm

@[reassoc]
private theorem attachmentLeg_iso_hom
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexBelow n (m + 1)) :
    attachmentLeg X a ≫ (latchingAttachmentIso X n m).hom =
      colimit.ι (filteredLatchingDiagram X n (m + 1)) a := by
  change (attachmentCocone X n m).ι.app a ≫
      (colimit.isoColimitCocone
        (attachmentColimitCocone X n m)).inv = _
  exact colimit.isoColimitCocone_ι_inv (attachmentColimitCocone X n m) a

@[reassoc]
private theorem latchingAttachmentIso_hom_inl
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
        (latchingAttachmentIso X n m).hom =
      filteredLatchingIncl X (Nat.le_succ m) := by
  apply colimit.hom_ext
  intro a
  let z := (oldEmbedding n m).obj a
  have hz : z.obj.obj.left.unop.len < m := a.property
  have hza : oldPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
  have hleg := attachmentLeg_iso_hom X z
  rw [attachmentLeg_old X z hz] at hleg
  have hincl := filteredLatchingIncl_ι X (Nat.le_succ m) a
  have hchain : colimit.ι (filteredLatchingDiagram X n m) (oldPart z hz) ≫
      (pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
        (latchingAttachmentIso X n m).hom) =
      colimit.ι (filteredLatchingDiagram X n m) a ≫
        filteredLatchingIncl X (Nat.le_succ m) := by
    exact (Category.assoc
      (colimit.ι (filteredLatchingDiagram X n m) (oldPart z hz))
      (pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m))
      (latchingAttachmentIso X n m).hom).symm.trans (hleg.trans hincl.symm)
  have hi : HEq (colimit.ι (filteredLatchingDiagram X n m) a)
      (colimit.ι (filteredLatchingDiagram X n m) (oldPart z hz)) := by
    cases hza
    rfl
  apply eq_of_heq
  exact (heq_comp (by rfl) (by rfl) (by rfl) hi (by rfl)).trans
    (heq_of_eq hchain)

@[reassoc]
private theorem latchingAttachmentIso_hom_inr_ι
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
        pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
          (latchingAttachmentIso X n m).hom =
      colimit.ι (filteredLatchingDiagram X n (m + 1)) ((newEmbedding n m).obj a) := by
  let z := (newEmbedding n m).obj a
  have hz : ¬ z.obj.obj.left.unop.len < m := by
    change ¬ a.obj.obj.left.unop.len < m
    rw [a.property]
    exact Nat.lt_irrefl m
  have hza : newPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
  have hleg := attachmentLeg_iso_hom X z
  rw [attachmentLeg_new X z hz] at hleg
  have hchain :
      Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) (newPart z hz) ≫
          (pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
            (latchingAttachmentIso X n m).hom) =
        colimit.ι (filteredLatchingDiagram X n (m + 1)) ((newEmbedding n m).obj a) := by
    dsimp [z]
    exact (Category.assoc
      (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) (newPart z hz))
      (pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m))
      (latchingAttachmentIso X n m).hom).symm.trans hleg
  have hi : HEq
      (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a)
      (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) (newPart z hz)) := by
    cases hza
    rfl
  apply eq_of_heq
  exact (heq_comp (by rfl) (by rfl) (by rfl) hi (by rfl)).trans (heq_of_eq hchain)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def predecessorEquivalenceDiagramIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    (predecessorEquivalence a).functor ⋙
        CategoryTheory.SimplicialObject.latchingDiagram X m ≅
      predecessorRestrictedDiagram X a :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {x y} g => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private noncomputable def predecessorBoundaryIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m) :
    predecessorBoundary X a ≅ CategoryTheory.SimplicialObject.latchingObject X m :=
  HasColimit.isoOfEquivalence (predecessorEquivalence a)
    (predecessorEquivalenceDiagramIso X a)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem predecessorBoundaryIso_ι_hom
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : latchingIndexDegree n m)
    (x : latchingPredecessor n m a) :
    colimit.ι (predecessorRestrictedDiagram X a) x ≫ (predecessorBoundaryIso X a).hom =
      CategoryTheory.SimplicialObject.latchingι X m
        ((predecessorEquivalence a).functor.obj x) := by
  have h := HasColimit.ι_isoOfEquivalence_hom (predecessorEquivalence a)
    (predecessorEquivalenceDiagramIso X a) x
  change _ = (Iso.refl _).inv ≫
    colimit.ι (CategoryTheory.SimplicialObject.latchingDiagram X m)
      ((predecessorEquivalence a).functor.obj x) at h
  simpa [predecessorBoundaryIso, CategoryTheory.SimplicialObject.latchingι] using h

private noncomputable def rawStratumBoundariesIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawStratumBoundaries X n m ≅ stratumBoundaries X n m :=
  (colim : (Discrete (latchingIndexDegree n m) ⥤ C) ⥤ C).mapIso
    (Discrete.natIso fun a => predecessorBoundaryIso X a.as)

@[reassoc]
private theorem rawStratumBoundariesIso_ι_hom
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun a : latchingIndexDegree n m => predecessorBoundary X a) a ≫
        (rawStratumBoundariesIso X n m).hom =
      (predecessorBoundaryIso X a).hom ≫
        Sigma.ι (fun _ : latchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.latchingObject X m) a := by
  apply ι_colimMap

private theorem predecessor_unit_left_map_eq_id {n m : ℕ}
    (a : latchingIndexDegree n m) (x : latchingPredecessor n m a) :
    ((predecessorEquivalence a).unitIso.hom.app x).left.hom.hom.left = 𝟙 _ := by
  dsimp [predecessorEquivalence]
  simp only [CostructuredArrow.eqToHom_left, ObjectProperty.eqToHom_hom]
  change (eqToHom _ : x.left.obj.obj.left ⟶ x.left.obj.obj.left) = 𝟙 _
  exact eqToHom_refl _ _

set_option backward.isDefEq.respectTransparency false in
private theorem predecessorLift_ι_eq
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexDegree n m) (x : latchingPredecessor n m a) :
    colimit.ι (filteredLatchingDiagram X n m)
        ((predecessorLiftFunctor a).obj ((predecessorEquivalence a).functor.obj x)) =
      colimit.ι (filteredLatchingDiagram X n m) x.left := by
  have hw := colimit.w (filteredLatchingDiagram X n m)
    ((predecessorEquivalence a).unitIso.hom.app x).left
  have hu := predecessor_unit_left_map_eq_id a x
  change X.map (((predecessorEquivalence a).unitIso.hom.app x).left.hom.hom.left) ≫
      colimit.ι (filteredLatchingDiagram X n m)
        ((predecessorLiftFunctor a).obj ((predecessorEquivalence a).functor.obj x)) =
    colimit.ι (filteredLatchingDiagram X n m) x.left at hw
  rw [hu, X.map_id, Category.id_comp] at hw
  exact hw

set_option backward.isDefEq.respectTransparency false in
private theorem predecessorBoundaryIso_hom_comp_toOld
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexDegree n m) :
    (predecessorBoundaryIso X a).hom ≫ predecessorBoundaryToOld X a =
      predecessorRawToOld X a := by
  apply colimit.hom_ext
  intro x
  rw [← Category.assoc, predecessorBoundaryIso_ι_hom,
    predecessorBoundaryToOld_ι, predecessorLift_ι_eq,
    predecessorRawToOld_ι]

set_option backward.isDefEq.respectTransparency false in
private theorem predecessorBoundaryIso_hom_comp_toObject
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : latchingIndexDegree n m) :
    (predecessorBoundaryIso X a).hom ≫
        (CategoryTheory.SimplicialObject.latchingMap X m ≫
          X.map (eqToHom (newTargetEq a).symm)) =
      predecessorRawToObject X a := by
  apply colimit.hom_ext
  intro x
  calc
    colimit.ι (predecessorRestrictedDiagram X a) x ≫
          ((predecessorBoundaryIso X a).hom ≫
            (CategoryTheory.SimplicialObject.latchingMap X m ≫
              X.map (eqToHom (newTargetEq a).symm))) =
        (colimit.ι (predecessorRestrictedDiagram X a) x ≫
          (predecessorBoundaryIso X a).hom) ≫
            CategoryTheory.SimplicialObject.latchingMap X m ≫
              X.map (eqToHom (newTargetEq a).symm) := by
                simp only [Category.assoc]
    _ = CategoryTheory.SimplicialObject.latchingι X m
          ((predecessorEquivalence a).functor.obj x) ≫
            CategoryTheory.SimplicialObject.latchingMap X m ≫
              X.map (eqToHom (newTargetEq a).symm) := by
                rw [predecessorBoundaryIso_ι_hom]
    _ = X.map (predecessorCanonicalHom x) ≫
          X.map (eqToHom (newTargetEq a).symm) := by
            have hι := CategoryTheory.SimplicialObject.latchingMap_ι X m
              ((predecessorEquivalence a).functor.obj x)
            change CategoryTheory.SimplicialObject.latchingι X m
                ((predecessorEquivalence a).functor.obj x) ≫
                  CategoryTheory.SimplicialObject.latchingMap X m =
              X.map (predecessorCanonicalHom x) at hι
            simpa only [Category.assoc] using congrArg
              (fun t => t ≫ X.map (eqToHom (newTargetEq a).symm)) hι
    _ = X.map x.hom.hom.left := predecessor_structure_map X x
    _ = colimit.ι (predecessorRestrictedDiagram X a) x ≫
          predecessorRawToObject X a :=
      (predecessorRawToObject_ι X a x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem rawBoundaryToOld_eq
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawBoundaryToOld X n m =
      (rawStratumBoundariesIso X n m).hom ≫ stratumBoundaryToOld X n m := by
  apply Sigma.hom_ext
  intro a
  unfold rawBoundaryToOld stratumBoundaryToOld
  rw [Sigma.ι_comp_desc]
  symm
  calc
    Sigma.ι (fun a : latchingIndexDegree n m => predecessorBoundary X a) a ≫
          ((rawStratumBoundariesIso X n m).hom ≫
            Sigma.desc (fun a => predecessorBoundaryToOld X a)) =
        (Sigma.ι (fun a : latchingIndexDegree n m => predecessorBoundary X a) a ≫
          (rawStratumBoundariesIso X n m).hom) ≫
            Sigma.desc (fun a => predecessorBoundaryToOld X a) := by
              simp only [Category.assoc]
    _ = ((predecessorBoundaryIso X a).hom ≫
          Sigma.ι (fun _ : latchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.latchingObject X m) a) ≫
        Sigma.desc (fun a => predecessorBoundaryToOld X a) := by
          rw [rawStratumBoundariesIso_ι_hom]
    _ = (predecessorBoundaryIso X a).hom ≫ predecessorBoundaryToOld X a := by
          rw [Category.assoc, Sigma.ι_comp_desc]
    _ = predecessorRawToOld X a :=
      predecessorBoundaryIso_hom_comp_toOld X a

set_option backward.isDefEq.respectTransparency false in
private theorem rawBoundaryToObjects_eq
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawBoundaryToObjects X n m =
      (rawStratumBoundariesIso X n m).hom ≫ stratumBoundaryToObjects X n m := by
  apply Sigma.hom_ext
  intro a
  unfold rawBoundaryToObjects stratumBoundaryToObjects
  rw [Sigma.ι_map]
  symm
  calc
    Sigma.ι (fun a : latchingIndexDegree n m => predecessorBoundary X a) a ≫
          ((rawStratumBoundariesIso X n m).hom ≫
            CategoryTheory.Limits.Sigma.map (fun a =>
              CategoryTheory.SimplicialObject.latchingMap X m ≫
                X.map (eqToHom (newTargetEq a).symm))) =
        (Sigma.ι (fun a : latchingIndexDegree n m => predecessorBoundary X a) a ≫
          (rawStratumBoundariesIso X n m).hom) ≫
            CategoryTheory.Limits.Sigma.map (fun a =>
              CategoryTheory.SimplicialObject.latchingMap X m ≫
                X.map (eqToHom (newTargetEq a).symm)) := by
                  simp only [Category.assoc]
    _ = ((predecessorBoundaryIso X a).hom ≫
          Sigma.ι (fun _ : latchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.latchingObject X m) a) ≫
        CategoryTheory.Limits.Sigma.map (fun a =>
          CategoryTheory.SimplicialObject.latchingMap X m ≫
            X.map (eqToHom (newTargetEq a).symm)) := by
              rw [rawStratumBoundariesIso_ι_hom]
    _ = ((predecessorBoundaryIso X a).hom ≫
          (CategoryTheory.SimplicialObject.latchingMap X m ≫
            X.map (eqToHom (newTargetEq a).symm))) ≫
        Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a := by
          rw [Category.assoc, Sigma.ι_map]
          simp only [← Category.assoc]
    _ = predecessorRawToObject X a ≫
        Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a := by
          rw [predecessorBoundaryIso_hom_comp_toObject]

private noncomputable def rawToStandardAttachmentMap
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawLatchingAttachment X n m ⟶ latchingAttachment X n m :=
  pushout.map
    (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m)
    (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m)
    (𝟙 _) (𝟙 _) (rawStratumBoundariesIso X n m).hom
    (by simpa using rawBoundaryToOld_eq X n m)
    (by simpa using rawBoundaryToObjects_eq X n m)

private noncomputable instance rawToStandardAttachmentMap_isIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    IsIso (rawToStandardAttachmentMap X n m) := by
  dsimp [rawToStandardAttachmentMap]
  infer_instance

/-- Replacing each raw predecessor boundary by the ordinary degree-`m`
latching object does not change the stratum attachment. -/
private noncomputable def rawToStandardAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawLatchingAttachment X n m ≅ latchingAttachment X n m :=
  asIso (rawToStandardAttachmentMap X n m)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_hom_inl
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
        (rawToStandardAttachmentIso X n m).hom =
      pushout.inl (stratumBoundaryToOld X n m)
        (stratumBoundaryToObjects X n m) := by
  change pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
      rawToStandardAttachmentMap X n m = _
  unfold rawToStandardAttachmentMap
  rw [pushout.inl_desc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_hom_inr
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
        (rawToStandardAttachmentIso X n m).hom =
      pushout.inr (stratumBoundaryToOld X n m)
        (stratumBoundaryToObjects X n m) := by
  change pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) ≫
      rawToStandardAttachmentMap X n m = _
  unfold rawToStandardAttachmentMap
  rw [pushout.inr_desc, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_inv_inl
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        (rawToStandardAttachmentIso X n m).inv =
      pushout.inl (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) := by
  apply (cancel_mono (rawToStandardAttachmentIso X n m).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    rawToStandardAttachmentIso_hom_inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_inv_inr
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inr (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        (rawToStandardAttachmentIso X n m).inv =
      pushout.inr (rawBoundaryToOld X n m) (rawBoundaryToObjects X n m) := by
  apply (cancel_mono (rawToStandardAttachmentIso X n m).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    rawToStandardAttachmentIso_hom_inr]

/-- The standard finite coproduct attachment presents the next filtered
latching colimit. -/
private noncomputable def standardLatchingAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    latchingAttachment X n m ≅ filteredLatchingObject X n (m + 1) :=
  (rawToStandardAttachmentIso X n m).symm ≪≫ latchingAttachmentIso X n m

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem standardLatchingAttachmentIso_hom_inl
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        (standardLatchingAttachmentIso X n m).hom =
      filteredLatchingIncl X (Nat.le_succ m) := by
  change pushout.inl (stratumBoundaryToOld X n m)
        (stratumBoundaryToObjects X n m) ≫
      (rawToStandardAttachmentIso X n m).inv ≫
        (latchingAttachmentIso X n m).hom = _
  rw [← Category.assoc, rawToStandardAttachmentIso_inv_inl,
    latchingAttachmentIso_hom_inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem standardLatchingAttachmentIso_hom_inr_ι
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
        pushout.inr (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
          (standardLatchingAttachmentIso X n m).hom =
      colimit.ι (filteredLatchingDiagram X n (m + 1))
        ((newEmbedding n m).obj a) := by
  change Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
      pushout.inr (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        (rawToStandardAttachmentIso X n m).inv ≫
          (latchingAttachmentIso X n m).hom = _
  rw [rawToStandardAttachmentIso_inv_inr_assoc]
  exact latchingAttachmentIso_hom_inr_ι X n m a

set_option backward.isDefEq.respectTransparency false in
private theorem filteredLatchingIncl_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m m' : ℕ} (h : m ≤ m') :
    filteredLatchingIncl X h ≫ filteredLatchingMap f n m' =
      filteredLatchingMap f n m ≫ filteredLatchingIncl Y h := by
  apply colimit.hom_ext
  intro a
  calc
    colimit.ι (filteredLatchingDiagram X n m) a ≫
          (filteredLatchingIncl X h ≫ filteredLatchingMap f n m') =
        colimit.ι (filteredLatchingDiagram X n m') ((belowIncl h).obj a) ≫
          filteredLatchingMap f n m' := by
            rw [← Category.assoc, filteredLatchingIncl_ι]
    _ = f.app a.obj.obj.left ≫
        colimit.ι (filteredLatchingDiagram Y n m') ((belowIncl h).obj a) := by
          have hmap := filteredLatchingMap_ι f n m' ((belowIncl h).obj a)
          change colimit.ι (filteredLatchingDiagram X n m') ((belowIncl h).obj a) ≫
              filteredLatchingMap f n m' =
            f.app a.obj.obj.left ≫
              colimit.ι (filteredLatchingDiagram Y n m') ((belowIncl h).obj a) at hmap
          exact hmap
    _ = f.app a.obj.obj.left ≫
        (colimit.ι (filteredLatchingDiagram Y n m) a ≫
          filteredLatchingIncl Y h) := by rw [filteredLatchingIncl_ι]
    _ = (colimit.ι (filteredLatchingDiagram X n m) a ≫
          filteredLatchingMap f n m) ≫ filteredLatchingIncl Y h := by
            rw [filteredLatchingMap_ι, Category.assoc]
    _ = colimit.ι (filteredLatchingDiagram X n m) a ≫
        (filteredLatchingMap f n m ≫ filteredLatchingIncl Y h) := by
          simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem latchingAttachmentMap_inl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        latchingAttachmentMap f n m =
      filteredLatchingMap f n m ≫
        pushout.inl (stratumBoundaryToOld Y n m)
          (stratumBoundaryToObjects Y n m) := by
  unfold latchingAttachmentMap
  rw [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem latchingAttachmentMap_inr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inr (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        latchingAttachmentMap f n m =
      stratumObjectsMap f n m ≫
        pushout.inr (stratumBoundaryToOld Y n m)
          (stratumBoundaryToObjects Y n m) := by
  unfold latchingAttachmentMap
  rw [pushout.inr_desc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the standard attachment presentation. -/
private theorem standardLatchingAttachmentIso_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (standardLatchingAttachmentIso X n m).hom ≫ filteredLatchingMap f n (m + 1) =
      latchingAttachmentMap f n m ≫ (standardLatchingAttachmentIso Y n m).hom := by
  apply pushout.hom_ext
  · calc
      pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
            ((standardLatchingAttachmentIso X n m).hom ≫
              filteredLatchingMap f n (m + 1)) =
          filteredLatchingIncl X (Nat.le_succ m) ≫
            filteredLatchingMap f n (m + 1) := by
              rw [← Category.assoc, standardLatchingAttachmentIso_hom_inl]
      _ = filteredLatchingMap f n m ≫
          filteredLatchingIncl Y (Nat.le_succ m) :=
        filteredLatchingIncl_naturality f (Nat.le_succ m)
      _ = filteredLatchingMap f n m ≫
          (pushout.inl (stratumBoundaryToOld Y n m)
              (stratumBoundaryToObjects Y n m) ≫
            (standardLatchingAttachmentIso Y n m).hom) := by
              rw [standardLatchingAttachmentIso_hom_inl]
      _ = (pushout.inl (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m) ≫
            latchingAttachmentMap f n m) ≫
          (standardLatchingAttachmentIso Y n m).hom := by
            rw [latchingAttachmentMap_inl, Category.assoc]
      _ = pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m) ≫
          (latchingAttachmentMap f n m ≫
            (standardLatchingAttachmentIso Y n m).hom) := by
              simp only [Category.assoc]
  · apply Sigma.hom_ext
    intro a
    calc
      Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
            pushout.inr (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m) ≫
            ((standardLatchingAttachmentIso X n m).hom ≫
              filteredLatchingMap f n (m + 1)) =
          colimit.ι (filteredLatchingDiagram X n (m + 1))
              ((newEmbedding n m).obj a) ≫
            filteredLatchingMap f n (m + 1) := by
              simpa only [Category.assoc] using
                standardLatchingAttachmentIso_hom_inr_ι_assoc X n m a
                  (filteredLatchingMap f n (m + 1))
      _ = f.app a.obj.obj.left ≫
          colimit.ι (filteredLatchingDiagram Y n (m + 1))
            ((newEmbedding n m).obj a) := by
              have hmap := filteredLatchingMap_ι f n (m + 1)
                ((newEmbedding n m).obj a)
              change colimit.ι (filteredLatchingDiagram X n (m + 1))
                    ((newEmbedding n m).obj a) ≫
                  filteredLatchingMap f n (m + 1) =
                f.app a.obj.obj.left ≫
                  colimit.ι (filteredLatchingDiagram Y n (m + 1))
                    ((newEmbedding n m).obj a) at hmap
              exact hmap
      _ = f.app a.obj.obj.left ≫
          (Sigma.ι (fun a : latchingIndexDegree n m => Y.obj a.obj.obj.left) a ≫
            pushout.inr (stratumBoundaryToOld Y n m)
              (stratumBoundaryToObjects Y n m) ≫
            (standardLatchingAttachmentIso Y n m).hom) := by
              rw [standardLatchingAttachmentIso_hom_inr_ι]
      _ = (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
              stratumObjectsMap f n m ≫
              pushout.inr (stratumBoundaryToOld Y n m)
                (stratumBoundaryToObjects Y n m)) ≫
            (standardLatchingAttachmentIso Y n m).hom := by
              unfold stratumObjectsMap
              rw [Sigma.ι_map_assoc]
              simp only [Category.assoc]
      _ = (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
              pushout.inr (stratumBoundaryToOld X n m)
                (stratumBoundaryToObjects X n m) ≫
              latchingAttachmentMap f n m) ≫
            (standardLatchingAttachmentIso Y n m).hom := by
              rw [latchingAttachmentMap_inr]
      _ = Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
          pushout.inr (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m) ≫
          (latchingAttachmentMap f n m ≫
            (standardLatchingAttachmentIso Y n m).hom) := by
              simp only [Category.assoc]

/-- The first intermediate object in the two-step attachment-map factorization. -/
private noncomputable abbrev attachmentIntermediate
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  pushout (filteredLatchingMap f n m)
    (pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m))

/-- The first factor, a cobase change of the filtered comparison at stage `m`. -/
private noncomputable def attachmentFirstMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    latchingAttachment X n m ⟶ attachmentIntermediate f n m :=
  pushout.inr (filteredLatchingMap f n m)
    (pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m))

/-- The second factor from the intermediate attachment to the target attachment. -/
private noncomputable def attachmentSecondMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentIntermediate f n m ⟶ latchingAttachment Y n m :=
  pushout.desc
    (pushout.inl (stratumBoundaryToOld Y n m) (stratumBoundaryToObjects Y n m))
    (latchingAttachmentMap f n m)
    (latchingAttachmentMap_inl f n m).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem attachmentSecondMap_inl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inl (filteredLatchingMap f n m)
          (pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m)) ≫
        attachmentSecondMap f n m =
      pushout.inl (stratumBoundaryToOld Y n m)
        (stratumBoundaryToObjects Y n m) := by
  apply pushout.inl_desc

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem attachmentSecondMap_inr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫ attachmentSecondMap f n m =
      latchingAttachmentMap f n m := by
  apply pushout.inr_desc

/-- The attachment comparison is the displayed two-step composite. -/
private theorem attachmentMap_factorization
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫ attachmentSecondMap f n m =
      latchingAttachmentMap f n m :=
  attachmentSecondMap_inr f n m

/-- The first factor is exhibited by its canonical pushout square. -/
private theorem attachmentFirstMap_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPushout
      (filteredLatchingMap f n m)
      (pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m))
      (pushout.inl (filteredLatchingMap f n m)
        (pushout.inl (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m)))
      (attachmentFirstMap f n m) := by
  exact IsPushout.of_hasPushout _ _

@[reassoc]
private theorem attachmentFirstMap_condition
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    filteredLatchingMap f n m ≫
        pushout.inl (filteredLatchingMap f n m)
          (pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m)) =
      pushout.inl (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m) ≫
        attachmentFirstMap f n m := by
  apply pushout.condition

/-- `R = E_X ⨿_{B_X} B_Y`, the source of the second cobase change. -/
private noncomputable abbrev relativeStratumSource
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  pushout (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m)

/-- The finite-stratum relative map `R ⟶ E_Y`. -/
private noncomputable def relativeStratumMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumSource f n m ⟶ stratumObjects Y n m :=
  pushout.desc (stratumObjectsMap f n m) (stratumBoundaryToObjects Y n m)
    (stratumBoundaryToObjects_naturality f n m)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem relativeStratumMap_inl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inl (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        relativeStratumMap f n m =
      stratumObjectsMap f n m := by
  apply pushout.inl_desc

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem relativeStratumMap_inr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inr (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        relativeStratumMap f n m =
      stratumBoundaryToObjects Y n m := by
  apply pushout.inr_desc

private theorem relativeStratumToIntermediate_compat
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumBoundaryToObjects X n m ≫
        (pushout.inr (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m) =
      stratumBoundaryMap f n m ≫
        (stratumBoundaryToOld Y n m ≫
          pushout.inl (filteredLatchingMap f n m)
            (pushout.inl (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m))) := by
  calc
    stratumBoundaryToObjects X n m ≫
          (pushout.inr (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m) =
        (stratumBoundaryToOld X n m ≫
            pushout.inl (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m)) ≫ attachmentFirstMap f n m := by
          rw [← Category.assoc, pushout.condition]
    _ = stratumBoundaryToOld X n m ≫
        (filteredLatchingMap f n m ≫
          pushout.inl (filteredLatchingMap f n m)
            (pushout.inl (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m))) := by
          unfold attachmentFirstMap
          rw [Category.assoc, pushout.condition]
    _ = (stratumBoundaryMap f n m ≫ stratumBoundaryToOld Y n m) ≫
        pushout.inl (filteredLatchingMap f n m)
          (pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m)) := by
          rw [← Category.assoc, stratumBoundaryToOld_naturality]
    _ = stratumBoundaryMap f n m ≫
        (stratumBoundaryToOld Y n m ≫
          pushout.inl (filteredLatchingMap f n m)
            (pushout.inl (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m))) := by
          simp only [Category.assoc]

/-- The map `R ⟶ T` in the second pushout square. -/
private noncomputable def relativeStratumToIntermediate
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumSource f n m ⟶ attachmentIntermediate f n m :=
  pushout.desc
    (pushout.inr (stratumBoundaryToOld X n m)
      (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m)
    (stratumBoundaryToOld Y n m ≫
      pushout.inl (filteredLatchingMap f n m)
        (pushout.inl (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m)))
    (relativeStratumToIntermediate_compat f n m)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem relativeStratumToIntermediate_inl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inl (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        relativeStratumToIntermediate f n m =
      pushout.inr (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m := by
  apply pushout.inl_desc

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem relativeStratumToIntermediate_inr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inr (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        relativeStratumToIntermediate f n m =
      stratumBoundaryToOld Y n m ≫
        pushout.inl (filteredLatchingMap f n m)
          (pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m)) := by
  apply pushout.inr_desc

private theorem attachmentFirstOuter_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPushout
      (stratumBoundaryToOld X n m ≫ filteredLatchingMap f n m)
      (stratumBoundaryToObjects X n m)
      (pushout.inl (filteredLatchingMap f n m)
        (pushout.inl (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m)))
      (pushout.inr (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m) := by
  exact (IsPushout.of_hasPushout
    (stratumBoundaryToOld X n m) (stratumBoundaryToObjects X n m)).paste_horiz
      (attachmentFirstMap_isPushout f n m)

private theorem boundaryToOld_relativeStratum_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPushout
      (stratumBoundaryToOld Y n m)
      (pushout.inr (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m))
      (pushout.inl (filteredLatchingMap f n m)
        (pushout.inl (stratumBoundaryToOld X n m)
          (stratumBoundaryToObjects X n m)))
      (relativeStratumToIntermediate f n m) := by
  have hOuter := attachmentFirstOuter_isPushout f n m
  rw [stratumBoundaryToOld_naturality f n m] at hOuter
  rw [← relativeStratumToIntermediate_inl f n m] at hOuter
  exact hOuter.of_left (relativeStratumToIntermediate_inr f n m).symm
    (IsPushout.of_hasPushout
      (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m)).flip

private theorem relativeStratum_secondMap_comm
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumToIntermediate f n m ≫ attachmentSecondMap f n m =
      relativeStratumMap f n m ≫
        pushout.inr (stratumBoundaryToOld Y n m)
          (stratumBoundaryToObjects Y n m) := by
  apply pushout.hom_ext
  · calc
      pushout.inl (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
            (relativeStratumToIntermediate f n m ≫ attachmentSecondMap f n m) =
          (pushout.inr (stratumBoundaryToOld X n m)
              (stratumBoundaryToObjects X n m) ≫ attachmentFirstMap f n m) ≫
            attachmentSecondMap f n m := by
              rw [← Category.assoc, relativeStratumToIntermediate_inl]
      _ = pushout.inr (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m) ≫
          latchingAttachmentMap f n m := by
            rw [Category.assoc, attachmentSecondMap_inr]
      _ = stratumObjectsMap f n m ≫
          pushout.inr (stratumBoundaryToOld Y n m)
            (stratumBoundaryToObjects Y n m) := latchingAttachmentMap_inr f n m
      _ = (pushout.inl (stratumBoundaryToObjects X n m)
              (stratumBoundaryMap f n m) ≫ relativeStratumMap f n m) ≫
          pushout.inr (stratumBoundaryToOld Y n m)
            (stratumBoundaryToObjects Y n m) := by
              rw [relativeStratumMap_inl]
      _ = pushout.inl (stratumBoundaryToObjects X n m)
            (stratumBoundaryMap f n m) ≫
          (relativeStratumMap f n m ≫
            pushout.inr (stratumBoundaryToOld Y n m)
              (stratumBoundaryToObjects Y n m)) := by
                simp only [Category.assoc]
  · calc
      pushout.inr (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
            (relativeStratumToIntermediate f n m ≫ attachmentSecondMap f n m) =
          (stratumBoundaryToOld Y n m ≫
              pushout.inl (filteredLatchingMap f n m)
                (pushout.inl (stratumBoundaryToOld X n m)
                  (stratumBoundaryToObjects X n m))) ≫
            attachmentSecondMap f n m := by
              rw [← Category.assoc, relativeStratumToIntermediate_inr]
      _ = stratumBoundaryToOld Y n m ≫
          pushout.inl (stratumBoundaryToOld Y n m)
            (stratumBoundaryToObjects Y n m) := by
              rw [Category.assoc, attachmentSecondMap_inl]
      _ = stratumBoundaryToObjects Y n m ≫
          pushout.inr (stratumBoundaryToOld Y n m)
            (stratumBoundaryToObjects Y n m) := pushout.condition
      _ = (pushout.inr (stratumBoundaryToObjects X n m)
              (stratumBoundaryMap f n m) ≫ relativeStratumMap f n m) ≫
          pushout.inr (stratumBoundaryToOld Y n m)
            (stratumBoundaryToObjects Y n m) := by
              rw [relativeStratumMap_inr]
      _ = pushout.inr (stratumBoundaryToObjects X n m)
            (stratumBoundaryMap f n m) ≫
          (relativeStratumMap f n m ≫
            pushout.inr (stratumBoundaryToOld Y n m)
              (stratumBoundaryToObjects Y n m)) := by
                simp only [Category.assoc]

/-- The second factor is the cobase change of the finite-stratum relative map. -/
private theorem attachmentSecondMap_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPushout
      (relativeStratumToIntermediate f n m)
      (relativeStratumMap f n m)
      (attachmentSecondMap f n m)
      (pushout.inr (stratumBoundaryToOld Y n m)
        (stratumBoundaryToObjects Y n m)) := by
  have hTop := boundaryToOld_relativeStratum_isPushout f n m
  have hOuter : IsPushout
      (stratumBoundaryToOld Y n m)
      (pushout.inr (stratumBoundaryToObjects X n m)
          (stratumBoundaryMap f n m) ≫ relativeStratumMap f n m)
      (pushout.inl (filteredLatchingMap f n m)
          (pushout.inl (stratumBoundaryToOld X n m)
            (stratumBoundaryToObjects X n m)) ≫ attachmentSecondMap f n m)
      (pushout.inr (stratumBoundaryToOld Y n m)
        (stratumBoundaryToObjects Y n m)) := by
    have h := IsPushout.of_hasPushout
      (stratumBoundaryToOld Y n m) (stratumBoundaryToObjects Y n m)
    apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa using (relativeStratumMap_inr f n m).symm
    · simpa using (attachmentSecondMap_inl f n m).symm
    · simp
  exact hOuter.of_top (relativeStratum_secondMap_comm f n m) hTop

private noncomputable abbrev coproductRelativeLatchingSource
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  ∐ fun _ : latchingIndexDegree n m =>
    CategoryTheory.SimplicialObject.relativeLatchingObject f m

private noncomputable abbrev coproductRelativeLatchingTarget
    {X Y : CategoryTheory.SimplicialObject C} (_f : X ⟶ Y) (n m : ℕ) : C :=
  ∐ fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)

private def stratumToRelativeLatchingInl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (a : latchingIndexDegree n m) :
    X.obj a.obj.obj.left ⟶
      CategoryTheory.SimplicialObject.relativeLatchingObject f m :=
  X.map (eqToHom (newTargetEq a)) ≫
    pushout.inl (CategoryTheory.SimplicialObject.latchingMap X m)
      ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f)

private def stratumToRelativeLatchingInr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (_a : latchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.latchingObject Y m ⟶
      CategoryTheory.SimplicialObject.relativeLatchingObject f m :=
  pushout.inr (CategoryTheory.SimplicialObject.latchingMap X m)
    ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f)

private theorem stratumRelativeLatching_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (a : latchingIndexDegree n m) :
    IsPushout
      (CategoryTheory.SimplicialObject.latchingMap X m ≫
        X.map (eqToHom (newTargetEq a).symm))
      ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f)
      (stratumToRelativeLatchingInl f a)
      (stratumToRelativeLatchingInr f a) := by
  have h := IsPushout.of_hasPushout
    (CategoryTheory.SimplicialObject.latchingMap X m)
    ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f)
  apply h.of_iso' (Iso.refl _)
    (X.mapIso (CategoryTheory.eqToIso (newTargetEq a))) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, CategoryTheory.eqToIso.hom]
    rw [Category.assoc, ← X.map_comp, eqToHom_trans, eqToHom_refl,
      X.map_id, Category.comp_id]
  · simp
  · simp [stratumToRelativeLatchingInl]
  · simp [stratumToRelativeLatchingInr]

private noncomputable def coproductRelativeLatchingInl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumObjects X n m ⟶ coproductRelativeLatchingSource f n m :=
  CategoryTheory.Limits.Sigma.map fun a => stratumToRelativeLatchingInl f a

private noncomputable def coproductRelativeLatchingInr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumBoundaries Y n m ⟶ coproductRelativeLatchingSource f n m :=
  CategoryTheory.Limits.Sigma.map fun a => stratumToRelativeLatchingInr f a

private theorem coproductRelativeLatching_isPushout
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPushout
      (stratumBoundaryToObjects X n m)
      (stratumBoundaryMap f n m)
      (coproductRelativeLatchingInl f n m)
      (coproductRelativeLatchingInr f n m) := by
  let F₀ : Discrete (latchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.latchingObject X m
  let F₁ : Discrete (latchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun a => X.obj a.obj.obj.left
  let F₂ : Discrete (latchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.latchingObject Y m
  let F₃ : Discrete (latchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.relativeLatchingObject f m
  let α : F₀ ⟶ F₁ := Discrete.natTrans fun a =>
    CategoryTheory.SimplicialObject.latchingMap X m ≫
      X.map (eqToHom (newTargetEq a.as).symm)
  let β : F₀ ⟶ F₂ := Discrete.natTrans fun _ =>
    (CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f
  let γ : F₁ ⟶ F₃ := Discrete.natTrans fun a =>
    stratumToRelativeLatchingInl f a.as
  let δ : F₂ ⟶ F₃ := Discrete.natTrans fun a =>
    stratumToRelativeLatchingInr f a.as
  have hPointwise : IsPushout α β γ δ :=
    IsPushout.of_forall_isPushout_app fun a =>
      stratumRelativeLatching_isPushout f a.as
  have hMapped := hPointwise.map
    (colim : (Discrete (latchingIndexDegree n m) ⥤ C) ⥤ C)
  simpa [F₀, F₁, F₂, F₃, α, β, γ, δ, CategoryTheory.Limits.Sigma.map,
    stratumBoundaryToObjects,
    stratumBoundaryMap, coproductRelativeLatchingInl,
    coproductRelativeLatchingInr] using hMapped

/-- The canonical source `R` is the coproduct of the degree-`m` relative
latching sources, after transporting each stratum target to `[m]`. -/
private noncomputable def relativeStratumSourceIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumSource f n m ≅ coproductRelativeLatchingSource f n m :=
  (IsPushout.of_hasPushout
    (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m)).isoIsPushout
      _ _ (coproductRelativeLatching_isPushout f n m)

@[reassoc]
private theorem relativeStratumSourceIso_hom_inl
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inl (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        (relativeStratumSourceIso f n m).hom =
      coproductRelativeLatchingInl f n m := by
  apply IsPushout.inl_isoIsPushout_hom

@[reassoc]
private theorem relativeStratumSourceIso_hom_inr
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pushout.inr (stratumBoundaryToObjects X n m) (stratumBoundaryMap f n m) ≫
        (relativeStratumSourceIso f n m).hom =
      coproductRelativeLatchingInr f n m := by
  apply IsPushout.inr_isoIsPushout_hom

private noncomputable def stratumObjectsToStandardIso
    (Z : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumObjects Z n m ≅
      (∐ fun _ : latchingIndexDegree n m => Z.obj (op ⦋m⦌)) :=
  (colim : (Discrete (latchingIndexDegree n m) ⥤ C) ⥤ C).mapIso
    (Discrete.natIso fun a => Z.mapIso (CategoryTheory.eqToIso (newTargetEq a.as)))

@[reassoc]
private theorem stratumObjectsToStandardIso_ι_hom
    (Z : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun a : latchingIndexDegree n m => Z.obj a.obj.obj.left) a ≫
        (stratumObjectsToStandardIso Z n m).hom =
      Z.map (eqToHom (newTargetEq a)) ≫
        Sigma.ι (fun _ : latchingIndexDegree n m => Z.obj (op ⦋m⦌)) a := by
  apply ι_colimMap

private noncomputable def coproductRelativeLatchingMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    coproductRelativeLatchingSource f n m ⟶
      coproductRelativeLatchingTarget f n m :=
  CategoryTheory.Limits.Sigma.map fun _ =>
    CategoryTheory.SimplicialObject.relativeLatchingMap f m

@[reassoc]
private theorem coproductRelativeLatchingInl_ι
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
        coproductRelativeLatchingInl f n m =
      stratumToRelativeLatchingInl f a ≫
        Sigma.ι (fun _ : latchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeLatchingObject f m) a := by
  unfold coproductRelativeLatchingInl
  rw [Sigma.ι_map]

@[reassoc]
private theorem coproductRelativeLatchingInr_ι
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun _ : latchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.latchingObject Y m) a ≫
        coproductRelativeLatchingInr f n m =
      stratumToRelativeLatchingInr f a ≫
        Sigma.ι (fun _ : latchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeLatchingObject f m) a := by
  unfold coproductRelativeLatchingInr
  rw [Sigma.ι_map]

@[reassoc]
private theorem coproductRelativeLatchingMap_ι
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : latchingIndexDegree n m) :
    Sigma.ι (fun _ : latchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeLatchingObject f m) a ≫
        coproductRelativeLatchingMap f n m =
      CategoryTheory.SimplicialObject.relativeLatchingMap f m ≫
        Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
  unfold coproductRelativeLatchingMap
  rw [Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeStratumMap_arrow_comm
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumMap f n m ≫ (stratumObjectsToStandardIso Y n m).hom =
      (relativeStratumSourceIso f n m).hom ≫
        coproductRelativeLatchingMap f n m := by
  apply pushout.hom_ext
  · rw [relativeStratumMap_inl_assoc, relativeStratumSourceIso_hom_inl_assoc]
    apply Sigma.hom_ext
    intro a
    calc
      Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
            (stratumObjectsMap f n m ≫
              (stratumObjectsToStandardIso Y n m).hom) =
          f.app a.obj.obj.left ≫
            (Sigma.ι (fun a : latchingIndexDegree n m => Y.obj a.obj.obj.left) a ≫
              (stratumObjectsToStandardIso Y n m).hom) := by
                unfold stratumObjectsMap
                rw [← Category.assoc, Sigma.ι_map]
                simp only [Category.assoc]
      _ = f.app a.obj.obj.left ≫ Y.map (eqToHom (newTargetEq a)) ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            rw [stratumObjectsToStandardIso_ι_hom]
      _ = X.map (eqToHom (newTargetEq a)) ≫ f.app (op ⦋m⦌) ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            simpa only [Category.assoc] using congrArg
              (fun t => t ≫
                Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a)
              (f.naturality (eqToHom (newTargetEq a))).symm
      _ = (X.map (eqToHom (newTargetEq a)) ≫
              pushout.inl (CategoryTheory.SimplicialObject.latchingMap X m)
                ((CategoryTheory.SimplicialObject.latchingObjectFunctor m).map f)) ≫
            CategoryTheory.SimplicialObject.relativeLatchingMap f m ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            simpa only [Category.assoc] using congrArg
              (fun t => X.map (eqToHom (newTargetEq a)) ≫ t)
              (CategoryTheory.SimplicialObject.relativeLatchingMap_inl_assoc f m
                (Sigma.ι (fun _ : latchingIndexDegree n m =>
                  Y.obj (op ⦋m⦌)) a)).symm
      _ = stratumToRelativeLatchingInl f a ≫
          (CategoryTheory.SimplicialObject.relativeLatchingMap f m ≫
            Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a) := by
              rfl
      _ = stratumToRelativeLatchingInl f a ≫
          (Sigma.ι (fun _ : latchingIndexDegree n m =>
                CategoryTheory.SimplicialObject.relativeLatchingObject f m) a ≫
            coproductRelativeLatchingMap f n m) := by
              rw [coproductRelativeLatchingMap_ι]
      _ = (Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
              coproductRelativeLatchingInl f n m) ≫
            coproductRelativeLatchingMap f n m := by
              simpa only [Category.assoc] using
                (coproductRelativeLatchingInl_ι_assoc f n m a
                  (coproductRelativeLatchingMap f n m)).symm
      _ = Sigma.ι (fun a : latchingIndexDegree n m => X.obj a.obj.obj.left) a ≫
          (coproductRelativeLatchingInl f n m ≫
            coproductRelativeLatchingMap f n m) := by
              simp only [Category.assoc]
  · rw [relativeStratumMap_inr_assoc, relativeStratumSourceIso_hom_inr_assoc]
    apply Sigma.hom_ext
    intro a
    calc
      Sigma.ι (fun _ : latchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.latchingObject Y m) a ≫
          (stratumBoundaryToObjects Y n m ≫
            (stratumObjectsToStandardIso Y n m).hom) =
        (CategoryTheory.SimplicialObject.latchingMap Y m ≫
            Y.map (eqToHom (newTargetEq a).symm)) ≫
          (Sigma.ι (fun a : latchingIndexDegree n m => Y.obj a.obj.obj.left) a ≫
            (stratumObjectsToStandardIso Y n m).hom) := by
              unfold stratumBoundaryToObjects
              rw [← Category.assoc, Sigma.ι_map]
              simp only [Category.assoc]
      _ = CategoryTheory.SimplicialObject.latchingMap Y m ≫
          Y.map (eqToHom (newTargetEq a).symm) ≫
          Y.map (eqToHom (newTargetEq a)) ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            rw [stratumObjectsToStandardIso_ι_hom]
            simp only [Category.assoc]
      _ = CategoryTheory.SimplicialObject.latchingMap Y m ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            have hm : Y.map (eqToHom (newTargetEq a).symm) ≫
                Y.map (eqToHom (newTargetEq a)) = 𝟙 _ := by
              rw [← Y.map_comp, eqToHom_trans, eqToHom_refl, Y.map_id]
            simpa only [Category.assoc, Category.id_comp, Category.comp_id] using congrArg
              (fun t => CategoryTheory.SimplicialObject.latchingMap Y m ≫ t ≫
                Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a) hm
      _ = stratumToRelativeLatchingInr f a ≫
          CategoryTheory.SimplicialObject.relativeLatchingMap f m ≫
          Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a := by
            unfold stratumToRelativeLatchingInr
            exact (CategoryTheory.SimplicialObject.relativeLatchingMap_inr_assoc f m
              (Sigma.ι (fun _ : latchingIndexDegree n m => Y.obj (op ⦋m⦌)) a)).symm
      _ = stratumToRelativeLatchingInr f a ≫
          (Sigma.ι (fun _ : latchingIndexDegree n m =>
                CategoryTheory.SimplicialObject.relativeLatchingObject f m) a ≫
            coproductRelativeLatchingMap f n m) := by
              rw [coproductRelativeLatchingMap_ι]
      _ = (Sigma.ι (fun _ : latchingIndexDegree n m =>
                CategoryTheory.SimplicialObject.latchingObject Y m) a ≫
              coproductRelativeLatchingInr f n m) ≫
            coproductRelativeLatchingMap f n m := by
              simpa only [Category.assoc] using
                (coproductRelativeLatchingInr_ι_assoc f n m a
                  (coproductRelativeLatchingMap f n m)).symm
      _ = Sigma.ι (fun _ : latchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.latchingObject Y m) a ≫
          (coproductRelativeLatchingInr f n m ≫
            coproductRelativeLatchingMap f n m) := by
              simp only [Category.assoc]

/-- Arrow identification of the finite-stratum map with the finite coproduct
of the degree-`m` relative latching map. -/
private noncomputable def relativeStratumMapArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    Arrow.mk (relativeStratumMap f n m) ≅
      Arrow.mk (coproductRelativeLatchingMap f n m) :=
  Arrow.isoMk (relativeStratumSourceIso f n m)
    (stratumObjectsToStandardIso Y n m)
    (relativeStratumMap_arrow_comm f n m).symm

private theorem coproductRelativeLatchingMap_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f m)) :
    HomotopicalAlgebra.trivialCofibrations C
      (coproductRelativeLatchingMap f n m) := by
  unfold coproductRelativeLatchingMap CategoryTheory.Limits.Sigma.map
  apply (HomotopicalAlgebra.trivialCofibrations C).colimMap
  intro a
  exact h

private theorem relativeStratumMap_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f m)) :
    HomotopicalAlgebra.trivialCofibrations C (relativeStratumMap f n m) := by
  exact ((HomotopicalAlgebra.trivialCofibrations C).arrow_mk_iso_iff
    (relativeStratumMapArrowIso f n m)).2
      (coproductRelativeLatchingMap_trivialCofibration f n m h)

private theorem attachmentFirstMap_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialCofibrations C
      (filteredLatchingMap f n m)) :
    HomotopicalAlgebra.trivialCofibrations C (attachmentFirstMap f n m) := by
  exact (HomotopicalAlgebra.trivialCofibrations C).of_isPushout
    (attachmentFirstMap_isPushout f n m).flip h

private theorem attachmentSecondMap_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f m)) :
    HomotopicalAlgebra.trivialCofibrations C (attachmentSecondMap f n m) := by
  exact (HomotopicalAlgebra.trivialCofibrations C).of_isPushout
    (attachmentSecondMap_isPushout f n m)
      (relativeStratumMap_trivialCofibration f n m h)

private theorem latchingAttachmentMap_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (hstage : HomotopicalAlgebra.trivialCofibrations C
      (filteredLatchingMap f n m))
    (hrelative : HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f m)) :
    HomotopicalAlgebra.trivialCofibrations C (latchingAttachmentMap f n m) := by
  rw [← attachmentMap_factorization f n m]
  exact (HomotopicalAlgebra.trivialCofibrations C).comp_mem _ _
    (attachmentFirstMap_trivialCofibration f n m hstage)
    (attachmentSecondMap_trivialCofibration f n m hrelative)

private noncomputable def filteredLatchingMapSuccessorArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    Arrow.mk (latchingAttachmentMap f n m) ≅
      Arrow.mk (filteredLatchingMap f n (m + 1)) :=
  Arrow.isoMk (standardLatchingAttachmentIso X n m)
    (standardLatchingAttachmentIso Y n m)
    (standardLatchingAttachmentIso_naturality f n m)

private theorem filteredLatchingMap_succ_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (hstage : HomotopicalAlgebra.trivialCofibrations C
      (filteredLatchingMap f n m))
    (hrelative : HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f m)) :
    HomotopicalAlgebra.trivialCofibrations C
      (filteredLatchingMap f n (m + 1)) := by
  exact ((HomotopicalAlgebra.trivialCofibrations C).arrow_mk_iso_iff
    (filteredLatchingMapSuccessorArrowIso f n m)).1
      (latchingAttachmentMap_trivialCofibration f n m hstage hrelative)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem filteredTotalObjectIso_ι_hom
    (Z : CategoryTheory.SimplicialObject C) (n : ℕ)
    (a : latchingIndexBelow n n) :
    colimit.ι (filteredLatchingDiagram Z n n) a ≫
        (filteredTotalObjectIso Z n).hom =
      CategoryTheory.SimplicialObject.latchingι Z n a.obj := by
  unfold filteredTotalObjectIso
  rw [HasColimit.ι_isoOfEquivalence_hom]
  change (𝟙 (Z.obj a.obj.obj.left)) ≫
      colimit.ι (CategoryTheory.SimplicialObject.latchingDiagram Z n) a.obj =
    colimit.ι (CategoryTheory.SimplicialObject.latchingDiagram Z n) a.obj
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem filteredTotalObjectIso_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    (filteredTotalObjectIso X n).hom ≫
        (CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f =
      filteredLatchingMap f n n ≫ (filteredTotalObjectIso Y n).hom := by
  apply colimit.hom_ext
  intro a
  calc
    colimit.ι (filteredLatchingDiagram X n n) a ≫
          ((filteredTotalObjectIso X n).hom ≫
            (CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f) =
        CategoryTheory.SimplicialObject.latchingι X n a.obj ≫
          (CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f := by
            rw [← Category.assoc, filteredTotalObjectIso_ι_hom]
    _ = f.app a.obj.obj.left ≫
        CategoryTheory.SimplicialObject.latchingι Y n a.obj := by
          rw [CategoryTheory.SimplicialObject.latchingObjectFunctor_map_ι]
    _ = f.app a.obj.obj.left ≫
        (colimit.ι (filteredLatchingDiagram Y n n) a ≫
          (filteredTotalObjectIso Y n).hom) := by
            rw [filteredTotalObjectIso_ι_hom]
    _ = (colimit.ι (filteredLatchingDiagram X n n) a ≫
          filteredLatchingMap f n n) ≫ (filteredTotalObjectIso Y n).hom := by
            rw [filteredLatchingMap_ι, Category.assoc]
    _ = colimit.ι (filteredLatchingDiagram X n n) a ≫
        (filteredLatchingMap f n n ≫ (filteredTotalObjectIso Y n).hom) := by
          simp only [Category.assoc]

private noncomputable def filteredTotalMapArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (filteredLatchingMap f n n) ≅
      Arrow.mk ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f) :=
  Arrow.isoMk (filteredTotalObjectIso X n) (filteredTotalObjectIso Y n)
    (filteredTotalObjectIso_naturality f n)

private def filteredZeroCocone (X : CategoryTheory.SimplicialObject C)
    (n : ℕ) (Z : C) : Cocone (filteredLatchingDiagram X n 0) where
  pt := Z
  ι :=
    { app := fun a => isEmptyElim a
      naturality := by
        intro a
        exact isEmptyElim a }

private noncomputable def filteredZeroIsInitial
    (X : CategoryTheory.SimplicialObject C) (n : ℕ) :
    IsInitial (filteredLatchingObject X n 0) :=
  IsInitial.ofUniqueHom
    (fun Z => colimit.desc (filteredLatchingDiagram X n 0) (filteredZeroCocone X n Z))
    (fun _ _ => by
      apply colimit.hom_ext
      intro a
      exact isEmptyElim a)

private noncomputable def filteredZeroObjectIso
    (X Y : CategoryTheory.SimplicialObject C) (n : ℕ) :
    filteredLatchingObject X n 0 ≅ filteredLatchingObject Y n 0 :=
  (filteredZeroIsInitial X n).uniqueUpToIso (filteredZeroIsInitial Y n)

private theorem filteredLatchingMap_zero_eq_iso_hom
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    filteredLatchingMap f n 0 = (filteredZeroObjectIso X Y n).hom :=
  (filteredZeroIsInitial X n).hom_ext _ _

private instance filteredLatchingMap_zero_isIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    IsIso (filteredLatchingMap f n 0) := by
  rw [filteredLatchingMap_zero_eq_iso_hom]
  infer_instance

private theorem filteredLatchingMap_zero_trivialCofibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    HomotopicalAlgebra.trivialCofibrations C (filteredLatchingMap f n 0) := by
  exact (HomotopicalAlgebra.trivialCofibrations C).of_isIso _

private theorem filteredLatchingMap_trivialCofibration_of_lower
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (n m : ℕ) (hm : m ≤ n)
    (hlower : ∀ k < m, HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f k)) :
    HomotopicalAlgebra.trivialCofibrations C (filteredLatchingMap f n m) := by
  induction m with
  | zero => exact filteredLatchingMap_zero_trivialCofibration f n
  | succ m ih =>
      apply filteredLatchingMap_succ_trivialCofibration f n m
      · exact ih (Nat.le_trans (Nat.le_succ m) hm)
          (fun k hk => hlower k (Nat.lt_trans hk (Nat.lt_succ_self m)))
      · exact hlower m (Nat.lt_succ_self m)

/-- If all lower relative latching maps are trivial cofibrations, then the
degree-`n` latching-object comparison is a trivial cofibration. -/
private theorem latchingObjectMap_trivialCofibration_of_lower
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
    (hlower : ∀ k < n, HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f k)) :
    HomotopicalAlgebra.trivialCofibrations C
      ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f) := by
  exact ((HomotopicalAlgebra.trivialCofibrations C).arrow_mk_iso_iff
    (filteredTotalMapArrowIso f n)).1
      (filteredLatchingMap_trivialCofibration_of_lower f n n (Nat.le_refl n) hlower)

/-- Every component of a Reedy left map in the base trivial-cofibration class is trivial. -/
theorem component_trivialCofibration_of_reedyLeft_trivial
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (h : CategoryTheory.SimplicialObject.reedyLeft
      (HomotopicalAlgebra.trivialCofibrations C) f) (n : ℕ) :
    HomotopicalAlgebra.trivialCofibrations C (f.app (op ⦋n⦌)) := by
  have hL := latchingObjectMap_trivialCofibration_of_lower f n
    (fun k _ => h k)
  have hinl : HomotopicalAlgebra.trivialCofibrations C
      (pushout.inl (CategoryTheory.SimplicialObject.latchingMap X n)
        ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f)) :=
    (HomotopicalAlgebra.trivialCofibrations C).of_isPushout
      (IsPushout.of_hasPushout
        (CategoryTheory.SimplicialObject.latchingMap X n)
        ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f)) hL
  have hcomp := (HomotopicalAlgebra.trivialCofibrations C).comp_mem _ _ hinl (h n)
  rw [CategoryTheory.SimplicialObject.relativeLatchingMap_inl] at hcomp
  exact hcomp

private theorem pointwiseWeakEquivalence_of_reedyLeft_trivial
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (h : CategoryTheory.SimplicialObject.reedyLeft
      (HomotopicalAlgebra.trivialCofibrations C) f) :
    (HomotopicalAlgebra.weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ f := by
  intro Δ
  let n := Δ.unop.len
  have hn : HomotopicalAlgebra.weakEquivalences C (f.app (op ⦋n⦌)) :=
    HomotopicalAlgebra.trivialCofibrations_sub_weakEquivalences C _
      (component_trivialCofibration_of_reedyLeft_trivial f h n)
  have hΔ : op ⦋n⦌ = Δ := congrArg op (SimplexCategory.mk_len Δ.unop)
  cases hΔ
  exact hn

private theorem relativeLatchingMap_trivialCofibration_of_reedyLeft_cof_pointwiseWeak
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (hcof : CategoryTheory.SimplicialObject.reedyLeft
      (HomotopicalAlgebra.cofibrations C) f)
    (hweak : (HomotopicalAlgebra.weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ f) :
    ∀ n : ℕ, HomotopicalAlgebra.trivialCofibrations C
      (CategoryTheory.SimplicialObject.relativeLatchingMap f n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      have hL := latchingObjectMap_trivialCofibration_of_lower f n
        (fun k hk => ih k hk)
      have hinl : HomotopicalAlgebra.trivialCofibrations C
          (pushout.inl (CategoryTheory.SimplicialObject.latchingMap X n)
            ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f)) :=
        (HomotopicalAlgebra.trivialCofibrations C).of_isPushout
          (IsPushout.of_hasPushout
            (CategoryTheory.SimplicialObject.latchingMap X n)
            ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f)) hL
      have hinlWeak : HomotopicalAlgebra.weakEquivalences C
          (pushout.inl (CategoryTheory.SimplicialObject.latchingMap X n)
            ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f)) :=
        HomotopicalAlgebra.trivialCofibrations_sub_weakEquivalences C _ hinl
      have hcompWeak : HomotopicalAlgebra.weakEquivalences C
          (pushout.inl (CategoryTheory.SimplicialObject.latchingMap X n)
              ((CategoryTheory.SimplicialObject.latchingObjectFunctor n).map f) ≫
            CategoryTheory.SimplicialObject.relativeLatchingMap f n) := by
        rw [CategoryTheory.SimplicialObject.relativeLatchingMap_inl]
        exact hweak (op ⦋n⦌)
      have hrelativeWeak : HomotopicalAlgebra.weakEquivalences C
          (CategoryTheory.SimplicialObject.relativeLatchingMap f n) :=
        (HomotopicalAlgebra.weakEquivalences C).of_precomp _ _ hinlWeak hcompWeak
      exact ⟨hcof n, hrelativeWeak⟩

/-- In a model category, Reedy trivial cofibrations are exactly Reedy
cofibrations that are pointwise weak equivalences. -/
private theorem reedyLeft_trivialCofibrations_eq_internal :
    CategoryTheory.SimplicialObject.reedyLeft
        (HomotopicalAlgebra.trivialCofibrations C) =
      CategoryTheory.SimplicialObject.reedyLeft
          (HomotopicalAlgebra.cofibrations C) ⊓
        (HomotopicalAlgebra.weakEquivalences C).functorCategory
          SimplexCategoryᵒᵖ := by
  apply le_antisymm
  · intro X Y f h
    exact ⟨fun n =>
      HomotopicalAlgebra.trivialCofibrations_sub_cofibrations C _ (h n),
      pointwiseWeakEquivalence_of_reedyLeft_trivial f h⟩
  · intro X Y f h
    exact relativeLatchingMap_trivialCofibration_of_reedyLeft_cof_pointwiseWeak
      f h.1 h.2



end FilteredColimits

end ReedyTrivialClassesLatching

namespace ReedyTrivialClassesMatching

/-- Objects of `matchingIndex n` whose source simplex has degree `< m`. -/
private abbrev matchingIndexBelow (n m : ℕ) :=
  ObjectProperty.FullSubcategory
    (fun a : CategoryTheory.SimplicialObject.matchingIndex n =>
      a.obj.right.unop.len < m)

/-- Forget the filtration bound. -/
private def belowToMatching (n m : ℕ) :
    matchingIndexBelow n m ⥤ CategoryTheory.SimplicialObject.matchingIndex n where
  obj a := a.obj
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Increase the filtration bound. -/
private def belowIncl {n m m' : ℕ} (h : m ≤ m') :
    matchingIndexBelow n m ⥤ matchingIndexBelow n m' where
  obj a := ⟨a.obj, a.property.trans_le h⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def belowToMatchingFullyFaithful (n m : ℕ) :
    (belowToMatching n m).FullyFaithful where
  preimage f := ObjectProperty.homMk f

private instance belowToMatching_full (n m : ℕ) : (belowToMatching n m).Full :=
  (belowToMatchingFullyFaithful n m).full

private instance belowToMatching_faithful (n m : ℕ) : (belowToMatching n m).Faithful :=
  (belowToMatchingFullyFaithful n m).faithful

private def belowInclFullyFaithful {n m m' : ℕ} (h : m ≤ m') :
    (belowIncl (n := n) h).FullyFaithful where
  preimage f := ObjectProperty.homMk f.hom

private instance belowIncl_full {n m m' : ℕ} (h : m ≤ m') : (belowIncl (n := n) h).Full :=
  (belowInclFullyFaithful h).full

private instance belowIncl_faithful {n m m' : ℕ} (h : m ≤ m') :
    (belowIncl (n := n) h).Faithful :=
  (belowInclFullyFaithful h).faithful

@[simp]
private theorem belowToMatching_obj (n m : ℕ) (a : matchingIndexBelow n m) :
    (belowToMatching n m).obj a = a.obj :=
  rfl

@[simp]
private theorem belowToMatching_map (n m : ℕ) {a b : matchingIndexBelow n m} (f : a ⟶ b) :
    (belowToMatching n m).map f = f.hom :=
  rfl

@[simp]
private theorem belowIncl_obj_obj {n m m' : ℕ} (h : m ≤ m') (a : matchingIndexBelow n m) :
    ((belowIncl h).obj a).obj = a.obj :=
  rfl

@[simp]
private theorem belowIncl_map_hom {n m m' : ℕ} (h : m ≤ m')
    {a b : matchingIndexBelow n m} (f : a ⟶ b) :
    ((belowIncl h).map f).hom = f.hom :=
  rfl

private theorem belowIncl_refl (n m : ℕ) :
    belowIncl (n := n) (Nat.le_refl m) = 𝟭 (matchingIndexBelow n m) :=
  rfl

private theorem belowIncl_trans {n m m' m'' : ℕ} (h : m ≤ m') (h' : m' ≤ m'') :
    belowIncl (n := n) h ⋙ belowIncl (n := n) h' =
      belowIncl (n := n) (h.trans h') :=
  rfl

private instance matchingIndexBelow_zero_isEmpty (n : ℕ) : IsEmpty (matchingIndexBelow n 0) where
  false a := (Nat.not_lt_zero _ a.property).elim

private noncomputable instance matchingIndexBelow_finite (n m : ℕ) :
    Finite (matchingIndexBelow n m) :=
  Finite.of_injective (fun a => a.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

/-- The exact degree-`m` stratum in the matching index. -/
private abbrev matchingIndexDegree (n m : ℕ) :=
  ObjectProperty.FullSubcategory
    (fun a : CategoryTheory.SimplicialObject.matchingIndex n =>
      a.obj.right.unop.len = m)

private noncomputable instance matchingIndexDegree_finite (n m : ℕ) :
    Finite (matchingIndexDegree n m) :=
  Finite.of_injective (fun a => a.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

private instance matchingIndexDegree_hom_subsingleton (n m : ℕ)
    (a b : matchingIndexDegree n m) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    let _ : Mono a.obj.obj.hom.unop := a.obj.property.1
    let _ : Epi a.obj.obj.hom := by
      simpa using (inferInstance : Epi a.obj.obj.hom.unop.op)
    apply (cancel_epi a.obj.obj.hom).1
    exact (StructuredArrow.w f.hom.hom).trans
      (StructuredArrow.w g.hom.hom).symm

/-- A morphism in one exact-degree stratum forces equality of its endpoints. -/
private theorem eq_of_hom_in_degree {n m : ℕ} {a b : matchingIndexDegree n m} (f : a ⟶ b) :
    a = b := by
  have hfac : f.hom.hom.right.unop ≫ a.obj.obj.hom.unop = b.obj.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simpa using StructuredArrow.w f.hom.hom
  let _ : Mono (f.hom.hom.right.unop ≫ a.obj.obj.hom.unop) := by
    rw [hfac]
    exact b.obj.property.1
  let _ : Mono f.hom.hom.right.unop :=
    CategoryTheory.mono_of_mono f.hom.hom.right.unop a.obj.obj.hom.unop
  have hrightUnop : a.obj.obj.right.unop = b.obj.obj.right.unop := by
    apply SimplexCategory.ext
    exact a.property.trans b.property.symm
  let hright : a.obj.obj.right = b.obj.obj.right := congrArg op hrightUnop
  let e := (f.hom.hom.right ≫ eqToHom hright.symm).unop
  let _ : Mono e := by
    dsimp [e]
    infer_instance
  have heUnop : e = 𝟙 _ := SimplexCategory.eq_id_of_mono e
  have he : f.hom.hom.right ≫ eqToHom hright.symm = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    simpa [e] using heUnop
  have hfright : f.hom.hom.right = eqToHom hright := by
    apply (cancel_mono (eqToHom hright.symm)).1
    rw [he]
    simp
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply StructuredArrow.obj_ext _ _ hright
  simpa [hfright] using StructuredArrow.w f.hom.hom

/-- The degree-`m` stratum is equivalent to a discrete category on its objects. -/
private noncomputable def matchingIndexDegreeEquivDiscrete (n m : ℕ) :
    matchingIndexDegree n m ≌ Discrete (matchingIndexDegree n m) := by
  let F : matchingIndexDegree n m ⥤ Discrete (matchingIndexDegree n m) :=
    { obj := Discrete.mk
      map := fun f => eqToHom (congrArg Discrete.mk (eq_of_hom_in_degree f))
      map_id := by intro; subsingleton
      map_comp := by intros; subsingleton }
  let G : Discrete (matchingIndexDegree n m) ⥤ matchingIndexDegree n m :=
    Discrete.functor fun a => a
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
      counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

private instance matchingIndex_hom_subsingleton (n : ℕ)
    (a b : CategoryTheory.SimplicialObject.matchingIndex n) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    let _ : Mono a.obj.hom.unop := a.property.1
    let _ : Epi a.obj.hom := by
      simpa using (inferInstance : Epi a.obj.hom.unop.op)
    apply (cancel_epi a.obj.hom).1
    exact (StructuredArrow.w f.hom).trans (StructuredArrow.w g.hom).symm

private instance matchingIndexBelow_hom_subsingleton (n m : ℕ)
    (a b : matchingIndexBelow n m) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

/-- The outgoing comma category from a new degree-`m` mono to earlier strata. -/
private abbrev matchingSuccessor (n m : ℕ) (a : matchingIndexDegree n m) :=
  StructuredArrow a.obj (belowToMatching n m)

private instance matchingSuccessor_hom_subsingleton (n m : ℕ)
    (a : matchingIndexDegree n m) (x y : matchingSuccessor n m a) :
    Subsingleton (x ⟶ y) where
  allEq f g := by
    apply StructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

private theorem newSourceEq {n m : ℕ} (a : matchingIndexDegree n m) :
    a.obj.obj.right = op ⦋m⦌ := by
  apply unop_injective
  apply SimplexCategory.ext
  simpa using a.property

private def successorCanonicalHom {n m : ℕ} {a : matchingIndexDegree n m}
    (x : matchingSuccessor n m a) :
    op ⦋m⦌ ⟶ x.right.obj.obj.right :=
  eqToHom (newSourceEq a).symm ≫ x.hom.hom.right

private instance successorCanonicalHom_mono {n m : ℕ}
    {a : matchingIndexDegree n m} (x : matchingSuccessor n m a) :
    Mono (successorCanonicalHom x).unop := by
  have hfac : x.hom.hom.right.unop ≫ a.obj.obj.hom.unop =
      x.right.obj.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simpa using StructuredArrow.w x.hom.hom
  let _ : Mono (x.hom.hom.right.unop ≫ a.obj.obj.hom.unop) := by
    rw [hfac]
    exact x.right.obj.property.1
  let _ : Mono x.hom.hom.right.unop :=
    CategoryTheory.mono_of_mono x.hom.hom.right.unop a.obj.obj.hom.unop
  let _ : Mono (eqToHom (newSourceEq a).symm).unop := by infer_instance
  change Mono (x.hom.hom.right.unop ≫ (eqToHom (newSourceEq a).symm).unop)
  infer_instance

private def successorToMatchingIndexObj {n m : ℕ}
    {a : matchingIndexDegree n m} (x : matchingSuccessor n m a) :
    CategoryTheory.SimplicialObject.matchingIndex m :=
  ⟨StructuredArrow.mk (successorCanonicalHom x),
    ⟨successorCanonicalHom_mono x, x.right.property⟩⟩

set_option backward.isDefEq.respectTransparency false in
private def successorToMatchingIndex {n m : ℕ}
    (a : matchingIndexDegree n m) :
    matchingSuccessor n m a ⥤ CategoryTheory.SimplicialObject.matchingIndex m where
  obj := successorToMatchingIndexObj
  map {x y} g := ObjectProperty.homMk
    (StructuredArrow.homMk g.right.hom.hom.right (by
      have hw := congrArg (fun z => z.hom.right) (StructuredArrow.w g)
      have hw' : x.hom.hom.right ≫ g.right.hom.hom.right = y.hom.hom.right := by
        change x.hom.hom.right ≫ g.right.hom.hom.right = y.hom.hom.right at hw
        exact hw
      change successorCanonicalHom x ≫ g.right.hom.hom.right =
        successorCanonicalHom y
      dsimp [successorCanonicalHom]
      simpa only [Category.assoc] using congrArg
        (fun t => eqToHom (newSourceEq a).symm ≫ t) hw'))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
private theorem successorToMatchingIndex_obj_right {n m : ℕ}
    {a : matchingIndexDegree n m} (x : matchingSuccessor n m a) :
    ((successorToMatchingIndex a).obj x).obj.right = x.right.obj.obj.right :=
  rfl

@[simp]
private theorem successorToMatchingIndex_obj_hom {n m : ℕ}
    {a : matchingIndexDegree n m} (x : matchingSuccessor n m a) :
    ((successorToMatchingIndex a).obj x).obj.hom = successorCanonicalHom x :=
  rfl

@[simp]
private theorem successorToMatchingIndex_map_right {n m : ℕ}
    {a : matchingIndexDegree n m} {x y : matchingSuccessor n m a} (g : x ⟶ y) :
    ((successorToMatchingIndex a).map g).hom.right = g.right.hom.hom.right :=
  rfl

private def liftedHom {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    op ⦋n⦌ ⟶ b.obj.right :=
  a.obj.obj.hom ≫ eqToHom (newSourceEq a) ≫ b.obj.hom

private instance liftedHom_mono {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    Mono (liftedHom a b).unop := by
  let _ : Mono b.obj.hom.unop := b.property.1
  let _ : Mono a.obj.obj.hom.unop := a.obj.property.1
  let _ : Mono (eqToHom (newSourceEq a)).unop := by infer_instance
  dsimp [liftedHom]
  infer_instance

private def liftedBelowObj {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) : matchingIndexBelow n m :=
  by
    refine ⟨⟨StructuredArrow.mk (liftedHom a b), ⟨liftedHom_mono a b, ?_⟩⟩,
      b.property.2⟩
    exact b.property.2.trans (by simpa [a.property] using a.obj.property.2)

private def liftedFromNew {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    a.obj ⟶ (belowToMatching n m).obj (liftedBelowObj a b) :=
  ObjectProperty.homMk
    (StructuredArrow.homMk (eqToHom (newSourceEq a) ≫ b.obj.hom) (by rfl))

private def matchingIndexToSuccessorObj {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) : matchingSuccessor n m a :=
  StructuredArrow.mk (liftedFromNew a b)

private def liftedMap {n m : ℕ} (a : matchingIndexDegree n m)
    {b c : CategoryTheory.SimplicialObject.matchingIndex m} (g : b ⟶ c) :
    liftedBelowObj a b ⟶ liftedBelowObj a c :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (StructuredArrow.homMk g.hom.right (by
      have hw := StructuredArrow.w g.hom
      change b.obj.hom ≫ g.hom.right = c.obj.hom at hw
      change liftedHom a b ≫ g.hom.right = liftedHom a c
      dsimp [liftedHom]
      simpa only [Category.assoc] using congrArg
        (fun t => a.obj.obj.hom ≫ eqToHom (newSourceEq a) ≫ t) hw)))

private def matchingIndexToSuccessor {n m : ℕ} (a : matchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.matchingIndex m ⥤ matchingSuccessor n m a where
  obj := matchingIndexToSuccessorObj a
  map g := StructuredArrow.homMk (liftedMap a g) (by subsingleton)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
private theorem matchingIndexToSuccessor_obj_right_obj_right {n m : ℕ}
    (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    ((matchingIndexToSuccessor a).obj b).right.obj.obj.right = b.obj.right :=
  rfl

@[simp]
private theorem matchingIndexToSuccessor_obj_right_obj_hom {n m : ℕ}
    (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    ((matchingIndexToSuccessor a).obj b).right.obj.obj.hom = liftedHom a b :=
  rfl

@[simp]
private theorem matchingIndexToSuccessor_obj_hom_right {n m : ℕ}
    (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    ((matchingIndexToSuccessor a).obj b).hom.hom.right =
      eqToHom (newSourceEq a) ≫ b.obj.hom :=
  rfl

@[simp]
private theorem matchingIndexToSuccessor_map_right_right {n m : ℕ}
    (a : matchingIndexDegree n m)
    {b c : CategoryTheory.SimplicialObject.matchingIndex m} (g : b ⟶ c) :
    ((matchingIndexToSuccessor a).map g).right.hom.hom.right = g.hom.right :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem successorCanonicalHom_lifted {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    successorCanonicalHom ((matchingIndexToSuccessor a).obj b) = b.obj.hom := by
  dsimp [successorCanonicalHom, matchingIndexToSuccessor,
    matchingIndexToSuccessorObj, liftedFromNew]
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem liftedHom_successor {n m : ℕ} (a : matchingIndexDegree n m)
    (x : matchingSuccessor n m a) :
    liftedHom a ((successorToMatchingIndex a).obj x) = x.right.obj.obj.hom := by
  have hc : eqToHom (newSourceEq a) ≫ eqToHom (newSourceEq a).symm = 𝟙 _ := by
    simp
  calc
    liftedHom a ((successorToMatchingIndex a).obj x) =
        a.obj.obj.hom ≫
          (eqToHom (newSourceEq a) ≫ eqToHom (newSourceEq a).symm) ≫
            x.hom.hom.right := by
              simp only [liftedHom, successorToMatchingIndex,
                successorToMatchingIndexObj, successorCanonicalHom,
                StructuredArrow.mk_hom_eq_self, Category.assoc]
    _ = a.obj.obj.hom ≫ x.hom.hom.right := by rw [hc]; simp
    _ = x.right.obj.obj.hom := StructuredArrow.w x.hom.hom

set_option backward.isDefEq.respectTransparency false in
private theorem successor_counit_obj_eq {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    (successorToMatchingIndex a).obj ((matchingIndexToSuccessor a).obj b) = b := by
  apply ObjectProperty.FullSubcategory.ext
  let hright :
      ((successorToMatchingIndex a).obj ((matchingIndexToSuccessor a).obj b)).obj.right =
        b.obj.right := rfl
  apply StructuredArrow.obj_ext _ _ hright
  simpa using successorCanonicalHom_lifted a b

set_option backward.isDefEq.respectTransparency false in
private theorem successor_unit_right_eq {n m : ℕ} (a : matchingIndexDegree n m)
    (x : matchingSuccessor n m a) :
    ((matchingIndexToSuccessor a).obj ((successorToMatchingIndex a).obj x)).right =
      x.right := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  let hright :
      (StructuredArrow.right
        ((matchingIndexToSuccessor a).obj ((successorToMatchingIndex a).obj x))).obj.obj.right =
          x.right.obj.obj.right := rfl
  apply StructuredArrow.obj_ext _ _ hright
  simpa using liftedHom_successor a x

private theorem successor_unit_obj_eq {n m : ℕ} (a : matchingIndexDegree n m)
    (x : matchingSuccessor n m a) :
    (matchingIndexToSuccessor a).obj ((successorToMatchingIndex a).obj x) = x := by
  apply StructuredArrow.obj_ext _ _ (successor_unit_right_eq a x)
  exact Subsingleton.elim _ _

/-- Direct composition/extraction identifies the outgoing successor category with
`matchingIndex m`. -/
private noncomputable def successorEquivalence {n m : ℕ} (a : matchingIndexDegree n m) :
    matchingSuccessor n m a ≌ CategoryTheory.SimplicialObject.matchingIndex m where
  functor := successorToMatchingIndex a
  inverse := matchingIndexToSuccessor a
  unitIso := NatIso.ofComponents
    (fun x => CategoryTheory.eqToIso (successor_unit_obj_eq a x).symm)
  counitIso := NatIso.ofComponents
    (fun b => CategoryTheory.eqToIso (successor_counit_obj_eq a b))

private theorem belowIncl_comp_belowToMatching {n m m' : ℕ} (h : m ≤ m') :
    belowIncl (n := n) h ⋙ belowToMatching n m' = belowToMatching n m :=
  rfl

private theorem sourceEq_comp_successorCanonicalHom {n m : ℕ}
    {a : matchingIndexDegree n m} (x : matchingSuccessor n m a) :
    eqToHom (newSourceEq a) ≫ successorCanonicalHom x = x.hom.hom.right := by
  dsimp [successorCanonicalHom]
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

section DiagramEquations

universe v u

variable {C : Type u} [Category.{v} C] (X : CategoryTheory.SimplicialObject C)

private theorem successor_diagram_obj {n m : ℕ} {a : matchingIndexDegree n m}
    (x : matchingSuccessor n m a) :
    (CategoryTheory.SimplicialObject.matchingDiagram X n).obj x.right.obj =
      (CategoryTheory.SimplicialObject.matchingDiagram X m).obj
        ((successorToMatchingIndex a).obj x) :=
  rfl

private theorem successor_diagram_map {n m : ℕ} {a : matchingIndexDegree n m}
    {x y : matchingSuccessor n m a} (g : x ⟶ y) :
    (CategoryTheory.SimplicialObject.matchingDiagram X n).map g.right.hom =
      (CategoryTheory.SimplicialObject.matchingDiagram X m).map
        ((successorToMatchingIndex a).map g) :=
  rfl

private theorem successor_structure_map {n m : ℕ} {a : matchingIndexDegree n m}
    (x : matchingSuccessor n m a) :
    X.map (eqToHom (newSourceEq a)) ≫ X.map (successorCanonicalHom x) =
      X.map x.hom.hom.right := by
  rw [← X.map_comp, sourceEq_comp_successorCanonicalHom]
  rfl

end DiagramEquations

section FilteredLimits

universe v u

open CategoryTheory.Limits
open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private instance matchingIndex_isThin (n : ℕ) :
    Quiver.IsThin (CategoryTheory.SimplicialObject.matchingIndex n) :=
  fun _ _ => inferInstance

private instance matchingIndexBelow_isThin (n m : ℕ) :
    Quiver.IsThin (matchingIndexBelow n m) :=
  fun _ _ => inferInstance

private noncomputable instance matchingIndexBelow_fintype (n m : ℕ) :
    Fintype (matchingIndexBelow n m) :=
  Fintype.ofFinite _

/-- The degree-`<m` part of the degree-`n` matching diagram. -/
private abbrev filteredMatchingDiagram (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    matchingIndexBelow n m ⥤ C :=
  belowToMatching n m ⋙ CategoryTheory.SimplicialObject.matchingDiagram X n

private def filteredMatchingDiagramMap {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) :
    filteredMatchingDiagram X n m ⟶ filteredMatchingDiagram Y n m :=
  Functor.whiskerLeft (belowToMatching n m)
    ((CategoryTheory.SimplicialObject.matchingDiagramFunctor n).map f)

private noncomputable abbrev filteredMatchingObject
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  limit (filteredMatchingDiagram X n m)

private noncomputable def filteredMatchingMap {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) :
    filteredMatchingObject X n m ⟶ filteredMatchingObject Y n m :=
  limMap (filteredMatchingDiagramMap f n m)

/-- Restriction from a later matching filtration stage to an earlier one. -/
private noncomputable def filteredMatchingRestrict
    (X : CategoryTheory.SimplicialObject C) {n m m' : ℕ} (h : m ≤ m') :
    filteredMatchingObject X n m' ⟶ filteredMatchingObject X n m :=
  limit.pre (filteredMatchingDiagram X n m') (belowIncl (n := n) h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem filteredMatchingRestrict_π
    (X : CategoryTheory.SimplicialObject C) {n m m' : ℕ} (h : m ≤ m')
    (a : matchingIndexBelow n m) :
    filteredMatchingRestrict X h ≫ limit.π (filteredMatchingDiagram X n m) a =
      limit.π (filteredMatchingDiagram X n m') ((belowIncl h).obj a) := by
  change limit.pre (filteredMatchingDiagram X n m') (belowIncl h) ≫
      limit.π (belowIncl (n := n) h ⋙ filteredMatchingDiagram X n m') a = _
  apply limit.pre_π

@[reassoc]
private theorem filteredMatchingMap_π {X Y : CategoryTheory.SimplicialObject C}
    (f : X ⟶ Y) (n m : ℕ) (a : matchingIndexBelow n m) :
    filteredMatchingMap f n m ≫ limit.π (filteredMatchingDiagram Y n m) a =
      limit.π (filteredMatchingDiagram X n m) a ≫ f.app a.obj.obj.right := by
  apply limit.map_π

private noncomputable def belowTotalInverse (n : ℕ) :
    CategoryTheory.SimplicialObject.matchingIndex n ⥤ matchingIndexBelow n n where
  obj a := ⟨a, a.property.2⟩
  map f := ObjectProperty.homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def belowTotalEquivalence (n : ℕ) :
    matchingIndexBelow n n ≌ CategoryTheory.SimplicialObject.matchingIndex n where
  functor := belowToMatching n n
  inverse := belowTotalInverse n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

private noncomputable def filteredTotalObjectIso
    (X : CategoryTheory.SimplicialObject C) (n : ℕ) :
    filteredMatchingObject X n n ≅ CategoryTheory.SimplicialObject.matchingObject X n :=
  HasLimit.isoOfEquivalence (belowTotalEquivalence n) (Iso.refl _)

private def successorLiftFunctor {n m : ℕ} (a : matchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.matchingIndex m ⥤ matchingIndexBelow n m :=
  matchingIndexToSuccessor a ⋙
    StructuredArrow.proj a.obj (belowToMatching n m)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def successorDiagramIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.matchingDiagram X m ≅
      successorLiftFunctor a ⋙ filteredMatchingDiagram X n m :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {b c} g => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private noncomputable def successorBoundaryFromOld
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    filteredMatchingObject X n m ⟶
      CategoryTheory.SimplicialObject.matchingObject X m :=
  limit.pre (filteredMatchingDiagram X n m) (successorLiftFunctor a) ≫
    (HasLimit.isoOfNatIso (successorDiagramIso X a)).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem successorBoundaryFromOld_π
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    successorBoundaryFromOld X a ≫
        CategoryTheory.SimplicialObject.matchingπ X m b =
      limit.π (filteredMatchingDiagram X n m) ((successorLiftFunctor a).obj b) := by
  unfold CategoryTheory.SimplicialObject.matchingπ successorBoundaryFromOld
  rw [Category.assoc, HasLimit.isoOfNatIso_inv_π]
  rw [← Category.assoc, limit.pre_π]
  change limit.π (filteredMatchingDiagram X n m) ((successorLiftFunctor a).obj b) ≫
      𝟙 _ = _
  simp

private noncomputable instance matchingIndexDegree_fintype (n m : ℕ) :
    Fintype (matchingIndexDegree n m) :=
  Fintype.ofFinite _

private noncomputable abbrev stratumMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∏ᶜ fun _ : matchingIndexDegree n m => CategoryTheory.SimplicialObject.matchingObject X m

private noncomputable abbrev stratumObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∏ᶜ fun a : matchingIndexDegree n m => X.obj a.obj.obj.right

private noncomputable def oldToStratumMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    filteredMatchingObject X n m ⟶ stratumMatchingObjects X n m :=
  Pi.lift fun a => successorBoundaryFromOld X a

private noncomputable def stratumObjectsToMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumObjects X n m ⟶ stratumMatchingObjects X n m :=
  CategoryTheory.Limits.Pi.map fun a =>
    X.map (eqToHom (newSourceEq a)) ≫
      CategoryTheory.SimplicialObject.matchingMap X m

@[reassoc]
private theorem oldToStratumMatchingObjects_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    oldToStratumMatchingObjects X n m ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a =
      successorBoundaryFromOld X a := by
  unfold oldToStratumMatchingObjects
  rw [Pi.lift_comp_π]

@[reassoc]
private theorem stratumObjectsToMatchingObjects_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    stratumObjectsToMatchingObjects X n m ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a =
      Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
        (X.map (eqToHom (newSourceEq a)) ≫
          CategoryTheory.SimplicialObject.matchingMap X m) := by
  unfold stratumObjectsToMatchingObjects
  rw [Pi.map_π]

private noncomputable abbrev matchingAttachment
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  pullback (oldToStratumMatchingObjects X n m) (stratumObjectsToMatchingObjects X n m)

private noncomputable def stratumMatchingObjectsMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumMatchingObjects X n m ⟶ stratumMatchingObjects Y n m :=
  CategoryTheory.Limits.Pi.map fun _ =>
    (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f

private noncomputable def stratumObjectsMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumObjects X n m ⟶ stratumObjects Y n m :=
  CategoryTheory.Limits.Pi.map fun a => f.app a.obj.obj.right

set_option backward.isDefEq.respectTransparency false in
private theorem oldToStratumMatchingObjects_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    filteredMatchingMap f n m ≫ oldToStratumMatchingObjects Y n m =
      oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m := by
  apply Pi.hom_ext _ _
  intro a
  calc
    (filteredMatchingMap f n m ≫ oldToStratumMatchingObjects Y n m) ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject Y m) a =
        filteredMatchingMap f n m ≫
          (oldToStratumMatchingObjects Y n m ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.matchingObject Y m) a) := by
                simp only [Category.assoc]
    _ = filteredMatchingMap f n m ≫ successorBoundaryFromOld Y a := by
          unfold oldToStratumMatchingObjects
          rw [Pi.lift_comp_π]
    _ = successorBoundaryFromOld X a ≫
        (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f := by
          apply limit.hom_ext
          intro b
          calc
            (filteredMatchingMap f n m ≫ successorBoundaryFromOld Y a) ≫
                  CategoryTheory.SimplicialObject.matchingπ Y m b =
                filteredMatchingMap f n m ≫
                  limit.π (filteredMatchingDiagram Y n m)
                    ((successorLiftFunctor a).obj b) := by
                      rw [Category.assoc, successorBoundaryFromOld_π]
            _ = limit.π (filteredMatchingDiagram X n m)
                  ((successorLiftFunctor a).obj b) ≫
                f.app ((successorLiftFunctor a).obj b).obj.obj.right := by
                    rw [filteredMatchingMap_π]
            _ = limit.π (filteredMatchingDiagram X n m)
                  ((successorLiftFunctor a).obj b) ≫ f.app b.obj.right := by rfl
            _ = successorBoundaryFromOld X a ≫
                (CategoryTheory.SimplicialObject.matchingπ X m b ≫
                  f.app b.obj.right) := by
                    simpa only [Category.assoc] using
                      (successorBoundaryFromOld_π_assoc X a b
                        (f.app b.obj.right)).symm
            _ = successorBoundaryFromOld X a ≫
                ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f ≫
                  CategoryTheory.SimplicialObject.matchingπ Y m b) := by
                    rw [CategoryTheory.SimplicialObject.matchingObjectFunctor_map_π]
            _ = (successorBoundaryFromOld X a ≫
                  (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) ≫
                CategoryTheory.SimplicialObject.matchingπ Y m b := by
                  simp only [Category.assoc]
    _ = (oldToStratumMatchingObjects X n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject X m) a) ≫
        (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f := by
          unfold oldToStratumMatchingObjects
          rw [Pi.lift_comp_π]
    _ = oldToStratumMatchingObjects X n m ≫
        (Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.matchingObject X m) a ≫
          (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) := by
            simp only [Category.assoc]
    _ = oldToStratumMatchingObjects X n m ≫
        (stratumMatchingObjectsMap f n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject Y m) a) := by
              unfold stratumMatchingObjectsMap
              rw [Pi.map_π]
    _ = (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m) ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject Y m) a := by
            simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem stratumObjectsToMatchingObjects_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumObjectsMap f n m ≫ stratumObjectsToMatchingObjects Y n m =
      stratumObjectsToMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m := by
  apply Pi.hom_ext _ _
  intro a
  calc
    (stratumObjectsMap f n m ≫ stratumObjectsToMatchingObjects Y n m) ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject Y m) a =
        stratumObjectsMap f n m ≫
          (stratumObjectsToMatchingObjects Y n m ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.matchingObject Y m) a) := by
                simp only [Category.assoc]
    _ = stratumObjectsMap f n m ≫
        (Pi.π (fun a : matchingIndexDegree n m => Y.obj a.obj.obj.right) a ≫
          Y.map (eqToHom (newSourceEq a)) ≫
            CategoryTheory.SimplicialObject.matchingMap Y m) := by
            unfold stratumObjectsToMatchingObjects
            rw [Pi.map_π]
    _ = (stratumObjectsMap f n m ≫
          Pi.π (fun a : matchingIndexDegree n m => Y.obj a.obj.obj.right) a) ≫
        (Y.map (eqToHom (newSourceEq a)) ≫
          CategoryTheory.SimplicialObject.matchingMap Y m) := by
            simp only [Category.assoc]
    _ = (Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
          f.app a.obj.obj.right) ≫
        (Y.map (eqToHom (newSourceEq a)) ≫
          CategoryTheory.SimplicialObject.matchingMap Y m) := by
            unfold stratumObjectsMap
            rw [Pi.map_π]
    _ = Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
        ((f.app a.obj.obj.right ≫ Y.map (eqToHom (newSourceEq a))) ≫
          CategoryTheory.SimplicialObject.matchingMap Y m) := by
            simp only [Category.assoc]
    _ = Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
        ((X.map (eqToHom (newSourceEq a)) ≫ f.app (op ⦋m⦌)) ≫
          CategoryTheory.SimplicialObject.matchingMap Y m) := by
            rw [f.naturality]
    _ = Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
        (X.map (eqToHom (newSourceEq a)) ≫
          (CategoryTheory.SimplicialObject.matchingMap X m ≫
            (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) := by
              rw [Category.assoc,
                ← CategoryTheory.SimplicialObject.matchingMap_naturality]
    _ = (Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a)) ≫
            CategoryTheory.SimplicialObject.matchingMap X m) ≫
        (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f := by
            simp only [Category.assoc]
    _ = (stratumObjectsToMatchingObjects X n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject X m) a) ≫
        (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f := by
          unfold stratumObjectsToMatchingObjects
          rw [Pi.map_π]
    _ = stratumObjectsToMatchingObjects X n m ≫
        (Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.matchingObject X m) a ≫
          (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) := by
            simp only [Category.assoc]
    _ = stratumObjectsToMatchingObjects X n m ≫
        (stratumMatchingObjectsMap f n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject Y m) a) := by
              unfold stratumMatchingObjectsMap
              rw [Pi.map_π]
    _ = (stratumObjectsToMatchingObjects X n m ≫
          stratumMatchingObjectsMap f n m) ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject Y m) a := by
            simp only [Category.assoc]

private noncomputable def matchingAttachmentMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingAttachment X n m ⟶ matchingAttachment Y n m :=
  pullback.map
    (oldToStratumMatchingObjects X n m) (stratumObjectsToMatchingObjects X n m)
    (oldToStratumMatchingObjects Y n m) (stratumObjectsToMatchingObjects Y n m)
    (filteredMatchingMap f n m) (stratumObjectsMap f n m)
    (stratumMatchingObjectsMap f n m)
    (oldToStratumMatchingObjects_naturality f n m).symm
    (stratumObjectsToMatchingObjects_naturality f n m).symm

private noncomputable instance matchingSuccessor_finite
    {n m : ℕ} (a : matchingIndexDegree n m) : Finite (matchingSuccessor n m a) :=
  Finite.of_injective (fun x => x.right) (fun x y h => by
    apply StructuredArrow.obj_ext _ _ h
    exact Subsingleton.elim _ _)

private noncomputable instance matchingSuccessor_fintype
    {n m : ℕ} (a : matchingIndexDegree n m) : Fintype (matchingSuccessor n m a) :=
  Fintype.ofFinite _

private instance matchingSuccessor_isThin
    {n m : ℕ} (a : matchingIndexDegree n m) : Quiver.IsThin (matchingSuccessor n m a) :=
  fun _ _ => inferInstance

private abbrev successorRestrictedDiagram
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    matchingSuccessor n m a ⥤ C :=
  StructuredArrow.proj a.obj (belowToMatching n m) ⋙
    filteredMatchingDiagram X n m

private noncomputable abbrev successorBoundary
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) : C :=
  limit (successorRestrictedDiagram X a)

private noncomputable abbrev rawStratumMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  ∏ᶜ fun a : matchingIndexDegree n m => successorBoundary X a

private noncomputable def successorRawFromOld
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    filteredMatchingObject X n m ⟶ successorBoundary X a :=
  limit.pre (filteredMatchingDiagram X n m)
    (StructuredArrow.proj a.obj (belowToMatching n m))

@[reassoc]
private theorem successorRawFromOld_π
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m)
    (x : matchingSuccessor n m a) :
    successorRawFromOld X a ≫ limit.π (successorRestrictedDiagram X a) x =
      limit.π (filteredMatchingDiagram X n m) x.right := by
  apply limit.pre_π

set_option backward.isDefEq.respectTransparency false in
private def successorFromObjectCone
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    Cone (successorRestrictedDiagram X a) where
  pt := X.obj a.obj.obj.right
  π :=
    { app := fun x => X.map x.hom.hom.right
      naturality := by
        intro x y g
        change 𝟙 _ ≫ X.map y.hom.hom.right =
          X.map x.hom.hom.right ≫ X.map g.right.hom.hom.right
        rw [Category.id_comp, ← X.map_comp]
        apply X.congr_map
        have hw := congrArg (fun z => z.hom.right) (StructuredArrow.w g)
        change x.hom.hom.right ≫ g.right.hom.hom.right = y.hom.hom.right at hw
        exact hw.symm }

private noncomputable def successorRawFromObject
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    X.obj a.obj.obj.right ⟶ successorBoundary X a :=
  limit.lift (successorRestrictedDiagram X a) (successorFromObjectCone X a)

@[reassoc]
private theorem successorRawFromObject_π
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m)
    (x : matchingSuccessor n m a) :
    successorRawFromObject X a ≫ limit.π (successorRestrictedDiagram X a) x =
      X.map x.hom.hom.right := by
  apply limit.lift_π

private noncomputable def rawOldToStratumMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    filteredMatchingObject X n m ⟶ rawStratumMatchingObjects X n m :=
  Pi.lift fun a => successorRawFromOld X a

private noncomputable def rawObjectsToStratumMatchingObjects
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumObjects X n m ⟶ rawStratumMatchingObjects X n m :=
  CategoryTheory.Limits.Pi.map fun a => successorRawFromObject X a

@[reassoc]
private theorem rawOldToStratumMatchingObjects_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    rawOldToStratumMatchingObjects X n m ≫
        Pi.π (fun a : matchingIndexDegree n m => successorBoundary X a) a =
      successorRawFromOld X a := by
  unfold rawOldToStratumMatchingObjects
  rw [Pi.lift_comp_π]

@[reassoc]
private theorem rawObjectsToStratumMatchingObjects_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    rawObjectsToStratumMatchingObjects X n m ≫
        Pi.π (fun a : matchingIndexDegree n m => successorBoundary X a) a =
      Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a ≫
        successorRawFromObject X a := by
  unfold rawObjectsToStratumMatchingObjects
  rw [Pi.map_π]

private noncomputable abbrev rawMatchingAttachment
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) : C :=
  pullback (rawOldToStratumMatchingObjects X n m)
    (rawObjectsToStratumMatchingObjects X n m)

private def oldEmbedding (n m : ℕ) :
    matchingIndexBelow n m ⥤ matchingIndexBelow n (m + 1) :=
  belowIncl (n := n) (Nat.le_succ m)

private def newEmbedding (n m : ℕ) :
    matchingIndexDegree n m ⥤ matchingIndexBelow n (m + 1) where
  obj a := ⟨a.obj, by rw [a.property]; exact Nat.lt_succ_self m⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem matching_hom_degree_le {n : ℕ}
    {a b : CategoryTheory.SimplicialObject.matchingIndex n} (g : a ⟶ b) :
    b.obj.right.unop.len ≤ a.obj.right.unop.len := by
  have hfac : g.hom.right.unop ≫ a.obj.hom.unop = b.obj.hom.unop := by
    apply Quiver.Hom.op_inj
    simpa using StructuredArrow.w g.hom
  let _ : Mono (g.hom.right.unop ≫ a.obj.hom.unop) := by
    rw [hfac]
    exact b.property.1
  let _ : Mono g.hom.right.unop :=
    CategoryTheory.mono_of_mono g.hom.right.unop a.obj.hom.unop
  exact SimplexCategory.len_le_of_mono g.hom.right.unop

private theorem below_succ_old_or_new {n m : ℕ} (a : matchingIndexBelow n (m + 1)) :
    a.obj.obj.right.unop.len < m ∨ a.obj.obj.right.unop.len = m := by
  exact Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp a.property)

private def oldPart {n m : ℕ} (a : matchingIndexBelow n (m + 1))
    (h : a.obj.obj.right.unop.len < m) : matchingIndexBelow n m :=
  ⟨a.obj, h⟩

private def newPart {n m : ℕ} (a : matchingIndexBelow n (m + 1))
    (h : ¬ a.obj.obj.right.unop.len < m) : matchingIndexDegree n m :=
  ⟨a.obj, le_antisymm (Nat.lt_succ_iff.mp a.property) (Nat.le_of_not_gt h)⟩

private noncomputable def attachmentProjection
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) :
    rawMatchingAttachment X n m ⟶ (filteredMatchingDiagram X n (m + 1)).obj a :=
  if h : a.obj.obj.right.unop.len < m then
    pullback.fst (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) ≫
      limit.π (filteredMatchingDiagram X n m) (oldPart a h)
  else
    pullback.snd (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) ≫
      Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) (newPart a h)

@[simp]
private theorem attachmentProjection_old
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) (h : a.obj.obj.right.unop.len < m) :
    attachmentProjection X a =
      pullback.fst (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) ≫
        limit.π (filteredMatchingDiagram X n m) (oldPart a h) := by
  simp [attachmentProjection, h]
  congr

@[simp]
private theorem attachmentProjection_new
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) (h : ¬ a.obj.obj.right.unop.len < m) :
    attachmentProjection X a =
      pullback.snd (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) ≫
        Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) (newPart a h) := by
  simp [attachmentProjection, h]
  congr

private theorem oldEmbedding_oldPart_eq {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) (h : a.obj.obj.right.unop.len < m) :
    (oldEmbedding n m).obj (oldPart a h) = a :=
  ObjectProperty.FullSubcategory.ext rfl

private theorem newEmbedding_newPart_eq {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) (h : ¬ a.obj.obj.right.unop.len < m) :
    (newEmbedding n m).obj (newPart a h) = a :=
  ObjectProperty.FullSubcategory.ext rfl

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentProjection_naturality
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    {a b : matchingIndexBelow n (m + 1)} (g : a ⟶ b) :
    attachmentProjection X a ≫ (filteredMatchingDiagram X n (m + 1)).map g =
      attachmentProjection X b := by
  by_cases ha : a.obj.obj.right.unop.len < m
  · have hle := matching_hom_degree_le g.hom
    have hb : b.obj.obj.right.unop.len < m := hle.trans_lt ha
    let gOld : oldPart a ha ⟶ oldPart b hb := ObjectProperty.homMk g.hom
    have hw := limit.w (filteredMatchingDiagram X n m) gOld
    have hw' := congrArg
      (fun t => pullback.fst (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) ≫ t) hw
    have hgmap : (filteredMatchingDiagram X n (m + 1)).map g =
        (filteredMatchingDiagram X n m).map gOld := rfl
    rw [attachmentProjection_old X a ha, attachmentProjection_old X b hb]
    rw [hgmap]
    simpa only [Category.assoc] using hw'
  · by_cases hb : b.obj.obj.right.unop.len < m
    · let aNew := newPart a ha
      let yright := oldPart b hb
      let yhom : aNew.obj ⟶ (belowToMatching n m).obj yright :=
        ObjectProperty.homMk g.hom.hom
      let y : matchingSuccessor n m aNew := StructuredArrow.mk yhom
      let preπ := Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) aNew ≫
        limit.π (successorRestrictedDiagram X aNew) y
      have hleft : rawOldToStratumMatchingObjects X n m ≫ preπ =
          limit.π (filteredMatchingDiagram X n m) (oldPart b hb) := by
        dsimp [preπ, rawOldToStratumMatchingObjects]
        rw [Pi.lift_comp_π_assoc]
        apply successorRawFromOld_π
      have hright : rawObjectsToStratumMatchingObjects X n m ≫ preπ =
          Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew ≫
            X.map g.hom.hom.right := by
        have hπ := successorRawFromObject_π X aNew y
        have hy : y.hom.hom.right = g.hom.hom.right := rfl
        calc
          rawObjectsToStratumMatchingObjects X n m ≫ preπ =
              (Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew ≫
                successorRawFromObject X aNew) ≫
                  limit.π (successorRestrictedDiagram X aNew) y := by
                    dsimp [preπ]
                    rw [← Category.assoc, rawObjectsToStratumMatchingObjects_π]
          _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew ≫
              X.map y.hom.hom.right := by
                simpa only [Category.assoc] using congrArg
                  (fun t => Pi.π (fun c : matchingIndexDegree n m =>
                    X.obj c.obj.obj.right) aNew ≫ t) hπ
          _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew ≫
              X.map g.hom.hom.right := by rw [hy]
      have hcondition :
          pullback.fst (rawOldToStratumMatchingObjects X n m)
              (rawObjectsToStratumMatchingObjects X n m) ≫
              rawOldToStratumMatchingObjects X n m =
            pullback.snd (rawOldToStratumMatchingObjects X n m)
              (rawObjectsToStratumMatchingObjects X n m) ≫
              rawObjectsToStratumMatchingObjects X n m :=
        pullback.condition
      have hcond := congrArg (fun t => t ≫ preπ) hcondition
      have hcond' : pullback.fst (rawOldToStratumMatchingObjects X n m)
              (rawObjectsToStratumMatchingObjects X n m) ≫
            (rawOldToStratumMatchingObjects X n m ≫ preπ) =
          pullback.snd (rawOldToStratumMatchingObjects X n m)
              (rawObjectsToStratumMatchingObjects X n m) ≫
            (rawObjectsToStratumMatchingObjects X n m ≫ preπ) := by
        simpa only [Category.assoc] using hcond
      rw [hleft, hright] at hcond'
      rw [attachmentProjection_new X a ha, attachmentProjection_old X b hb]
      change (pullback.snd (rawOldToStratumMatchingObjects X n m)
            (rawObjectsToStratumMatchingObjects X n m) ≫
          Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew) ≫
            X.map g.hom.hom.right = _
      simpa only [Category.assoc] using hcond'.symm
    · let aNew := newPart a ha
      let bNew := newPart b hb
      let gNew : aNew ⟶ bNew := ObjectProperty.homMk g.hom
      have hab : aNew = bNew := eq_of_hom_in_degree gNew
      have habObj : a.obj = b.obj := congrArg (fun z => z.obj) hab
      have habBelow : a = b := ObjectProperty.FullSubcategory.ext habObj
      subst b
      have hg : g = 𝟙 a := Subsingleton.elim _ _
      subst g
      simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def attachmentCone
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    Cone (filteredMatchingDiagram X n (m + 1)) where
  pt := rawMatchingAttachment X n m
  π :=
    { app := attachmentProjection X
      naturality := by
        intro a b g
        change 𝟙 _ ≫ attachmentProjection X b =
          attachmentProjection X a ≫
            (filteredMatchingDiagram X n (m + 1)).map g
        rw [Category.id_comp]
        exact (attachmentProjection_naturality X g).symm }

set_option backward.isDefEq.respectTransparency false in
private def attachmentOldCone
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1))) :
    Cone (filteredMatchingDiagram X n m) where
  pt := s.pt
  π :=
    { app := fun a => s.π.app ((oldEmbedding n m).obj a)
      naturality := by
        intro a b g
        simpa [filteredMatchingDiagram, oldEmbedding, belowIncl] using
          (s.w ((oldEmbedding n m).map g)).symm }

private noncomputable def attachmentOldLift
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1))) :
    s.pt ⟶ filteredMatchingObject X n m :=
  limit.lift (filteredMatchingDiagram X n m) (attachmentOldCone X s)

private noncomputable def attachmentNewLift
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1))) :
    s.pt ⟶ stratumObjects X n m :=
  Pi.lift fun a => s.π.app ((newEmbedding n m).obj a)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem attachmentNewLift_π
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1)))
    (a : matchingIndexDegree n m) :
    attachmentNewLift X s ≫
        Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a =
      s.π.app ((newEmbedding n m).obj a) := by
  unfold attachmentNewLift
  rw [Pi.lift_comp_π]

private def successorStepHom {n m : ℕ} {a : matchingIndexDegree n m}
    (x : matchingSuccessor n m a) :
    (newEmbedding n m).obj a ⟶ (oldEmbedding n m).obj x.right :=
  ObjectProperty.homMk x.hom

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentLift_compat
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1))) :
    attachmentOldLift X s ≫ rawOldToStratumMatchingObjects X n m =
      attachmentNewLift X s ≫ rawObjectsToStratumMatchingObjects X n m := by
  apply Pi.hom_ext _ _
  intro a
  apply limit.hom_ext
  intro x
  calc
    ((attachmentOldLift X s ≫ rawOldToStratumMatchingObjects X n m) ≫
          Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) a) ≫
          limit.π (successorRestrictedDiagram X a) x =
        attachmentOldLift X s ≫ limit.π (filteredMatchingDiagram X n m) x.right := by
          calc
            ((attachmentOldLift X s ≫ rawOldToStratumMatchingObjects X n m) ≫
                  Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) a) ≫
                limit.π (successorRestrictedDiagram X a) x =
              attachmentOldLift X s ≫
                ((rawOldToStratumMatchingObjects X n m ≫
                    Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) a) ≫
                  limit.π (successorRestrictedDiagram X a) x) := by
                    simp only [Category.assoc]
            _ = attachmentOldLift X s ≫
                (successorRawFromOld X a ≫
                  limit.π (successorRestrictedDiagram X a) x) := by
                    rw [rawOldToStratumMatchingObjects_π]
            _ = attachmentOldLift X s ≫
                limit.π (filteredMatchingDiagram X n m) x.right := by
                  rw [successorRawFromOld_π]
    _ = s.π.app ((oldEmbedding n m).obj x.right) := by
          apply limit.lift_π
    _ = s.π.app ((newEmbedding n m).obj a) ≫
        (filteredMatchingDiagram X n (m + 1)).map (successorStepHom x) := by
          rw [s.w (successorStepHom x)]
    _ = s.π.app ((newEmbedding n m).obj a) ≫ X.map x.hom.hom.right := by rfl
    _ = attachmentNewLift X s ≫
        (Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map x.hom.hom.right) := by
            simpa only [Category.assoc] using
              (attachmentNewLift_π_assoc X s a (X.map x.hom.hom.right)).symm
    _ = attachmentNewLift X s ≫
        ((rawObjectsToStratumMatchingObjects X n m ≫
            Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) a) ≫
          limit.π (successorRestrictedDiagram X a) x) := by
            rw [rawObjectsToStratumMatchingObjects_π,
              Category.assoc, successorRawFromObject_π]
    _ = ((attachmentNewLift X s ≫ rawObjectsToStratumMatchingObjects X n m) ≫
        Pi.π (fun c : matchingIndexDegree n m => successorBoundary X c) a) ≫
          limit.π (successorRestrictedDiagram X a) x := by
            simp only [Category.assoc]

private noncomputable def attachmentLift
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1))) :
    s.pt ⟶ rawMatchingAttachment X n m :=
  pullback.lift (attachmentOldLift X s) (attachmentNewLift X s)
    (attachmentLift_compat X s)

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentLift_fac
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (s : Cone (filteredMatchingDiagram X n (m + 1)))
    (a : matchingIndexBelow n (m + 1)) :
    attachmentLift X s ≫ attachmentProjection X a = s.π.app a := by
  by_cases h : a.obj.obj.right.unop.len < m
  · rw [attachmentProjection_old X a h]
    dsimp [attachmentLift, attachmentOldLift]
    rw [pullback.lift_fst_assoc, limit.lift_π]
    cases oldEmbedding_oldPart_eq a h
    rfl
  · rw [attachmentProjection_new X a h]
    dsimp [attachmentLift, attachmentNewLift]
    rw [pullback.lift_snd_assoc, Pi.lift_comp_π]
    cases newEmbedding_newPart_eq a h
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def attachmentIsLimit
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    IsLimit (attachmentCone X n m) where
  lift s := attachmentLift X s
  fac s a := attachmentLift_fac X s a
  uniq s k hk := by
    apply pullback.hom_ext
    · apply limit.hom_ext
      intro a
      let z := (oldEmbedding n m).obj a
      have h := (hk z).trans (attachmentLift_fac X s z).symm
      change k ≫ attachmentProjection X z = attachmentLift X s ≫ attachmentProjection X z at h
      have hz : z.obj.obj.right.unop.len < m := a.property
      rw [attachmentProjection_old X z hz] at h
      have hza : oldPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
      cases hza
      simpa [z, oldPart, oldEmbedding, attachmentCone, Category.assoc] using h
    · apply Pi.hom_ext _ _
      intro a
      let z := (newEmbedding n m).obj a
      have h := (hk z).trans (attachmentLift_fac X s z).symm
      change k ≫ attachmentProjection X z = attachmentLift X s ≫ attachmentProjection X z at h
      have hz : ¬ z.obj.obj.right.unop.len < m := by
        change ¬ a.obj.obj.right.unop.len < m
        rw [a.property]
        exact Nat.lt_irrefl m
      rw [attachmentProjection_new X z hz] at h
      have hza : newPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
      cases hza
      simpa [z, newPart, newEmbedding, attachmentCone, Category.assoc] using h

private noncomputable def attachmentLimitCone
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    LimitCone (filteredMatchingDiagram X n (m + 1)) :=
  ⟨attachmentCone X n m, attachmentIsLimit X n m⟩

/-- The raw successor-boundary pullback presents the next filtered matching limit. -/
private noncomputable def rawMatchingAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawMatchingAttachment X n m ≅ filteredMatchingObject X n (m + 1) :=
  (limit.isoLimitCone (attachmentLimitCone X n m)).symm

@[reassoc]
private theorem attachmentIso_hom_projection
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ}
    (a : matchingIndexBelow n (m + 1)) :
    (rawMatchingAttachmentIso X n m).hom ≫
        limit.π (filteredMatchingDiagram X n (m + 1)) a =
      attachmentProjection X a := by
  change (limit.isoLimitCone (attachmentLimitCone X n m)).inv ≫
      limit.π (filteredMatchingDiagram X n (m + 1)) a = _
  exact limit.isoLimitCone_inv_π (attachmentLimitCone X n m) a

@[reassoc]
private theorem rawMatchingAttachmentIso_hom_fst
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (rawMatchingAttachmentIso X n m).hom ≫
        filteredMatchingRestrict X (Nat.le_succ m) =
      pullback.fst (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) := by
  apply limit.hom_ext
  intro a
  let z := (oldEmbedding n m).obj a
  have hz : z.obj.obj.right.unop.len < m := a.property
  have hza : oldPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
  have hproj := attachmentIso_hom_projection X z
  rw [attachmentProjection_old X z hz] at hproj
  have hrestrict := filteredMatchingRestrict_π X (Nat.le_succ m) a
  have hrestrict' : filteredMatchingRestrict X (Nat.le_succ m) ≫
        limit.π (filteredMatchingDiagram X n m) a =
      limit.π (filteredMatchingDiagram X n (m + 1)) z := by
    simpa [z, oldEmbedding] using hrestrict
  cases hza
  have hchain : ((rawMatchingAttachmentIso X n m).hom ≫
      filteredMatchingRestrict X (Nat.le_succ m)) ≫
        limit.π (filteredMatchingDiagram X n m) a =
      pullback.fst (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) ≫
        limit.π (filteredMatchingDiagram X n m) (oldPart z hz) := by
    rw [Category.assoc, hrestrict']
    exact hproj
  exact hchain

@[reassoc]
private theorem rawMatchingAttachmentIso_hom_new_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    (rawMatchingAttachmentIso X n m).hom ≫
        limit.π (filteredMatchingDiagram X n (m + 1)) ((newEmbedding n m).obj a) =
      pullback.snd (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) ≫
        Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a := by
  let z := (newEmbedding n m).obj a
  have hz : ¬ z.obj.obj.right.unop.len < m := by
    change ¬ a.obj.obj.right.unop.len < m
    rw [a.property]
    exact Nat.lt_irrefl m
  have hza : newPart z hz = a := ObjectProperty.FullSubcategory.ext rfl
  have hproj := attachmentIso_hom_projection X z
  rw [attachmentProjection_new X z hz] at hproj
  cases hza
  exact hproj

set_option backward.isDefEq.respectTransparency false in
private noncomputable def successorInverseDiagramIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    (successorEquivalence a).symm.functor ⋙ successorRestrictedDiagram X a ≅
      CategoryTheory.SimplicialObject.matchingDiagram X m :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {x y} g => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- The raw successor boundary is the ordinary degree-`m` matching object. -/
private noncomputable def successorBoundaryIso
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m) :
    successorBoundary X a ≅ CategoryTheory.SimplicialObject.matchingObject X m :=
  (HasLimit.isoOfEquivalence (successorEquivalence a).symm
    (successorInverseDiagramIso X a)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem successorBoundaryIso_hom_π
    (X : CategoryTheory.SimplicialObject C) {n m : ℕ} (a : matchingIndexDegree n m)
    (b : CategoryTheory.SimplicialObject.matchingIndex m) :
    (successorBoundaryIso X a).hom ≫
        CategoryTheory.SimplicialObject.matchingπ X m b =
      limit.π (successorRestrictedDiagram X a)
        ((matchingIndexToSuccessor a).obj b) := by
  have h := HasLimit.isoOfEquivalence_inv_π (successorEquivalence a).symm
    (successorInverseDiagramIso X a) b
  change _ = limit.π (successorRestrictedDiagram X a)
      ((matchingIndexToSuccessor a).obj b) ≫ (Iso.refl _).hom at h
  simpa [successorBoundaryIso, CategoryTheory.SimplicialObject.matchingπ] using h

private noncomputable def rawStratumMatchingObjectsIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawStratumMatchingObjects X n m ≅ stratumMatchingObjects X n m :=
  (lim : (Discrete (matchingIndexDegree n m) ⥤ C) ⥤ C).mapIso
    (Discrete.natIso fun a => successorBoundaryIso X a.as)

@[reassoc]
private theorem rawStratumMatchingObjectsIso_hom_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    (rawStratumMatchingObjectsIso X n m).hom ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a =
      Pi.π (fun a : matchingIndexDegree n m => successorBoundary X a) a ≫
        (successorBoundaryIso X a).hom := by
  apply limit.map_π

set_option backward.isDefEq.respectTransparency false in
private theorem rawOldToStratumMatchingObjects_compat
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawOldToStratumMatchingObjects X n m ≫
        (rawStratumMatchingObjectsIso X n m).hom =
      oldToStratumMatchingObjects X n m := by
  apply Pi.hom_ext _ _
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc]
  rw [rawStratumMatchingObjectsIso_hom_π_assoc,
    rawOldToStratumMatchingObjects_π_assoc]
  change successorRawFromOld X a ≫
      ((successorBoundaryIso X a).hom ≫
        CategoryTheory.SimplicialObject.matchingπ X m b) = _
  rw [successorBoundaryIso_hom_π, successorRawFromOld_π]
  rw [oldToStratumMatchingObjects_π_assoc]
  exact (successorBoundaryFromOld_π X a b).symm

set_option backward.isDefEq.respectTransparency false in
private theorem rawObjectsToStratumMatchingObjects_compat
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawObjectsToStratumMatchingObjects X n m ≫
        (rawStratumMatchingObjectsIso X n m).hom =
      stratumObjectsToMatchingObjects X n m := by
  apply Pi.hom_ext _ _
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc]
  rw [rawStratumMatchingObjectsIso_hom_π_assoc,
    rawObjectsToStratumMatchingObjects_π_assoc]
  change Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
      successorRawFromObject X a ≫
        ((successorBoundaryIso X a).hom ≫
          CategoryTheory.SimplicialObject.matchingπ X m b) = _
  rw [successorBoundaryIso_hom_π, successorRawFromObject_π]
  rw [stratumObjectsToMatchingObjects_π_assoc]
  have hm := CategoryTheory.SimplicialObject.matchingMap_π X m b
  calc
    Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map ((matchingIndexToSuccessor a).obj b).hom.hom.right =
        Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a) ≫ b.obj.hom) := by rfl
    _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
        (X.map (eqToHom (newSourceEq a)) ≫ X.map b.obj.hom) := by
          rw [X.map_comp]
    _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
        (X.map (eqToHom (newSourceEq a)) ≫
          (CategoryTheory.SimplicialObject.matchingMap X m ≫
            CategoryTheory.SimplicialObject.matchingπ X m b)) := by rw [hm]

private noncomputable def rawToStandardAttachmentMap
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawMatchingAttachment X n m ⟶ matchingAttachment X n m :=
  pullback.map
    (rawOldToStratumMatchingObjects X n m)
    (rawObjectsToStratumMatchingObjects X n m)
    (oldToStratumMatchingObjects X n m)
    (stratumObjectsToMatchingObjects X n m)
    (𝟙 _) (𝟙 _) (rawStratumMatchingObjectsIso X n m).hom
    (by simpa using rawOldToStratumMatchingObjects_compat X n m)
    (by simpa using rawObjectsToStratumMatchingObjects_compat X n m)

private noncomputable instance rawToStandardAttachmentMap_isIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    IsIso (rawToStandardAttachmentMap X n m) := by
  dsimp [rawToStandardAttachmentMap]
  infer_instance

private noncomputable def rawToStandardAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    rawMatchingAttachment X n m ≅ matchingAttachment X n m :=
  asIso (rawToStandardAttachmentMap X n m)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_hom_fst
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (rawToStandardAttachmentIso X n m).hom ≫
        pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) =
      pullback.fst (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) := by
  change rawToStandardAttachmentMap X n m ≫
      pullback.fst (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) = _
  unfold rawToStandardAttachmentMap
  rw [pullback.lift_fst, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_hom_snd
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (rawToStandardAttachmentIso X n m).hom ≫
        pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) =
      pullback.snd (rawOldToStratumMatchingObjects X n m)
        (rawObjectsToStratumMatchingObjects X n m) := by
  change rawToStandardAttachmentMap X n m ≫
      pullback.snd (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) = _
  unfold rawToStandardAttachmentMap
  rw [pullback.lift_snd, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_inv_fst
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (rawToStandardAttachmentIso X n m).inv ≫
        pullback.fst (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) =
      pullback.fst (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) := by
  apply (cancel_epi (rawToStandardAttachmentIso X n m).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    rawToStandardAttachmentIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rawToStandardAttachmentIso_inv_snd
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (rawToStandardAttachmentIso X n m).inv ≫
        pullback.snd (rawOldToStratumMatchingObjects X n m)
          (rawObjectsToStratumMatchingObjects X n m) =
      pullback.snd (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) := by
  apply (cancel_epi (rawToStandardAttachmentIso X n m).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    rawToStandardAttachmentIso_hom_snd]

/-- The standard matching attachment presents the next filtered matching limit. -/
private noncomputable def standardMatchingAttachmentIso
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    matchingAttachment X n m ≅ filteredMatchingObject X n (m + 1) :=
  (rawToStandardAttachmentIso X n m).symm ≪≫ rawMatchingAttachmentIso X n m

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem standardMatchingAttachmentIso_hom_restrict
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    (standardMatchingAttachmentIso X n m).hom ≫
        filteredMatchingRestrict X (Nat.le_succ m) =
      pullback.fst (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) := by
  dsimp [standardMatchingAttachmentIso]
  rw [Category.assoc, rawMatchingAttachmentIso_hom_fst,
    rawToStandardAttachmentIso_inv_fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem standardMatchingAttachmentIso_hom_new_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    (standardMatchingAttachmentIso X n m).hom ≫
        limit.π (filteredMatchingDiagram X n (m + 1)) ((newEmbedding n m).obj a) =
      pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        Pi.π (fun a : matchingIndexDegree n m => X.obj a.obj.obj.right) a := by
  dsimp [standardMatchingAttachmentIso]
  rw [Category.assoc, rawMatchingAttachmentIso_hom_new_π,
    rawToStandardAttachmentIso_inv_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem standardMatchingAttachmentIso_hom_old_π
    (X : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexBelow n m) :
    (standardMatchingAttachmentIso X n m).hom ≫
        limit.π (filteredMatchingDiagram X n (m + 1)) ((oldEmbedding n m).obj a) =
      pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        limit.π (filteredMatchingDiagram X n m) a := by
  calc
    (standardMatchingAttachmentIso X n m).hom ≫
          limit.π (filteredMatchingDiagram X n (m + 1)) ((oldEmbedding n m).obj a) =
        (standardMatchingAttachmentIso X n m).hom ≫
          (filteredMatchingRestrict X (Nat.le_succ m) ≫
            limit.π (filteredMatchingDiagram X n m) a) := by
              have hr := filteredMatchingRestrict_π X (Nat.le_succ m) a
              simpa [oldEmbedding] using congrArg
                (fun t => (standardMatchingAttachmentIso X n m).hom ≫ t) hr.symm
    _ = ((standardMatchingAttachmentIso X n m).hom ≫
          filteredMatchingRestrict X (Nat.le_succ m)) ≫
        limit.π (filteredMatchingDiagram X n m) a := by
          simp only [Category.assoc]
    _ = pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        limit.π (filteredMatchingDiagram X n m) a := by
          rw [standardMatchingAttachmentIso_hom_restrict]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredMatchingRestrict_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m m' : ℕ} (h : m ≤ m') :
    filteredMatchingMap f n m' ≫ filteredMatchingRestrict Y h =
      filteredMatchingRestrict X h ≫ filteredMatchingMap f n m := by
  apply limit.hom_ext
  intro a
  calc
    (filteredMatchingMap f n m' ≫ filteredMatchingRestrict Y h) ≫
          limit.π (filteredMatchingDiagram Y n m) a =
        filteredMatchingMap f n m' ≫
          limit.π (filteredMatchingDiagram Y n m') ((belowIncl h).obj a) := by
            rw [Category.assoc, filteredMatchingRestrict_π]
    _ = limit.π (filteredMatchingDiagram X n m') ((belowIncl h).obj a) ≫
        f.app a.obj.obj.right := by
          have hmap := filteredMatchingMap_π f n m' ((belowIncl h).obj a)
          change filteredMatchingMap f n m' ≫
              limit.π (filteredMatchingDiagram Y n m') ((belowIncl h).obj a) =
            limit.π (filteredMatchingDiagram X n m') ((belowIncl h).obj a) ≫
              f.app a.obj.obj.right at hmap
          exact hmap
    _ = (filteredMatchingRestrict X h ≫
          limit.π (filteredMatchingDiagram X n m) a) ≫ f.app a.obj.obj.right := by
            rw [filteredMatchingRestrict_π]
    _ = filteredMatchingRestrict X h ≫
        (limit.π (filteredMatchingDiagram X n m) a ≫ f.app a.obj.obj.right) := by
          simp only [Category.assoc]
    _ = filteredMatchingRestrict X h ≫
        (filteredMatchingMap f n m ≫
          limit.π (filteredMatchingDiagram Y n m) a) := by
            rw [filteredMatchingMap_π]
    _ = (filteredMatchingRestrict X h ≫ filteredMatchingMap f n m) ≫
        limit.π (filteredMatchingDiagram Y n m) a := by
          simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem matchingAttachmentMap_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingAttachmentMap f n m ≫
        pullback.fst (oldToStratumMatchingObjects Y n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        filteredMatchingMap f n m := by
  unfold matchingAttachmentMap
  rw [pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem matchingAttachmentMap_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingAttachmentMap f n m ≫
        pullback.snd (oldToStratumMatchingObjects Y n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        stratumObjectsMap f n m := by
  unfold matchingAttachmentMap
  rw [pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the standard matching attachment presentation. -/
private theorem standardMatchingAttachmentIso_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (standardMatchingAttachmentIso X n m).hom ≫
        filteredMatchingMap f n (m + 1) =
      matchingAttachmentMap f n m ≫ (standardMatchingAttachmentIso Y n m).hom := by
  apply limit.hom_ext
  intro a
  by_cases h : a.obj.obj.right.unop.len < m
  · let aOld := oldPart a h
    have ha : (oldEmbedding n m).obj aOld = a := oldEmbedding_oldPart_eq a h
    cases ha
    calc
      ((standardMatchingAttachmentIso X n m).hom ≫
            filteredMatchingMap f n (m + 1)) ≫
          limit.π (filteredMatchingDiagram Y n (m + 1)) ((oldEmbedding n m).obj aOld) =
        (standardMatchingAttachmentIso X n m).hom ≫
          (limit.π (filteredMatchingDiagram X n (m + 1))
              ((oldEmbedding n m).obj aOld) ≫
            f.app aOld.obj.obj.right) := by
              have hmap := filteredMatchingMap_π f n (m + 1)
                ((oldEmbedding n m).obj aOld)
              change filteredMatchingMap f n (m + 1) ≫
                    limit.π (filteredMatchingDiagram Y n (m + 1))
                      ((oldEmbedding n m).obj aOld) =
                  limit.π (filteredMatchingDiagram X n (m + 1))
                      ((oldEmbedding n m).obj aOld) ≫ f.app aOld.obj.obj.right at hmap
              rw [Category.assoc, hmap]
      _ = pullback.fst (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          limit.π (filteredMatchingDiagram X n m) aOld ≫
            f.app aOld.obj.obj.right := by
              simpa only [Category.assoc] using
                standardMatchingAttachmentIso_hom_old_π_assoc X n m aOld
                  (f.app aOld.obj.obj.right)
      _ = pullback.fst (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          (filteredMatchingMap f n m ≫
            limit.π (filteredMatchingDiagram Y n m) aOld) := by
              rw [filteredMatchingMap_π]
      _ = matchingAttachmentMap f n m ≫
          pullback.fst (oldToStratumMatchingObjects Y n m)
            (stratumObjectsToMatchingObjects Y n m) ≫
          limit.π (filteredMatchingDiagram Y n m) aOld := by
            simpa only [Category.assoc] using
              (matchingAttachmentMap_fst_assoc f n m
                (limit.π (filteredMatchingDiagram Y n m) aOld)).symm
      _ = matchingAttachmentMap f n m ≫
          (standardMatchingAttachmentIso Y n m).hom ≫
            limit.π (filteredMatchingDiagram Y n (m + 1))
              ((oldEmbedding n m).obj aOld) := by
                simpa only [Category.assoc] using congrArg
                  (fun t => matchingAttachmentMap f n m ≫ t)
                  (standardMatchingAttachmentIso_hom_old_π Y n m aOld).symm
      _ = (matchingAttachmentMap f n m ≫
            (standardMatchingAttachmentIso Y n m).hom) ≫
          limit.π (filteredMatchingDiagram Y n (m + 1))
            ((oldEmbedding n m).obj aOld) := by
            simp only [Category.assoc]
  · let aNew := newPart a h
    have ha : (newEmbedding n m).obj aNew = a := newEmbedding_newPart_eq a h
    cases ha
    calc
      ((standardMatchingAttachmentIso X n m).hom ≫
            filteredMatchingMap f n (m + 1)) ≫
          limit.π (filteredMatchingDiagram Y n (m + 1)) ((newEmbedding n m).obj aNew) =
        (standardMatchingAttachmentIso X n m).hom ≫
          (limit.π (filteredMatchingDiagram X n (m + 1))
              ((newEmbedding n m).obj aNew) ≫
            f.app aNew.obj.obj.right) := by
              have hmap := filteredMatchingMap_π f n (m + 1)
                ((newEmbedding n m).obj aNew)
              change filteredMatchingMap f n (m + 1) ≫
                    limit.π (filteredMatchingDiagram Y n (m + 1))
                      ((newEmbedding n m).obj aNew) =
                  limit.π (filteredMatchingDiagram X n (m + 1))
                      ((newEmbedding n m).obj aNew) ≫ f.app aNew.obj.obj.right at hmap
              rw [Category.assoc, hmap]
      _ = pullback.snd (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) aNew ≫
            f.app aNew.obj.obj.right := by
              simpa only [Category.assoc] using
                standardMatchingAttachmentIso_hom_new_π_assoc X n m aNew
                  (f.app aNew.obj.obj.right)
      _ = pullback.snd (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          (stratumObjectsMap f n m ≫
            Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) aNew) := by
              unfold stratumObjectsMap
              rw [Pi.map_π]
      _ = matchingAttachmentMap f n m ≫
          pullback.snd (oldToStratumMatchingObjects Y n m)
            (stratumObjectsToMatchingObjects Y n m) ≫
          Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) aNew := by
            simpa only [Category.assoc] using
              (matchingAttachmentMap_snd_assoc f n m
                (Pi.π (fun c : matchingIndexDegree n m =>
                  Y.obj c.obj.obj.right) aNew)).symm
      _ = matchingAttachmentMap f n m ≫
          (standardMatchingAttachmentIso Y n m).hom ≫
            limit.π (filteredMatchingDiagram Y n (m + 1))
              ((newEmbedding n m).obj aNew) := by
                simpa only [Category.assoc] using congrArg
                  (fun t => matchingAttachmentMap f n m ≫ t)
                  (standardMatchingAttachmentIso_hom_new_π Y n m aNew).symm
      _ = (matchingAttachmentMap f n m ≫
            (standardMatchingAttachmentIso Y n m).hom) ≫
          limit.π (filteredMatchingDiagram Y n (m + 1))
            ((newEmbedding n m).obj aNew) := by
            simp only [Category.assoc]

/-- The target of the finite-stratum relative matching map. -/
private noncomputable abbrev relativeStratumTarget
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  pullback (stratumObjectsToMatchingObjects Y n m)
    (stratumMatchingObjectsMap f n m)

private noncomputable def relativeStratumMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    stratumObjects X n m ⟶ relativeStratumTarget f n m :=
  pullback.lift (stratumObjectsMap f n m) (stratumObjectsToMatchingObjects X n m)
    (stratumObjectsToMatchingObjects_naturality f n m)

@[reassoc]
private theorem relativeStratumMap_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumMap f n m ≫
        pullback.fst (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) =
      stratumObjectsMap f n m := by
  apply pullback.lift_fst

@[reassoc]
private theorem relativeStratumMap_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumMap f n m ≫
        pullback.snd (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) =
      stratumObjectsToMatchingObjects X n m := by
  apply pullback.lift_snd

private noncomputable abbrev productRelativeMatchingSource
    {X Y : CategoryTheory.SimplicialObject C} (_f : X ⟶ Y) (n m : ℕ) : C :=
  ∏ᶜ fun _ : matchingIndexDegree n m => X.obj (op ⦋m⦌)

private noncomputable abbrev productRelativeMatchingTarget
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  ∏ᶜ fun _ : matchingIndexDegree n m =>
    CategoryTheory.SimplicialObject.relativeMatchingObject f m

private def relativeMatchingToStratumFst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (a : matchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.relativeMatchingObject f m ⟶
      Y.obj a.obj.obj.right :=
  pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
      ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) ≫
    Y.map (eqToHom (newSourceEq a).symm)

private def relativeMatchingToStratumSnd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (_a : matchingIndexDegree n m) :
    CategoryTheory.SimplicialObject.relativeMatchingObject f m ⟶
      CategoryTheory.SimplicialObject.matchingObject X m :=
  pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
    ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)

private theorem stratumRelativeMatching_isPullback
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    {n m : ℕ} (a : matchingIndexDegree n m) :
    IsPullback
      (relativeMatchingToStratumFst f a)
      (relativeMatchingToStratumSnd f a)
      (Y.map (eqToHom (newSourceEq a)) ≫
        CategoryTheory.SimplicialObject.matchingMap Y m)
      ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) := by
  have h := IsPullback.of_hasPullback
    (CategoryTheory.SimplicialObject.matchingMap Y m)
    ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)
  apply h.of_iso' (Iso.refl _)
    (Y.mapIso (CategoryTheory.eqToIso (newSourceEq a))) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, CategoryTheory.eqToIso.hom]
    unfold relativeMatchingToStratumFst
    rw [Category.assoc, ← Y.map_comp, eqToHom_trans, eqToHom_refl,
      Y.map_id, Category.comp_id]
  · simp [relativeMatchingToStratumSnd]
  · simp [Functor.mapIso_hom, CategoryTheory.eqToIso.hom]
  · simp

private noncomputable def productRelativeMatchingFst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    productRelativeMatchingTarget f n m ⟶ stratumObjects Y n m :=
  CategoryTheory.Limits.Pi.map fun a => relativeMatchingToStratumFst f a

private noncomputable def productRelativeMatchingSnd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    productRelativeMatchingTarget f n m ⟶ stratumMatchingObjects X n m :=
  CategoryTheory.Limits.Pi.map fun a => relativeMatchingToStratumSnd f a

private theorem productRelativeMatching_isPullback
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPullback
      (productRelativeMatchingFst f n m)
      (productRelativeMatchingSnd f n m)
      (stratumObjectsToMatchingObjects Y n m)
      (stratumMatchingObjectsMap f n m) := by
  let F₀ : Discrete (matchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.relativeMatchingObject f m
  let F₁ : Discrete (matchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun a => Y.obj a.obj.obj.right
  let F₂ : Discrete (matchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.matchingObject X m
  let F₃ : Discrete (matchingIndexDegree n m) ⥤ C :=
    Discrete.functor fun _ => CategoryTheory.SimplicialObject.matchingObject Y m
  let α : F₀ ⟶ F₁ := Discrete.natTrans fun a => relativeMatchingToStratumFst f a.as
  let β : F₀ ⟶ F₂ := Discrete.natTrans fun a => relativeMatchingToStratumSnd f a.as
  let γ : F₁ ⟶ F₃ := Discrete.natTrans fun a =>
    Y.map (eqToHom (newSourceEq a.as)) ≫
      CategoryTheory.SimplicialObject.matchingMap Y m
  let δ : F₂ ⟶ F₃ := Discrete.natTrans fun _ =>
    (CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f
  have hPointwise : IsPullback α β γ δ :=
    IsPullback.of_forall_isPullback_app fun a =>
      stratumRelativeMatching_isPullback f a.as
  have hMapped := hPointwise.map
    (lim : (Discrete (matchingIndexDegree n m) ⥤ C) ⥤ C)
  simpa [F₀, F₁, F₂, F₃, α, β, γ, δ, CategoryTheory.Limits.Pi.map,
    productRelativeMatchingFst, productRelativeMatchingSnd,
    stratumObjectsToMatchingObjects, stratumMatchingObjectsMap] using hMapped

private noncomputable def relativeStratumTargetIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    relativeStratumTarget f n m ≅ productRelativeMatchingTarget f n m :=
  (IsPullback.of_hasPullback
    (stratumObjectsToMatchingObjects Y n m)
    (stratumMatchingObjectsMap f n m)).isoIsPullback _ _
      (productRelativeMatching_isPullback f n m)

@[reassoc]
private theorem relativeStratumTargetIso_hom_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (relativeStratumTargetIso f n m).hom ≫ productRelativeMatchingFst f n m =
      pullback.fst (stratumObjectsToMatchingObjects Y n m)
        (stratumMatchingObjectsMap f n m) := by
  apply IsPullback.isoIsPullback_hom_fst

@[reassoc]
private theorem relativeStratumTargetIso_hom_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (relativeStratumTargetIso f n m).hom ≫ productRelativeMatchingSnd f n m =
      pullback.snd (stratumObjectsToMatchingObjects Y n m)
        (stratumMatchingObjectsMap f n m) := by
  apply IsPullback.isoIsPullback_hom_snd

private noncomputable def stratumObjectsToStandardIso
    (Z : CategoryTheory.SimplicialObject C) (n m : ℕ) :
    stratumObjects Z n m ≅
      (∏ᶜ fun _ : matchingIndexDegree n m => Z.obj (op ⦋m⦌)) :=
  (lim : (Discrete (matchingIndexDegree n m) ⥤ C) ⥤ C).mapIso
    (Discrete.natIso fun a => Z.mapIso (CategoryTheory.eqToIso (newSourceEq a.as)))

@[reassoc]
private theorem stratumObjectsToStandardIso_hom_π
    (Z : CategoryTheory.SimplicialObject C) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    (stratumObjectsToStandardIso Z n m).hom ≫
        Pi.π (fun _ : matchingIndexDegree n m => Z.obj (op ⦋m⦌)) a =
      Pi.π (fun a : matchingIndexDegree n m => Z.obj a.obj.obj.right) a ≫
        Z.map (eqToHom (newSourceEq a)) := by
  apply limit.map_π

private noncomputable def productRelativeMatchingMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    productRelativeMatchingSource f n m ⟶ productRelativeMatchingTarget f n m :=
  CategoryTheory.Limits.Pi.map fun _ =>
    CategoryTheory.SimplicialObject.relativeMatchingMap f m

@[reassoc]
private theorem productRelativeMatchingFst_π
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    productRelativeMatchingFst f n m ≫
        Pi.π (fun a : matchingIndexDegree n m => Y.obj a.obj.obj.right) a =
      Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a ≫
        relativeMatchingToStratumFst f a := by
  unfold productRelativeMatchingFst
  rw [Pi.map_π]

@[reassoc]
private theorem productRelativeMatchingSnd_π
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    productRelativeMatchingSnd f n m ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a =
      Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a ≫
        relativeMatchingToStratumSnd f a := by
  unfold productRelativeMatchingSnd
  rw [Pi.map_π]

@[reassoc]
private theorem productRelativeMatchingMap_π
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    productRelativeMatchingMap f n m ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a =
      Pi.π (fun _ : matchingIndexDegree n m => X.obj (op ⦋m⦌)) a ≫
        CategoryTheory.SimplicialObject.relativeMatchingMap f m := by
  unfold productRelativeMatchingMap
  rw [Pi.map_π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem sourceProductMap_π
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    ((stratumObjectsToStandardIso X n m).hom ≫ productRelativeMatchingMap f n m) ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a =
      Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
        X.map (eqToHom (newSourceEq a)) ≫
          CategoryTheory.SimplicialObject.relativeMatchingMap f m := by
  rw [Category.assoc, productRelativeMatchingMap_π,
    stratumObjectsToStandardIso_hom_π_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem targetIso_component_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    (((relativeStratumTargetIso f n m).hom ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
        pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
          ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) ≫
      Y.map (eqToHom (newSourceEq a).symm) =
    pullback.fst (stratumObjectsToMatchingObjects Y n m)
        (stratumMatchingObjectsMap f n m) ≫
      Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a := by
  calc
    (((relativeStratumTargetIso f n m).hom ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
        pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
          ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) ≫
      Y.map (eqToHom (newSourceEq a).symm) =
    (relativeStratumTargetIso f n m).hom ≫
      (Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a ≫
        relativeMatchingToStratumFst f a) := by
          unfold relativeMatchingToStratumFst
          simp only [Category.assoc]
    _ = (relativeStratumTargetIso f n m).hom ≫
        (productRelativeMatchingFst f n m ≫
          Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a) := by
            rw [productRelativeMatchingFst_π]
    _ = ((relativeStratumTargetIso f n m).hom ≫
          productRelativeMatchingFst f n m) ≫
        Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a := by
          simp only [Category.assoc]
    _ = pullback.fst (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) ≫
        Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a := by
          rw [relativeStratumTargetIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem targetIso_component_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (a : matchingIndexDegree n m) :
    ((relativeStratumTargetIso f n m).hom ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
      pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
        ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) =
    pullback.snd (stratumObjectsToMatchingObjects Y n m)
        (stratumMatchingObjectsMap f n m) ≫
      Pi.π (fun _ : matchingIndexDegree n m =>
        CategoryTheory.SimplicialObject.matchingObject X m) a := by
  calc
    ((relativeStratumTargetIso f n m).hom ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
      pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
        ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) =
    (relativeStratumTargetIso f n m).hom ≫
      (Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.relativeMatchingObject f m) a ≫
        relativeMatchingToStratumSnd f a) := by
          unfold relativeMatchingToStratumSnd
          simp only [Category.assoc]
    _ = (relativeStratumTargetIso f n m).hom ≫
        (productRelativeMatchingSnd f n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject X m) a) := by
              rw [productRelativeMatchingSnd_π]
    _ = ((relativeStratumTargetIso f n m).hom ≫
          productRelativeMatchingSnd f n m) ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a := by
            simp only [Category.assoc]
    _ = pullback.snd (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) ≫
        Pi.π (fun _ : matchingIndexDegree n m =>
          CategoryTheory.SimplicialObject.matchingObject X m) a := by
            rw [relativeStratumTargetIso_hom_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeStratumMap_arrow_comm
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (stratumObjectsToStandardIso X n m).hom ≫ productRelativeMatchingMap f n m =
      relativeStratumMap f n m ≫ (relativeStratumTargetIso f n m).hom := by
  apply Pi.hom_ext _ _
  intro a
  apply pullback.hom_ext
  · apply (cancel_mono (Y.map (eqToHom (newSourceEq a).symm))).1
    calc
      ((((stratumObjectsToStandardIso X n m).hom ≫
              productRelativeMatchingMap f n m) ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
          pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) ≫
        Y.map (eqToHom (newSourceEq a).symm) =
      ((Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a)) ≫
            CategoryTheory.SimplicialObject.relativeMatchingMap f m) ≫
          pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) ≫
        Y.map (eqToHom (newSourceEq a).symm) := by
          rw [sourceProductMap_π]
      _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a)) ≫ f.app (op ⦋m⦌) ≫
            Y.map (eqToHom (newSourceEq a).symm) := by
              simpa only [Category.assoc] using congrArg
                (fun t => (Pi.π (fun c : matchingIndexDegree n m =>
                    X.obj c.obj.obj.right) a ≫ X.map (eqToHom (newSourceEq a))) ≫
                  t ≫ Y.map (eqToHom (newSourceEq a).symm))
                (CategoryTheory.SimplicialObject.relativeMatchingMap_fst f m)
      _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          f.app a.obj.obj.right ≫ Y.map (eqToHom (newSourceEq a)) ≫
            Y.map (eqToHom (newSourceEq a).symm) := by
            have hn := f.naturality (eqToHom (newSourceEq a))
            simpa only [Category.assoc] using congrArg
              (fun t => Pi.π (fun c : matchingIndexDegree n m =>
                X.obj c.obj.obj.right) a ≫ t ≫
                  Y.map (eqToHom (newSourceEq a).symm)) hn
      _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          f.app a.obj.obj.right := by
            have hi : Y.map (eqToHom (newSourceEq a)) ≫
                Y.map (eqToHom (newSourceEq a).symm) = 𝟙 _ := by
              rw [← Y.map_comp, eqToHom_trans, eqToHom_refl, Y.map_id]
            simpa only [Category.assoc, Category.comp_id] using congrArg
              (fun t => (Pi.π (fun c : matchingIndexDegree n m =>
                X.obj c.obj.obj.right) a ≫ f.app a.obj.obj.right) ≫ t) hi
      _ = stratumObjectsMap f n m ≫
          Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a := by
            unfold stratumObjectsMap
            rw [Pi.map_π]
      _ = relativeStratumMap f n m ≫
          pullback.fst (stratumObjectsToMatchingObjects Y n m)
              (stratumMatchingObjectsMap f n m) ≫
            Pi.π (fun c : matchingIndexDegree n m => Y.obj c.obj.obj.right) a := by
              simpa only [Category.assoc] using
                (relativeStratumMap_fst_assoc f n m
                  (Pi.π (fun c : matchingIndexDegree n m =>
                    Y.obj c.obj.obj.right) a)).symm
      _ = (((relativeStratumMap f n m ≫
              (relativeStratumTargetIso f n m).hom) ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
          pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f)) ≫
        Y.map (eqToHom (newSourceEq a).symm) := by
          simpa only [Category.assoc] using congrArg
            (fun t => relativeStratumMap f n m ≫ t)
            (targetIso_component_fst f n m a).symm
  · calc
      (((stratumObjectsToStandardIso X n m).hom ≫
              productRelativeMatchingMap f n m) ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
          pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) =
      (Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a)) ≫
            CategoryTheory.SimplicialObject.relativeMatchingMap f m) ≫
          pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) := by
              rw [sourceProductMap_π]
      _ = Pi.π (fun c : matchingIndexDegree n m => X.obj c.obj.obj.right) a ≫
          X.map (eqToHom (newSourceEq a)) ≫
            CategoryTheory.SimplicialObject.matchingMap X m := by
              simpa only [Category.assoc] using congrArg
                (fun t => (Pi.π (fun c : matchingIndexDegree n m =>
                  X.obj c.obj.obj.right) a ≫ X.map (eqToHom (newSourceEq a))) ≫ t)
                (CategoryTheory.SimplicialObject.relativeMatchingMap_snd f m)
      _ = stratumObjectsToMatchingObjects X n m ≫
          Pi.π (fun _ : matchingIndexDegree n m =>
            CategoryTheory.SimplicialObject.matchingObject X m) a := by
              exact (stratumObjectsToMatchingObjects_π X n m a).symm
      _ = relativeStratumMap f n m ≫
          pullback.snd (stratumObjectsToMatchingObjects Y n m)
              (stratumMatchingObjectsMap f n m) ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.matchingObject X m) a := by
                simpa only [Category.assoc] using
                  (relativeStratumMap_snd_assoc f n m
                    (Pi.π (fun _ : matchingIndexDegree n m =>
                      CategoryTheory.SimplicialObject.matchingObject X m) a)).symm
      _ = ((relativeStratumMap f n m ≫
              (relativeStratumTargetIso f n m).hom) ≫
            Pi.π (fun _ : matchingIndexDegree n m =>
              CategoryTheory.SimplicialObject.relativeMatchingObject f m) a) ≫
          pullback.snd (CategoryTheory.SimplicialObject.matchingMap Y m)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor m).map f) := by
              simpa only [Category.assoc] using congrArg
                (fun t => relativeStratumMap f n m ≫ t)
                (targetIso_component_snd f n m a).symm

private noncomputable def relativeStratumMapArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    Arrow.mk (relativeStratumMap f n m) ≅
      Arrow.mk (productRelativeMatchingMap f n m) :=
  Arrow.isoMk (stratumObjectsToStandardIso X n m)
    (relativeStratumTargetIso f n m)
    (relativeStratumMap_arrow_comm f n m)

/-- `T = A_X ×_{C_Y} B_Y`, the intermediate successor matching object. -/
private noncomputable abbrev matchingIntermediate
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) : C :=
  pullback
    (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
    (stratumObjectsToMatchingObjects Y n m)

private theorem attachmentFirstMap_compat
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m) =
      (pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m) ≫
        stratumObjectsToMatchingObjects Y n m := by
  calc
    pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m) =
      (pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        oldToStratumMatchingObjects X n m) ≫ stratumMatchingObjectsMap f n m := by
          simp only [Category.assoc]
    _ = (pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫
        stratumObjectsToMatchingObjects X n m) ≫ stratumMatchingObjectsMap f n m := by
          rw [pullback.condition]
    _ = pullback.snd (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) ≫
          (stratumObjectsToMatchingObjects X n m ≫
            stratumMatchingObjectsMap f n m) := by simp only [Category.assoc]
    _ = pullback.snd (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) ≫
          (stratumObjectsMap f n m ≫
            stratumObjectsToMatchingObjects Y n m) := by
              rw [stratumObjectsToMatchingObjects_naturality]
    _ = (pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m) ≫
        stratumObjectsToMatchingObjects Y n m := by simp only [Category.assoc]

/-- The first factor from the source attachment into `T`. -/
private noncomputable def attachmentFirstMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingAttachment X n m ⟶ matchingIntermediate f n m :=
  pullback.lift
    (pullback.fst (oldToStratumMatchingObjects X n m)
      (stratumObjectsToMatchingObjects X n m))
    (pullback.snd (oldToStratumMatchingObjects X n m)
      (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m)
    (attachmentFirstMap_compat f n m)

@[reassoc]
private theorem attachmentFirstMap_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫
        pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.fst (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m) := by
  apply pullback.lift_fst

@[reassoc]
private theorem attachmentFirstMap_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫
        pullback.snd
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m := by
  apply pullback.lift_snd

private theorem attachmentSecondMap_compat
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    (pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫ filteredMatchingMap f n m) ≫
        oldToStratumMatchingObjects Y n m =
      pullback.snd
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫
        stratumObjectsToMatchingObjects Y n m := by
  calc
    (pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫ filteredMatchingMap f n m) ≫
        oldToStratumMatchingObjects Y n m =
      pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫
        (filteredMatchingMap f n m ≫ oldToStratumMatchingObjects Y n m) := by
          simp only [Category.assoc]
    _ = pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m) := by
          rw [oldToStratumMatchingObjects_naturality]
    _ = pullback.snd
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫
        stratumObjectsToMatchingObjects Y n m := pullback.condition

/-- The second factor from `T` into the target attachment. -/
private noncomputable def attachmentSecondMap
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingIntermediate f n m ⟶ matchingAttachment Y n m :=
  pullback.lift
    (pullback.fst
      (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
      (stratumObjectsToMatchingObjects Y n m) ≫ filteredMatchingMap f n m)
    (pullback.snd
      (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
      (stratumObjectsToMatchingObjects Y n m))
    (attachmentSecondMap_compat f n m)

@[reassoc]
private theorem attachmentSecondMap_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentSecondMap f n m ≫
        pullback.fst (oldToStratumMatchingObjects Y n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫ filteredMatchingMap f n m := by
  apply pullback.lift_fst

@[reassoc]
private theorem attachmentSecondMap_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentSecondMap f n m ≫
        pullback.snd (oldToStratumMatchingObjects Y n m)
          (stratumObjectsToMatchingObjects Y n m) =
      pullback.snd
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
        (stratumObjectsToMatchingObjects Y n m) := by
  apply pullback.lift_snd

private theorem attachmentMap_factorization
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫ attachmentSecondMap f n m =
      matchingAttachmentMap f n m := by
  apply pullback.hom_ext
  · calc
      (attachmentFirstMap f n m ≫ attachmentSecondMap f n m) ≫
            pullback.fst (oldToStratumMatchingObjects Y n m)
              (stratumObjectsToMatchingObjects Y n m) =
          attachmentFirstMap f n m ≫
            (pullback.fst
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) ≫
              filteredMatchingMap f n m) := by
                rw [Category.assoc, attachmentSecondMap_fst]
      _ = pullback.fst (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          filteredMatchingMap f n m := by
            rw [attachmentFirstMap_fst_assoc]
      _ = matchingAttachmentMap f n m ≫
          pullback.fst (oldToStratumMatchingObjects Y n m)
            (stratumObjectsToMatchingObjects Y n m) :=
        (matchingAttachmentMap_fst f n m).symm
  · calc
      (attachmentFirstMap f n m ≫ attachmentSecondMap f n m) ≫
            pullback.snd (oldToStratumMatchingObjects Y n m)
              (stratumObjectsToMatchingObjects Y n m) =
          attachmentFirstMap f n m ≫
            pullback.snd
              (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
              (stratumObjectsToMatchingObjects Y n m) := by
                rw [Category.assoc, attachmentSecondMap_snd]
      _ = pullback.snd (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m := by
              rw [attachmentFirstMap_snd]
      _ = matchingAttachmentMap f n m ≫
          pullback.snd (oldToStratumMatchingObjects Y n m)
            (stratumObjectsToMatchingObjects Y n m) :=
        (matchingAttachmentMap_snd f n m).symm

private noncomputable def intermediateToRelativeTarget
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    matchingIntermediate f n m ⟶ relativeStratumTarget f n m :=
  pullback.lift
    (pullback.snd
      (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
      (stratumObjectsToMatchingObjects Y n m))
    (pullback.fst
      (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
      (stratumObjectsToMatchingObjects Y n m) ≫ oldToStratumMatchingObjects X n m)
    (by
      rw [Category.assoc, pullback.condition])

@[reassoc]
private theorem intermediateToRelativeTarget_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    intermediateToRelativeTarget f n m ≫
        pullback.fst (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) =
      pullback.snd
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
        (stratumObjectsToMatchingObjects Y n m) := by
  apply pullback.lift_fst

@[reassoc]
private theorem intermediateToRelativeTarget_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    intermediateToRelativeTarget f n m ≫
        pullback.snd (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m) =
      pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) ≫
        oldToStratumMatchingObjects X n m := by
  apply pullback.lift_snd

private theorem attachmentFirstSquare_comm
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    attachmentFirstMap f n m ≫ intermediateToRelativeTarget f n m =
      pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) ≫ relativeStratumMap f n m := by
  apply pullback.hom_ext
  · rw [Category.assoc, intermediateToRelativeTarget_fst,
      attachmentFirstMap_snd, Category.assoc, relativeStratumMap_fst]
  · calc
      (attachmentFirstMap f n m ≫ intermediateToRelativeTarget f n m) ≫
            pullback.snd (stratumObjectsToMatchingObjects Y n m)
              (stratumMatchingObjectsMap f n m) =
          attachmentFirstMap f n m ≫
            (pullback.fst
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) ≫
              oldToStratumMatchingObjects X n m) := by
                rw [Category.assoc, intermediateToRelativeTarget_snd]
      _ = pullback.fst (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          oldToStratumMatchingObjects X n m := by
            rw [attachmentFirstMap_fst_assoc]
      _ = pullback.snd (oldToStratumMatchingObjects X n m)
            (stratumObjectsToMatchingObjects X n m) ≫
          stratumObjectsToMatchingObjects X n m := pullback.condition
      _ = (pullback.snd (oldToStratumMatchingObjects X n m)
              (stratumObjectsToMatchingObjects X n m) ≫ relativeStratumMap f n m) ≫
            pullback.snd (stratumObjectsToMatchingObjects Y n m)
              (stratumMatchingObjectsMap f n m) := by
                rw [Category.assoc, relativeStratumMap_snd]

private noncomputable def attachmentFirstSquareLift
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone (intermediateToRelativeTarget f n m)
      (relativeStratumMap f n m)) :
    s.pt ⟶ matchingAttachment X n m :=
  pullback.lift
    (s.fst ≫ pullback.fst
      (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
      (stratumObjectsToMatchingObjects Y n m))
    s.snd
    (by
      have hc := congrArg (fun t => t ≫
        pullback.snd (stratumObjectsToMatchingObjects Y n m)
          (stratumMatchingObjectsMap f n m)) s.condition
      simpa only [Category.assoc, intermediateToRelativeTarget_snd,
        relativeStratumMap_snd] using hc)

@[reassoc]
private theorem attachmentFirstSquareLift_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone (intermediateToRelativeTarget f n m)
      (relativeStratumMap f n m)) :
    attachmentFirstSquareLift f n m s ≫
        pullback.snd (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) = s.snd := by
  apply pullback.lift_snd

@[reassoc]
private theorem attachmentFirstSquareLift_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone (intermediateToRelativeTarget f n m)
      (relativeStratumMap f n m)) :
    attachmentFirstSquareLift f n m s ≫
        pullback.fst (oldToStratumMatchingObjects X n m)
          (stratumObjectsToMatchingObjects X n m) =
      s.fst ≫ pullback.fst
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
        (stratumObjectsToMatchingObjects Y n m) := by
  apply pullback.lift_fst

private theorem attachmentFirstSquareLift_first
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone (intermediateToRelativeTarget f n m)
      (relativeStratumMap f n m)) :
    attachmentFirstSquareLift f n m s ≫ attachmentFirstMap f n m = s.fst := by
  apply pullback.hom_ext
  · rw [Category.assoc, attachmentFirstMap_fst, attachmentFirstSquareLift_fst]
  · calc
      (attachmentFirstSquareLift f n m s ≫ attachmentFirstMap f n m) ≫
            pullback.snd
              (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
              (stratumObjectsToMatchingObjects Y n m) =
          attachmentFirstSquareLift f n m s ≫
            (pullback.snd (oldToStratumMatchingObjects X n m)
              (stratumObjectsToMatchingObjects X n m) ≫ stratumObjectsMap f n m) := by
                rw [Category.assoc, attachmentFirstMap_snd]
      _ = s.snd ≫ stratumObjectsMap f n m := by
            rw [attachmentFirstSquareLift_snd_assoc]
      _ = s.fst ≫
          pullback.snd
            (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
            (stratumObjectsToMatchingObjects Y n m) := by
        have hc := congrArg (fun t => t ≫
          pullback.fst (stratumObjectsToMatchingObjects Y n m)
            (stratumMatchingObjectsMap f n m)) s.condition
        simpa only [Category.assoc, intermediateToRelativeTarget_fst,
          relativeStratumMap_fst] using hc.symm

/-- The first factor is the base change of the finite-stratum relative matching map. -/
private theorem attachmentFirstMap_isPullback
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPullback
      (attachmentFirstMap f n m)
      (pullback.snd (oldToStratumMatchingObjects X n m)
        (stratumObjectsToMatchingObjects X n m))
      (intermediateToRelativeTarget f n m)
      (relativeStratumMap f n m) where
  w := attachmentFirstSquare_comm f n m
  isLimit' := ⟨PullbackCone.IsLimit.mk (attachmentFirstSquare_comm f n m)
    (fun s => attachmentFirstSquareLift f n m s)
    (fun s => attachmentFirstSquareLift_first f n m s)
    (fun s => attachmentFirstSquareLift_snd f n m s)
    (fun s k hk₁ hk₂ => by
      apply pullback.hom_ext
      · calc
          k ≫ pullback.fst (oldToStratumMatchingObjects X n m)
                (stratumObjectsToMatchingObjects X n m) =
              k ≫ (attachmentFirstMap f n m ≫
                pullback.fst
                  (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                  (stratumObjectsToMatchingObjects Y n m)) := by
                    rw [attachmentFirstMap_fst]
          _ = (k ≫ attachmentFirstMap f n m) ≫
              pullback.fst
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) := by
                  simp only [Category.assoc]
          _ = s.fst ≫ pullback.fst
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) := by rw [hk₁]
          _ = attachmentFirstSquareLift f n m s ≫
              pullback.fst (oldToStratumMatchingObjects X n m)
                (stratumObjectsToMatchingObjects X n m) :=
            (attachmentFirstSquareLift_fst f n m s).symm
      · exact hk₂.trans (attachmentFirstSquareLift_snd f n m s).symm)⟩

private noncomputable def attachmentSecondSquareLift
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone
      (pullback.fst (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m))
      (filteredMatchingMap f n m)) :
    s.pt ⟶ matchingIntermediate f n m :=
  pullback.lift s.snd
    (s.fst ≫ pullback.snd (oldToStratumMatchingObjects Y n m)
      (stratumObjectsToMatchingObjects Y n m))
    (by
      have hc := congrArg (fun t => t ≫ oldToStratumMatchingObjects Y n m) s.condition
      calc
        s.snd ≫
              (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m) =
            s.snd ≫
              (filteredMatchingMap f n m ≫ oldToStratumMatchingObjects Y n m) := by
                rw [oldToStratumMatchingObjects_naturality]
        _ = s.fst ≫
            (pullback.fst (oldToStratumMatchingObjects Y n m)
                (stratumObjectsToMatchingObjects Y n m) ≫
              oldToStratumMatchingObjects Y n m) := by
                simpa only [Category.assoc] using hc.symm
        _ = s.fst ≫
            (pullback.snd (oldToStratumMatchingObjects Y n m)
                (stratumObjectsToMatchingObjects Y n m) ≫
              stratumObjectsToMatchingObjects Y n m) := by
                rw [pullback.condition]
        _ = (s.fst ≫ pullback.snd (oldToStratumMatchingObjects Y n m)
              (stratumObjectsToMatchingObjects Y n m)) ≫
            stratumObjectsToMatchingObjects Y n m := by simp only [Category.assoc])

@[reassoc]
private theorem attachmentSecondSquareLift_fst
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone
      (pullback.fst (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m))
      (filteredMatchingMap f n m)) :
    attachmentSecondSquareLift f n m s ≫
        pullback.fst
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) = s.snd := by
  apply pullback.lift_fst

@[reassoc]
private theorem attachmentSecondSquareLift_snd
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone
      (pullback.fst (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m))
      (filteredMatchingMap f n m)) :
    attachmentSecondSquareLift f n m s ≫
        pullback.snd
          (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
          (stratumObjectsToMatchingObjects Y n m) =
      s.fst ≫ pullback.snd (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m) := by
  apply pullback.lift_snd

private theorem attachmentSecondSquareLift_second
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (s : PullbackCone
      (pullback.fst (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m))
      (filteredMatchingMap f n m)) :
    attachmentSecondSquareLift f n m s ≫ attachmentSecondMap f n m = s.fst := by
  apply pullback.hom_ext
  · calc
      (attachmentSecondSquareLift f n m s ≫ attachmentSecondMap f n m) ≫
            pullback.fst (oldToStratumMatchingObjects Y n m)
              (stratumObjectsToMatchingObjects Y n m) =
          attachmentSecondSquareLift f n m s ≫
            (pullback.fst
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) ≫
              filteredMatchingMap f n m) := by
                rw [Category.assoc, attachmentSecondMap_fst]
      _ = s.snd ≫ filteredMatchingMap f n m := by
            rw [attachmentSecondSquareLift_fst_assoc]
      _ = s.fst ≫ pullback.fst (oldToStratumMatchingObjects Y n m)
            (stratumObjectsToMatchingObjects Y n m) := s.condition.symm
  · rw [Category.assoc, attachmentSecondMap_snd,
      attachmentSecondSquareLift_snd]

/-- The second factor is a base change of the preceding filtered matching map. -/
private theorem attachmentSecondMap_isPullback
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    IsPullback
      (attachmentSecondMap f n m)
      (pullback.fst
        (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
        (stratumObjectsToMatchingObjects Y n m))
      (pullback.fst (oldToStratumMatchingObjects Y n m)
        (stratumObjectsToMatchingObjects Y n m))
      (filteredMatchingMap f n m) where
  w := attachmentSecondMap_fst f n m
  isLimit' := ⟨PullbackCone.IsLimit.mk (attachmentSecondMap_fst f n m)
    (fun s => attachmentSecondSquareLift f n m s)
    (fun s => attachmentSecondSquareLift_second f n m s)
    (fun s => attachmentSecondSquareLift_fst f n m s)
    (fun s k hk₁ hk₂ => by
      apply pullback.hom_ext
      · exact hk₂.trans (attachmentSecondSquareLift_fst f n m s).symm
      · calc
          k ≫ pullback.snd
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) =
              k ≫ (attachmentSecondMap f n m ≫
                pullback.snd (oldToStratumMatchingObjects Y n m)
                  (stratumObjectsToMatchingObjects Y n m)) := by
                    rw [attachmentSecondMap_snd]
          _ = (k ≫ attachmentSecondMap f n m) ≫
              pullback.snd (oldToStratumMatchingObjects Y n m)
                (stratumObjectsToMatchingObjects Y n m) := by simp only [Category.assoc]
          _ = s.fst ≫ pullback.snd (oldToStratumMatchingObjects Y n m)
                (stratumObjectsToMatchingObjects Y n m) := by rw [hk₁]
          _ = attachmentSecondSquareLift f n m s ≫
              pullback.snd
                (oldToStratumMatchingObjects X n m ≫ stratumMatchingObjectsMap f n m)
                (stratumObjectsToMatchingObjects Y n m) :=
            (attachmentSecondSquareLift_snd f n m s).symm)⟩

private theorem productRelativeMatchingMap_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f m)) :
    HomotopicalAlgebra.trivialFibrations C (productRelativeMatchingMap f n m) := by
  unfold productRelativeMatchingMap CategoryTheory.Limits.Pi.map
  apply (HomotopicalAlgebra.trivialFibrations C).limMap
  intro a
  exact h

private theorem relativeStratumMap_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f m)) :
    HomotopicalAlgebra.trivialFibrations C (relativeStratumMap f n m) := by
  exact ((HomotopicalAlgebra.trivialFibrations C).arrow_mk_iso_iff
    (relativeStratumMapArrowIso f n m)).2
      (productRelativeMatchingMap_trivialFibration f n m h)

private theorem attachmentFirstMap_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f m)) :
    HomotopicalAlgebra.trivialFibrations C (attachmentFirstMap f n m) := by
  exact (HomotopicalAlgebra.trivialFibrations C).of_isPullback
    (attachmentFirstMap_isPullback f n m).flip
      (relativeStratumMap_trivialFibration f n m h)

private theorem attachmentSecondMap_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (h : HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n m)) :
    HomotopicalAlgebra.trivialFibrations C (attachmentSecondMap f n m) := by
  exact (HomotopicalAlgebra.trivialFibrations C).of_isPullback
    (attachmentSecondMap_isPullback f n m).flip h

private theorem matchingAttachmentMap_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (hstage : HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n m))
    (hrelative : HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f m)) :
    HomotopicalAlgebra.trivialFibrations C (matchingAttachmentMap f n m) := by
  rw [← attachmentMap_factorization f n m]
  exact (HomotopicalAlgebra.trivialFibrations C).comp_mem _ _
    (attachmentFirstMap_trivialFibration f n m hrelative)
    (attachmentSecondMap_trivialFibration f n m hstage)

private noncomputable def filteredMatchingMapSuccessorArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ) :
    Arrow.mk (matchingAttachmentMap f n m) ≅
      Arrow.mk (filteredMatchingMap f n (m + 1)) :=
  Arrow.isoMk (standardMatchingAttachmentIso X n m)
    (standardMatchingAttachmentIso Y n m)
    (standardMatchingAttachmentIso_naturality f n m)

private theorem filteredMatchingMap_succ_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n m : ℕ)
    (hstage : HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n m))
    (hrelative : HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f m)) :
    HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n (m + 1)) := by
  exact ((HomotopicalAlgebra.trivialFibrations C).arrow_mk_iso_iff
    (filteredMatchingMapSuccessorArrowIso f n m)).1
      (matchingAttachmentMap_trivialFibration f n m hstage hrelative)

private def filteredZeroCone (X : CategoryTheory.SimplicialObject C)
    (n : ℕ) (Z : C) : Cone (filteredMatchingDiagram X n 0) where
  pt := Z
  π :=
    { app := fun a => isEmptyElim a
      naturality := by
        intro a
        exact isEmptyElim a }

private noncomputable def filteredZeroIsTerminal
    (X : CategoryTheory.SimplicialObject C) (n : ℕ) :
    IsTerminal (filteredMatchingObject X n 0) :=
  IsTerminal.ofUniqueHom
    (fun Z => limit.lift (filteredMatchingDiagram X n 0) (filteredZeroCone X n Z))
    (fun _ _ => by
      apply limit.hom_ext
      intro a
      exact isEmptyElim a)

private noncomputable def filteredZeroObjectIso
    (X Y : CategoryTheory.SimplicialObject C) (n : ℕ) :
    filteredMatchingObject X n 0 ≅ filteredMatchingObject Y n 0 :=
  (filteredZeroIsTerminal X n).uniqueUpToIso (filteredZeroIsTerminal Y n)

private theorem filteredMatchingMap_zero_eq_iso_hom
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    filteredMatchingMap f n 0 = (filteredZeroObjectIso X Y n).hom :=
  (filteredZeroIsTerminal Y n).hom_ext _ _

private instance filteredMatchingMap_zero_isIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    IsIso (filteredMatchingMap f n 0) := by
  rw [filteredMatchingMap_zero_eq_iso_hom]
  infer_instance

private theorem filteredMatchingMap_zero_trivialFibration
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n 0) := by
  exact (HomotopicalAlgebra.trivialFibrations C).of_isIso _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem filteredTotalObjectIso_hom_π
    (Z : CategoryTheory.SimplicialObject C) (n : ℕ)
    (a : CategoryTheory.SimplicialObject.matchingIndex n) :
    (filteredTotalObjectIso Z n).hom ≫
        CategoryTheory.SimplicialObject.matchingπ Z n a =
      limit.π (filteredMatchingDiagram Z n n) ((belowTotalInverse n).obj a) := by
  unfold filteredTotalObjectIso CategoryTheory.SimplicialObject.matchingπ
  rw [HasLimit.isoOfEquivalence_hom_π]
  simp [belowTotalEquivalence]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredTotalObjectIso_naturality
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    (filteredTotalObjectIso X n).hom ≫
        (CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f =
      filteredMatchingMap f n n ≫ (filteredTotalObjectIso Y n).hom := by
  apply limit.hom_ext
  intro a
  calc
    ((filteredTotalObjectIso X n).hom ≫
          (CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f) ≫
        CategoryTheory.SimplicialObject.matchingπ Y n a =
      (filteredTotalObjectIso X n).hom ≫
        (CategoryTheory.SimplicialObject.matchingπ X n a ≫ f.app a.obj.right) := by
          rw [Category.assoc,
            CategoryTheory.SimplicialObject.matchingObjectFunctor_map_π]
    _ = limit.π (filteredMatchingDiagram X n n) ((belowTotalInverse n).obj a) ≫
        f.app a.obj.right := by
          simpa only [Category.assoc] using
            filteredTotalObjectIso_hom_π_assoc X n a (f.app a.obj.right)
    _ = filteredMatchingMap f n n ≫
        limit.π (filteredMatchingDiagram Y n n) ((belowTotalInverse n).obj a) := by
          have hmap := filteredMatchingMap_π f n n ((belowTotalInverse n).obj a)
          change filteredMatchingMap f n n ≫
              limit.π (filteredMatchingDiagram Y n n) ((belowTotalInverse n).obj a) =
            limit.π (filteredMatchingDiagram X n n) ((belowTotalInverse n).obj a) ≫
              f.app a.obj.right at hmap
          exact hmap.symm
    _ = filteredMatchingMap f n n ≫
        ((filteredTotalObjectIso Y n).hom ≫
          CategoryTheory.SimplicialObject.matchingπ Y n a) := by
            rw [filteredTotalObjectIso_hom_π]
    _ = (filteredMatchingMap f n n ≫ (filteredTotalObjectIso Y n).hom) ≫
        CategoryTheory.SimplicialObject.matchingπ Y n a := by
          simp only [Category.assoc]

private noncomputable def filteredTotalMapArrowIso
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (filteredMatchingMap f n n) ≅
      Arrow.mk ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f) :=
  Arrow.isoMk (filteredTotalObjectIso X n) (filteredTotalObjectIso Y n)
    (filteredTotalObjectIso_naturality f n)

private theorem filteredMatchingMap_trivialFibration_of_lower
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (n m : ℕ) (hm : m ≤ n)
    (hlower : ∀ k < m, HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f k)) :
    HomotopicalAlgebra.trivialFibrations C (filteredMatchingMap f n m) := by
  induction m with
  | zero => exact filteredMatchingMap_zero_trivialFibration f n
  | succ m ih =>
      apply filteredMatchingMap_succ_trivialFibration f n m
      · exact ih (Nat.le_trans (Nat.le_succ m) hm)
          (fun k hk => hlower k (Nat.lt_trans hk (Nat.lt_succ_self m)))
      · exact hlower m (Nat.lt_succ_self m)

/-- If all lower relative matching maps are trivial fibrations, then the
degree-`n` matching-object comparison is a trivial fibration. -/
private theorem matchingObjectMap_trivialFibration_of_lower
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
    (hlower : ∀ k < n, HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f k)) :
    HomotopicalAlgebra.trivialFibrations C
      ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f) := by
  exact ((HomotopicalAlgebra.trivialFibrations C).arrow_mk_iso_iff
    (filteredTotalMapArrowIso f n)).1
      (filteredMatchingMap_trivialFibration_of_lower f n n (Nat.le_refl n) hlower)

/-- Every component of a Reedy right map in the base trivial-fibration class is trivial. -/
theorem component_trivialFibration_of_reedyRight_trivial
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (h : CategoryTheory.SimplicialObject.reedyRight
      (HomotopicalAlgebra.trivialFibrations C) f) (n : ℕ) :
    HomotopicalAlgebra.trivialFibrations C (f.app (op ⦋n⦌)) := by
  have hM := matchingObjectMap_trivialFibration_of_lower f n
    (fun k _ => h k)
  have hfst : HomotopicalAlgebra.trivialFibrations C
      (pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y n)
        ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)) :=
    (HomotopicalAlgebra.trivialFibrations C).of_isPullback
      (IsPullback.of_hasPullback
        (CategoryTheory.SimplicialObject.matchingMap Y n)
        ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)).flip hM
  have hcomp := (HomotopicalAlgebra.trivialFibrations C).comp_mem _ _ (h n) hfst
  rw [CategoryTheory.SimplicialObject.relativeMatchingMap_fst] at hcomp
  exact hcomp

private theorem pointwiseWeakEquivalence_of_reedyRight_trivial
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (h : CategoryTheory.SimplicialObject.reedyRight
      (HomotopicalAlgebra.trivialFibrations C) f) :
    (HomotopicalAlgebra.weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ f := by
  intro Δ
  let n := Δ.unop.len
  have hn : HomotopicalAlgebra.weakEquivalences C (f.app (op ⦋n⦌)) :=
    HomotopicalAlgebra.trivialFibrations_sub_weakEquivalences C _
      (component_trivialFibration_of_reedyRight_trivial f h n)
  have hΔ : op ⦋n⦌ = Δ := congrArg op (SimplexCategory.mk_len Δ.unop)
  cases hΔ
  exact hn

private theorem relativeMatchingMap_trivialFibration_of_reedyRight_fib_pointwiseWeak
    {X Y : CategoryTheory.SimplicialObject C} (f : X ⟶ Y)
    (hfib : CategoryTheory.SimplicialObject.reedyRight
      (HomotopicalAlgebra.fibrations C) f)
    (hweak : (HomotopicalAlgebra.weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ f) :
    ∀ n : ℕ, HomotopicalAlgebra.trivialFibrations C
      (CategoryTheory.SimplicialObject.relativeMatchingMap f n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      have hM := matchingObjectMap_trivialFibration_of_lower f n
        (fun k hk => ih k hk)
      have hfst : HomotopicalAlgebra.trivialFibrations C
          (pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y n)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)) :=
        (HomotopicalAlgebra.trivialFibrations C).of_isPullback
          (IsPullback.of_hasPullback
            (CategoryTheory.SimplicialObject.matchingMap Y n)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)).flip hM
      have hfstWeak : HomotopicalAlgebra.weakEquivalences C
          (pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y n)
            ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)) :=
        HomotopicalAlgebra.trivialFibrations_sub_weakEquivalences C _ hfst
      have hcompWeak : HomotopicalAlgebra.weakEquivalences C
          (CategoryTheory.SimplicialObject.relativeMatchingMap f n ≫
            pullback.fst (CategoryTheory.SimplicialObject.matchingMap Y n)
              ((CategoryTheory.SimplicialObject.matchingObjectFunctor n).map f)) := by
        rw [CategoryTheory.SimplicialObject.relativeMatchingMap_fst]
        exact hweak (op ⦋n⦌)
      have hrelativeWeak : HomotopicalAlgebra.weakEquivalences C
          (CategoryTheory.SimplicialObject.relativeMatchingMap f n) :=
        (HomotopicalAlgebra.weakEquivalences C).of_postcomp _ _ hfstWeak hcompWeak
      exact ⟨hfib n, hrelativeWeak⟩

/-- In a model category, Reedy trivial fibrations are exactly Reedy
fibrations that are pointwise weak equivalences. -/
private theorem reedyRight_trivialFibrations_eq_internal :
    CategoryTheory.SimplicialObject.reedyRight
        (HomotopicalAlgebra.trivialFibrations C) =
      CategoryTheory.SimplicialObject.reedyRight
          (HomotopicalAlgebra.fibrations C) ⊓
        (HomotopicalAlgebra.weakEquivalences C).functorCategory
          SimplexCategoryᵒᵖ := by
  apply le_antisymm
  · intro X Y f h
    exact ⟨fun n =>
      HomotopicalAlgebra.trivialFibrations_sub_fibrations C _ (h n),
      pointwiseWeakEquivalence_of_reedyRight_trivial f h⟩
  · intro X Y f h
    exact relativeMatchingMap_trivialFibration_of_reedyRight_fib_pointwiseWeak
      f h.1 h.2



end FilteredLimits

end ReedyTrivialClassesMatching

universe v u

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Reedy trivial cofibrations are the Reedy cofibrations that are pointwise weak equivalences. -/
theorem reedyLeft_trivialCofibrations_eq :
    reedyLeft (trivialCofibrations C) =
      reedyLeft (cofibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ :=
  ReedyTrivialClassesLatching.reedyLeft_trivialCofibrations_eq_internal

/-- Reedy trivial fibrations are the Reedy fibrations that are pointwise weak equivalences. -/
theorem reedyRight_trivialFibrations_eq :
    reedyRight (trivialFibrations C) =
      reedyRight (fibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ :=
  ReedyTrivialClassesMatching.reedyRight_trivialFibrations_eq_internal

end CategoryTheory.SimplicialObject
