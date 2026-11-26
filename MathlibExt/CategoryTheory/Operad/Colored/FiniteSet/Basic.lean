/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.Types

/-!
# Type-valued colored operads

Elementwise accessors for colored operads valued in `Type`, using the canonical dependent-product
finite tensor. This includes simultaneous substitution, its naturality, and the unrestricted
three-level associativity law, including empty input families.
-/

@[expose] public section

namespace CategoryTheory.Operad
open CategoryTheory
universe u v

/-- A colored operad valued in types, with independent universes for colors and operations. -/
abbrev ColoredSetOperad (Color : Type u) := ColoredOperadObj Color (Type v)

namespace ColoredSetOperad

variable {Color : Type u}

/-- The unique element of the empty finite tensor in `Type`. -/
def emptyTensorElement : operadUnitSource (V := Type v) :=
  fun e ↦ e.elim

/-- The operadic unit at a color, evaluated on the unique empty tensor element. -/
def unitElement (O : ColoredSetOperad Color) (c : Color) :
    O.toCollection.obj (ColoredSubstitutionData.unitProfile c) :=
  O.unit c emptyTensorElement

/-- Units are preserved along unit-profile maps, evaluated at an
element: the elementwise corollary of the general morphism equality
`ColoredOperadObj.map_unitProfileMap_unit`, using uniqueness of the
empty tensor element. Shared by the free-operad bridge and the
tree-isomorphism degeneracy naturality proof. -/
theorem map_unitProfileMap_unit (O : ColoredSetOperad Color)
    {c c' : Color} (f : ColoredSubstitutionData.unitProfile c ⟶
      ColoredSubstitutionData.unitProfile c') (e : operadUnitSource (V := Type v)) :
    O.toCollection.map f (O.unit c e) =
      O.unit c' emptyTensorElement := by
  have h := ColoredOperadObj.map_unitProfileMap_unit O f
  have he : e = emptyTensorElement := by
    funext i
    exact i.elim
  subst he
  have h1 := congrArg (fun k ↦ k emptyTensorElement) h
  with_unfolding_all exact h1

private theorem rightFactorHom_none (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) :
    (ColoredOperadObj.UnitInsertion.rightFactorHom O unit P).hom
        (none : Option P.inputs) =
      FiniteFamily.typeTensorSingletonIso.hom.app (O.obj P) := by
  change FiniteFamily.typeTensorSingletonIso.hom.app (O.obj P) ≫
      O.map (ColoredSubstitutionData.rightUnitOuterHom P) = _
  rw [ColoredSubstitutionData.rightUnitOuterHom_eq_id]
  exact (congrArg (fun k ↦ FiniteFamily.typeTensorSingletonIso.hom.app (O.obj P) ≫ k)
    (O.map_id P)).trans (Category.comp_id _)

private theorem leftFactorHom_none (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) :
    (ColoredOperadObj.UnitInsertion.leftFactorHom O unit P).hom
        (none : Option PUnit) = unit P.outputColor := by
  change unit P.outputColor ≫ O.map (ColoredSubstitutionData.leftUnitOuterHom P) = _
  rw [ColoredSubstitutionData.leftUnitOuterHom_eq_id]
  exact (congrArg (fun k ↦ unit P.outputColor ≫ k)
    (O.map_id (ColoredSubstitutionData.unitProfile P.outputColor))).trans (Category.comp_id _)

/-- In `Type`, right-unit insertion leaves the outer operation unchanged. -/
theorem rightUnitInsert_apply_none (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) (x : O.obj P) :
    ColoredOperadObj.rightUnitInsert O unit P x none = x := by
  let f := ColoredOperadObj.UnitInsertion.rightFactorHom O unit P
  let j : (ColoredOperadObj.UnitInsertion.rightTensorFamily O P).index := none
  let a : FiniteFamily.typeTensorObj (FiniteFamily.singleton.obj (O.obj P)) :=
    (FiniteFamily.typeTensorSingletonEquiv (O.obj P)).symm x
  let b : FiniteFamily.typeTensorObj
      (FiniteFamily.flatten.obj (UnitInsertion.rightNestedFamily (O.obj P) P.inputs)) :=
    FiniteFamily.typeTensorMap (UnitInsertion.rightSingletonToFlatten (O.obj P) P.inputs) a
  let t : FiniteFamily.typeTensorObj (ColoredOperadObj.UnitInsertion.rightTensorFamily O P) :=
    FiniteFamily.typeTensorFlattenEquiv
      (UnitInsertion.rightNestedFamily (O.obj P) P.inputs) b
  have hEq : ColoredOperadObj.rightUnitInsert O unit P =
      FiniteFamily.typeTensorSingletonIso.inv.app (O.obj P) ≫
      FiniteFamily.typeTensor.map (UnitInsertion.rightSingletonToFlatten (O.obj P) P.inputs) ≫
      FiniteFamily.typeTensorFlattenIso.hom.app
        (UnitInsertion.rightNestedFamily (O.obj P) P.inputs) ≫
      FiniteFamily.typeTensor.map f := by rfl
  change ColoredOperadObj.rightUnitInsert O unit P x (f.equiv j) = x
  rw [hEq]
  change FiniteFamily.typeTensorMap f t (f.equiv j) = x
  rw [FiniteFamily.typeTensorMap_apply]
  have hf : f.hom j = FiniteFamily.typeTensorSingletonIso.hom.app (O.obj P) := by
    simpa only [f, j] using rightFactorHom_none O unit P
  rw [hf]
  rfl

/-- In `Type`, every inner component of right-unit insertion is the corresponding unit. -/
theorem rightUnitInsert_apply_some (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) (x : O.obj P) (i : P.inputs) :
    ColoredOperadObj.rightUnitInsert O unit P x (some i) = unit (P.inputColor i)
      emptyTensorElement := by
  let f := ColoredOperadObj.UnitInsertion.rightFactorHom O unit P
  let j : (ColoredOperadObj.UnitInsertion.rightTensorFamily O P).index := some i
  let a : FiniteFamily.typeTensorObj (FiniteFamily.singleton.obj (O.obj P)) :=
    (FiniteFamily.typeTensorSingletonEquiv (O.obj P)).symm x
  let b : FiniteFamily.typeTensorObj
      (FiniteFamily.flatten.obj (UnitInsertion.rightNestedFamily (O.obj P) P.inputs)) :=
    FiniteFamily.typeTensorMap (UnitInsertion.rightSingletonToFlatten (O.obj P) P.inputs) a
  let t : FiniteFamily.typeTensorObj (ColoredOperadObj.UnitInsertion.rightTensorFamily O P) :=
    FiniteFamily.typeTensorFlattenEquiv
      (UnitInsertion.rightNestedFamily (O.obj P) P.inputs) b
  have hEq : ColoredOperadObj.rightUnitInsert O unit P =
      FiniteFamily.typeTensorSingletonIso.inv.app (O.obj P) ≫
      FiniteFamily.typeTensor.map (UnitInsertion.rightSingletonToFlatten (O.obj P) P.inputs) ≫
      FiniteFamily.typeTensorFlattenIso.hom.app
        (UnitInsertion.rightNestedFamily (O.obj P) P.inputs) ≫
      FiniteFamily.typeTensor.map f := by rfl
  rw [hEq]
  change FiniteFamily.typeTensorMap f t (f.equiv j) = unit (P.inputColor i) emptyTensorElement
  rw [FiniteFamily.typeTensorMap_apply]
  dsimp [f, j, ColoredOperadObj.UnitInsertion.rightFactorHom]
  congr 1
  funext e
  exact e.elim

/-- In `Type`, the outer component of left-unit insertion is the unit at the output color. -/
theorem leftUnitInsert_apply_none (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) (x : O.obj P) :
    ColoredOperadObj.leftUnitInsert O unit P x none = unit P.outputColor emptyTensorElement := by
  let f := ColoredOperadObj.UnitInsertion.leftFactorHom O unit P
  let j : (ColoredOperadObj.UnitInsertion.leftTensorFamily O P).index := none
  let a : FiniteFamily.typeTensorObj (FiniteFamily.singleton.obj (O.obj P)) :=
    (FiniteFamily.typeTensorSingletonEquiv (O.obj P)).symm x
  let b : FiniteFamily.typeTensorObj
      (FiniteFamily.flatten.obj (UnitInsertion.leftNestedFamily (O.obj P))) :=
    FiniteFamily.typeTensorMap (UnitInsertion.leftSingletonToFlatten (O.obj P)) a
  let t : FiniteFamily.typeTensorObj (ColoredOperadObj.UnitInsertion.leftTensorFamily O P) :=
    FiniteFamily.typeTensorFlattenEquiv (UnitInsertion.leftNestedFamily (O.obj P)) b
  have hEq : ColoredOperadObj.leftUnitInsert O unit P =
      FiniteFamily.typeTensorSingletonIso.inv.app (O.obj P) ≫
      FiniteFamily.typeTensor.map (UnitInsertion.leftSingletonToFlatten (O.obj P)) ≫
      FiniteFamily.typeTensorFlattenIso.hom.app (UnitInsertion.leftNestedFamily (O.obj P)) ≫
      FiniteFamily.typeTensor.map f := by rfl
  rw [hEq]
  change FiniteFamily.typeTensorMap f t (f.equiv j) = unit P.outputColor emptyTensorElement
  rw [FiniteFamily.typeTensorMap_apply]
  have hf : f.hom j = unit P.outputColor := by
    simpa only [f, j] using leftFactorHom_none O unit P
  rw [hf]
  congr 1
  funext e
  exact e.elim

/-- In `Type`, the unique inner component of left-unit insertion is the original operation. -/
theorem leftUnitInsert_apply_some (O : ColoredSymmetricCollection Color (Type v))
    (unit : ColoredOperadUnit O) (P : ColoredProfile Color) (x : O.obj P)
    (i : (ColoredSubstitutionData.leftUnit P).inner.index) :
    ColoredOperadObj.leftUnitInsert O unit P x (some i) = x := by rfl

/-- Assemble an outer operation and its family of inner operations into the substitution tensor of
a Type-valued collection. -/
def substitutionInputOf (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredSubstitutionData Color) (outer : O.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.obj (d.inner.obj i)) :
    (ColoredOperadObj.substitutionSource O).obj d :=
  fun o ↦ match o with
    | none => outer
    | some i => inner i

/-- Assemble an outer operation and its family of inner operations into the substitution tensor. -/
def substitutionInput (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color) (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.toCollection.obj (d.inner.obj i)) :
    (ColoredOperadObj.substitutionSource O.toCollection).obj d :=
  substitutionInputOf O.toCollection d outer inner

/-- The outer component of a substitution input. -/
@[simp]
theorem substitutionInput_none (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color) (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.toCollection.obj (d.inner.obj i)) :
    substitutionInput O d outer inner none = outer := rfl

/-- The outer component of `substitutionInputOf`. -/
@[simp]
theorem substitutionInputOf_none (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredSubstitutionData Color) (outer : O.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.obj (d.inner.obj i)) :
    substitutionInputOf O d outer inner none = outer := rfl

/-- An inner component of a substitution input. -/
@[simp]
theorem substitutionInput_some (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color) (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.toCollection.obj (d.inner.obj i))
    (i : d.inner.index) : substitutionInput O d outer inner (some i) = inner i := rfl

/-- An inner component of `substitutionInputOf`. -/
@[simp]
theorem substitutionInputOf_some (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredSubstitutionData Color) (outer : O.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.obj (d.inner.obj i))
    (i : d.inner.index) : substitutionInputOf O d outer inner (some i) = inner i := rfl

/-- Evaluate a relabeling of substitution factors at an arbitrary source index. -/
theorem substitutionSource_map_apply (O : ColoredSymmetricCollection Color (Type v))
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y)
    (fam : (ColoredOperadObj.substitutionSource O).obj X)
    (i : Option X.inner.index) :
    ((ColoredOperadObj.substitutionSource O).map f fam)
        (((ColoredOperadObj.substitutionFactors O).map f).equiv i) =
      ((ColoredOperadObj.substitutionFactors O).map f).hom i (fam i) := by
  change FiniteFamily.typeTensorMap ((ColoredOperadObj.substitutionFactors O).map f) fam
      (((ColoredOperadObj.substitutionFactors O).map f).equiv i) = _
  exact FiniteFamily.typeTensorMap_apply _ _ _

/-- Evaluate a relabeling of substitution factors at the outer index. -/
theorem substitutionSource_map_apply_none (O : ColoredSymmetricCollection Color (Type v))
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y)
    (fam : (ColoredOperadObj.substitutionSource O).obj X) :
    ((ColoredOperadObj.substitutionSource O).map f fam) none =
      ((ColoredOperadObj.substitutionFactors O).map f).hom none (fam none) := by
  have h1 := substitutionSource_map_apply O f fam none
  have h2 : ((ColoredOperadObj.substitutionSource O).map f fam)
      (((ColoredOperadObj.substitutionFactors O).map f).equiv none) =
        ((ColoredOperadObj.substitutionSource O).map f fam) none := rfl
  exact h2 ▸ h1

/-- Evaluate a relabeling of substitution factors at an inner index. -/
theorem substitutionSource_map_apply_some (O : ColoredSymmetricCollection Color (Type v))
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y)
    (fam : (ColoredOperadObj.substitutionSource O).obj X) (i : X.inner.index) :
    ((ColoredOperadObj.substitutionSource O).map f fam) (some (f.innerHom.equiv i)) =
      ((ColoredOperadObj.substitutionFactors O).map f).hom (some i) (fam (some i)) := by
  have h1 := substitutionSource_map_apply O f fam (some i)
  have h2 : ((ColoredOperadObj.substitutionSource O).map f fam)
      (((ColoredOperadObj.substitutionFactors O).map f).equiv (some i)) =
        ((ColoredOperadObj.substitutionSource O).map f fam)
          (some (f.innerHom.equiv i)) := rfl
  exact h2 ▸ h1

/-- Elementwise naturality of colored operadic substitution. -/
theorem subst_naturality_apply (O : ColoredSetOperad Color)
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y)
    (fam : (ColoredOperadObj.substitutionSource O.toCollection).obj X) :
    O.subst.app Y ((ColoredOperadObj.substitutionSource O.toCollection).map f fam) =
      O.toCollection.map (ColoredSubstitutionData.totalProfileMap f) (O.subst.app X fam) := by
  have h := O.subst.naturality f
  have h1 := congrArg (fun k ↦ k fam) h
  with_unfolding_all exact h1

/-- Elementwise functoriality of profile relabeling. -/
theorem map_comp_apply (O : ColoredSymmetricCollection Color (Type v))
    {P Q R : ColoredProfile Color} (f : P ⟶ Q) (g : Q ⟶ R) (x : O.obj P) :
    O.map g (O.map f x) = O.map (f ≫ g) x := by
  have h := congrArg (fun k ↦ k x) (O.map_comp f g)
  with_unfolding_all exact h.symm

/-- Simultaneous elementwise substitution for a collection equipped with a substitution map. -/
def fullSubstitutionOf (O : ColoredSymmetricCollection Color (Type v))
    (subst : ColoredOperadSubstitution O) (d : ColoredSubstitutionData Color)
    (outer : O.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.obj (d.inner.obj i)) : O.obj d.totalProfile :=
  subst.app d (substitutionInputOf O d outer inner)

/-- Simultaneous elementwise substitution of a family of operations into an outer operation. -/
def fullSubstitution (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color) (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) → O.toCollection.obj (d.inner.obj i)) :
    O.toCollection.obj d.totalProfile :=
  fullSubstitutionOf O.toCollection O.subst d outer inner

/-- Assemble the outer, middle, and inner operations into the common source of the two
associativity routes. -/
def associativityInput (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredAssocData Color)
    (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) →
      O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j)) :
    ColoredOperadObj.associativityCommonSource O d :=
  fun p ↦ match p with
    | ⟨none, j⟩ => match j with | PUnit.unit => outer
    | ⟨some i, none⟩ => middle i
    | ⟨some i, some j⟩ => inner i j

/-- The root component of an associativity input. -/
@[simp]
theorem associativityInput_root (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredAssocData Color) (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) → O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j)) :
    associativityInput O d outer middle inner ⟨none, PUnit.unit⟩ = outer := rfl

/-- A middle component of an associativity input. -/
@[simp]
theorem associativityInput_middle (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredAssocData Color) (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) → O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j)) (i : d.branches.index) :
    associativityInput O d outer middle inner ⟨some i, none⟩ = middle i := rfl

/-- An inner component of an associativity input. -/
@[simp]
theorem associativityInput_inner (O : ColoredSymmetricCollection Color (Type v))
    (d : ColoredAssocData Color) (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) → O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j))
    (i : d.branches.index) (j : (d.localData i).inner.index) :
    associativityInput O d outer middle inner ⟨some i, some j⟩ = inner i j := rfl

/-- Evaluate the first associativity route for arbitrary Type-valued substitution data. -/
theorem associativityRouteA_apply_of (O : ColoredSymmetricCollection Color (Type v))
    (subst : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color)
    (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) →
      O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j)) :
    ColoredOperadObj.associativityRouteA O subst d
        (associativityInput O d outer middle inner) =
      fullSubstitutionOf O subst d.outerAfterInnerData outer
        (fun i ↦ fullSubstitutionOf O subst (d.localData i) (middle i) (inner i)) := by
  unfold ColoredOperadObj.associativityRouteA
  unfold fullSubstitutionOf
  let f := ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
    O subst d
  let t := FiniteFamily.typeTensorFlattenEquiv
    (ColoredOperadObj.AssocInsertion.groupingA O d)
    (associativityInput O d outer middle inner)
  change subst.app d.outerAfterInnerData (FiniteFamily.typeTensorMap f t) = _
  congr 1
  funext o
  with_unfolding_all change Option d.branches.index at o
  cases o with
  | none =>
      let j : ((FiniteFamily.map FiniteFamily.typeTensor).obj
        (ColoredOperadObj.AssocInsertion.groupingA O d)).index := none
      change FiniteFamily.typeTensorMap f t (f.equiv j) = outer
      rw [FiniteFamily.typeTensorMap_apply]
      rfl
  | some i =>
      let j : ((FiniteFamily.map FiniteFamily.typeTensor).obj
        (ColoredOperadObj.AssocInsertion.groupingA O d)).index := some i
      change FiniteFamily.typeTensorMap f t (f.equiv j) = _
      rw [FiniteFamily.typeTensorMap_apply]
      have hf : f.hom j = subst.app (d.localData i) := by rfl
      rw [hf]
      have ht : t j = fun o ↦ match o with
          | none => middle i
          | some k => inner i k := by
        funext o
        cases o with
        | none =>
            change associativityInput O d outer middle inner ⟨some i, none⟩ = middle i
            exact associativityInput_middle O d outer middle inner i
        | some k =>
            change associativityInput O d outer middle inner ⟨some i, some k⟩ = inner i k
            exact associativityInput_inner O d outer middle inner i k
      rw [ht]
      have hInput : (fun o ↦ match o with
          | none => middle i
          | some k => inner i k) = substitutionInputOf O (d.localData i) (middle i) (inner i) := by
        funext o
        cases o with
        | none => exact (substitutionInputOf_none O (d.localData i) (middle i) (inner i)).symm
        | some k =>
            exact (substitutionInputOf_some O (d.localData i) (middle i) (inner i) k).symm
      have hLocal := congrArg (fun z ↦ subst.app (d.localData i) z) hInput
      exact hLocal.trans
        (substitutionInputOf_some O d.outerAfterInnerData outer
          (fun i ↦ subst.app (d.localData i)
            (substitutionInputOf O (d.localData i) (middle i) (inner i))) i).symm

/-- Evaluate the second associativity route for arbitrary Type-valued substitution data. -/
theorem associativityRouteB_apply_of (O : ColoredSymmetricCollection Color (Type v))
    (subst : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color)
    (outer : O.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) →
      O.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.obj ((d.localData i).inner.obj j)) :
    ColoredOperadObj.associativityRouteB O subst d
        (associativityInput O d outer middle inner) =
      O.map d.totalHom
        (fullSubstitutionOf O subst d.innerData
          (fullSubstitutionOf O subst d.middleData outer middle)
          (fun p ↦ inner p.1 p.2)) := by
  unfold ColoredOperadObj.associativityRouteB
  unfold fullSubstitutionOf
  let r := ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O d
  let s : FiniteFamily.typeTensorObj
      (ColoredOperadObj.AssocInsertion.flattenedGroupingA O d) :=
    associativityInput O d outer middle inner
  let f := ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
    O subst d
  let t := FiniteFamily.typeTensorFlattenEquiv
    (ColoredOperadObj.AssocInsertion.groupingB O d)
    (FiniteFamily.typeTensorMap r s)
  change O.map d.totalHom
      (subst.app d.innerData (FiniteFamily.typeTensorMap f t)) = _
  congr 2
  funext o
  with_unfolding_all change Option d.middleData.totalProfile.inputs at o
  cases o with
  | none =>
      let j : ((FiniteFamily.map FiniteFamily.typeTensor).obj
        (ColoredOperadObj.AssocInsertion.groupingB O d)).index := none
      change FiniteFamily.typeTensorMap f t (f.equiv j) = _
      rw [FiniteFamily.typeTensorMap_apply]
      have hf : f.hom j = subst.app d.middleData := by rfl
      rw [hf]
      have ht : t j = fun o ↦ match o with
          | none => outer
          | some i => middle i := by
        funext o
        cases o with
        | none =>
            let k : (ColoredOperadObj.AssocInsertion.flattenedGroupingA
              O d).index := ⟨none, PUnit.unit⟩
            change FiniteFamily.typeTensorMap r s (r.equiv k) = outer
            rw [FiniteFamily.typeTensorMap_apply]
            change associativityInput O d outer middle inner k = outer
            exact associativityInput_root O d outer middle inner
        | some i =>
            with_unfolding_all change d.branches.index at i
            let k : (ColoredOperadObj.AssocInsertion.flattenedGroupingA
              O d).index := ⟨some i, none⟩
            change FiniteFamily.typeTensorMap r s (r.equiv k) = middle i
            rw [FiniteFamily.typeTensorMap_apply]
            change associativityInput O d outer middle inner k = middle i
            exact associativityInput_middle O d outer middle inner i
      rw [ht]
      have hInput : (fun o ↦ match o with
          | none => outer
          | some i => middle i) = substitutionInputOf O d.middleData outer middle := by
        funext o
        cases o with
        | none => exact (substitutionInputOf_none O d.middleData outer middle).symm
        | some i => exact (substitutionInputOf_some O d.middleData outer middle i).symm
      have hMiddle := congrArg (fun z ↦ subst.app d.middleData z) hInput
      exact hMiddle.trans
        (substitutionInputOf_none O d.innerData
          (subst.app d.middleData (substitutionInputOf O d.middleData outer middle))
          (fun p ↦ inner p.1 p.2)).symm
  | some p =>
      let j : ((FiniteFamily.map FiniteFamily.typeTensor).obj
        (ColoredOperadObj.AssocInsertion.groupingB O d)).index := some p
      change FiniteFamily.typeTensorMap f t (f.equiv j) = _
      rw [FiniteFamily.typeTensorMap_apply]
      have hf : f.hom j = FiniteFamily.typeTensorSingletonIso.hom.app
          (O.obj (d.innerData.inner.obj p)) := by rfl
      rw [hf]
      rfl

/-- Evaluate the first associativity route of a Type-valued colored operad. -/
theorem associativityRouteA_apply (O : ColoredSetOperad Color)
    (d : ColoredAssocData Color)
    (outer : O.toCollection.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) → O.toCollection.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.toCollection.obj ((d.localData i).inner.obj j)) :
    ColoredOperadObj.associativityRouteA O.toCollection O.subst d
        (associativityInput O.toCollection d outer middle inner) =
      fullSubstitution O d.outerAfterInnerData outer
        (fun i ↦ fullSubstitution O (d.localData i) (middle i) (inner i)) :=
  associativityRouteA_apply_of O.toCollection O.subst d outer middle inner

/-- Evaluate the second associativity route of a Type-valued colored operad. -/
theorem associativityRouteB_apply (O : ColoredSetOperad Color)
    (d : ColoredAssocData Color)
    (outer : O.toCollection.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) → O.toCollection.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.toCollection.obj ((d.localData i).inner.obj j)) :
    ColoredOperadObj.associativityRouteB O.toCollection O.subst d
        (associativityInput O.toCollection d outer middle inner) =
      O.toCollection.map d.totalHom
        (fullSubstitution O d.innerData
          (fullSubstitution O d.middleData outer middle)
          (fun p ↦ inner p.1 p.2)) :=
  associativityRouteB_apply_of O.toCollection O.subst d outer middle inner

/-- Elementwise associativity of simultaneous colored substitution.

This theorem has no nonemptiness hypotheses, so it also covers nullary operations and empty
families of branches. -/
theorem fullSubstitution_assoc (O : ColoredSetOperad Color)
    (d : ColoredAssocData Color)
    (outer : O.toCollection.obj d.middleData.outerProfile)
    (middle : (i : d.branches.index) →
      O.toCollection.obj (d.localData i).outerProfile)
    (inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.toCollection.obj ((d.localData i).inner.obj j)) :
    fullSubstitution O d.outerAfterInnerData outer
        (fun i ↦ fullSubstitution O (d.localData i) (middle i) (inner i)) =
      O.toCollection.map d.totalHom
        (fullSubstitution O d.innerData
          (fullSubstitution O d.middleData outer middle)
          (fun p ↦ inner p.1 p.2)) := by
  have h := congrArg
    (fun k ↦ k (associativityInput O.toCollection d outer middle inner)) (O.assoc d)
  rw [associativityRouteA_apply, associativityRouteB_apply] at h
  exact h

/-- Evaluate the source map induced by a collection morphism at one substitution factor. -/
theorem homData_sourceHom_apply
    {O P : ColoredSymmetricCollection Color (Type v)} (F : O ⟶ P)
    (d : ColoredSubstitutionData Color)
    (fam : (ColoredOperadObj.substitutionSource O).obj d)
    (i : Option d.inner.index) :
    ColoredOperadObj.HomData.sourceHom F d fam i =
      F.app (d.factorFamily.obj i) (fam i) := by
  let f := ColoredOperadObj.HomData.factorHom F d
  let j : ((ColoredOperadObj.substitutionFactors O).obj d).index := i
  let t : FiniteFamily.typeTensorObj ((ColoredOperadObj.substitutionFactors O).obj d) := fam
  change FiniteFamily.typeTensorMap f t (f.equiv j) = _
  rw [FiniteFamily.typeTensorMap_apply]
  rfl

/-- Left-unit insertion, elementwise: the outer component is the unit
and the unique inner component is the original operation. -/
theorem leftUnitInsert_eq (O : ColoredSetOperad Color)
    (P : ColoredProfile Color) (x : O.toCollection.obj P) :
    ColoredOperadObj.leftUnitInsert O.toCollection O.unit P x =
      ColoredSetOperad.substitutionInputOf O.toCollection
        (ColoredSubstitutionData.leftUnit P)
        (ColoredSetOperad.unitElement O P.outputColor)
        (fun _ => x) := by
  funext o
  with_unfolding_all change Option PUnit at o
  cases o with
  | none =>
      have h1 := ColoredSetOperad.leftUnitInsert_apply_none
        O.toCollection O.unit P x
      exact h1.trans rfl
  | some i =>
      have h1 := ColoredSetOperad.leftUnitInsert_apply_some
        O.toCollection O.unit P x i
      exact h1.trans rfl

/-- Elementwise left-unit law for simultaneous substitution:
substituting into the unit recovers the operation. -/
theorem leftUnitlaw_apply (O : ColoredSetOperad Color)
    (P : ColoredProfile Color) (x : O.toCollection.obj P) :
    O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
      (ColoredSetOperad.fullSubstitution O
        (ColoredSubstitutionData.leftUnit P)
        (ColoredSetOperad.unitElement O P.outputColor)
        (fun _ => x)) = x := by
  have hApp := congrArg (fun k => k x) (O.left_unit P)
  simp only [types_comp_apply] at hApp
  rw [leftUnitInsert_eq O P x] at hApp
  exact hApp

end ColoredSetOperad

end CategoryTheory.Operad
