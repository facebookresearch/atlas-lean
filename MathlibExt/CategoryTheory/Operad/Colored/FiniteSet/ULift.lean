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

public import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.Basic
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColor
public import MathlibExt.CategoryTheory.Operad.FiniteSet.Basic

/-!
# Universe lifts of colored set operads

A small Type-valued colored operad can be lifted into an arbitrary operation universe by applying
`ULift` to every operation type. This file constructs the lifted collection, unit, substitution,
and operad, together with computation lemmas projecting the lifted structure back down.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredSetOperad

open CategoryTheory

universe u v

variable {Color : Type u}

/-- Lift every object and structure map of a small Type-valued colored collection. -/
def liftCollection (O : ColoredSetOperad.{u, 0} Color) :
    ColoredSymmetricCollection Color (Type v) where
  obj P := ULift.{v} (O.toCollection.obj P)
  map f := TypeCat.ofHom fun x => ⟨O.toCollection.map f x.down⟩
  map_id P := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    apply ULift.ext
    exact ConcreteCategory.hom_ext_iff.mp (O.toCollection.map_id P) x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x⟩
    apply ULift.ext
    exact ConcreteCategory.hom_ext_iff.mp (O.toCollection.map_comp f g) x

/-- Lift the unit data of a small Type-valued colored operad. -/
def liftUnit (O : ColoredSetOperad.{u, 0} Color) :
    ColoredOperadUnit (liftCollection.{u, v} O) :=
  fun c => TypeCat.ofHom fun _ => ⟨unitElement O c⟩

/-- Lift the substitution data of a small Type-valued colored operad. -/
def liftSubstitution (O : ColoredSetOperad.{u, 0} Color) :
    ColoredOperadSubstitution (liftCollection.{u, v} O) where
  app d := TypeCat.ofHom fun ops => ⟨O.subst.app d (fun o => (ops o).down)⟩
  naturality := by
    intro d e f
    apply ConcreteCategory.hom_ext
    intro ops
    apply ULift.ext
    let y := (ColoredOperadObj.substitutionSource (liftCollection.{u, v} O)).map f ops
    let z := fun o => (ops o).down
    have hy0 : (y none).down =
        O.toCollection.map (ColoredSubstitutionData.outerProfileMap f) (z none) := by
      have h := substitutionSource_map_apply_none (liftCollection.{u, v} O) f ops
      exact congrArg ULift.down h
    have hyi (i : d.inner.index) : (y (some (f.innerHom.equiv i))).down =
        O.toCollection.map (f.innerHom.hom i) (z (some i)) := by
      have h := substitutionSource_map_apply_some (liftCollection.{u, v} O) f ops i
      exact congrArg ULift.down h
    have hO := O.subst.naturality f
    have hEval := congrArg (fun k => k z) hO
    have hz : (fun o => (y o).down) =
        (ColoredOperadObj.substitutionSource O.toCollection).map f z := by
      funext o
      cases o with
      | none =>
          exact hy0.trans
            (substitutionSource_map_apply_none O.toCollection f z).symm
      | some j =>
          obtain ⟨i, rfl⟩ := f.innerHom.equiv.surjective j
          exact (hyi i).trans
            (substitutionSource_map_apply_some O.toCollection f z i).symm
    change O.subst.app e (fun o => (y o).down) =
      O.toCollection.map (ColoredSubstitutionData.totalProfileMap f) (O.subst.app d z)
    calc
      O.subst.app e (fun o => (y o).down) =
          O.subst.app e ((ColoredOperadObj.substitutionSource O.toCollection).map f z) :=
        congrArg (fun q => O.subst.app e q) hz
      _ = _ := by with_unfolding_all exact hEval

/-- Relabeling a lifted operation and projecting down is relabeling before lifting. -/
@[simp]
theorem liftCollection_map_down (O : ColoredSetOperad.{u, 0} Color)
    {P Q : ColoredProfile Color} (f : P ⟶ Q)
    (x : (liftCollection.{u, v} O).obj P) :
    ((liftCollection.{u, v} O).map f x).down = O.toCollection.map f x.down :=
  rfl

/-- The lifted unit projects to the original unit element. -/
@[simp]
theorem liftUnit_down (O : ColoredSetOperad.{u, 0} Color) (c : Color)
    (x : operadUnitSource (V := Type v)) :
    ((liftUnit.{u, v} O) c x).down = unitElement O c :=
  rfl

/-- Lifted substitution projects to the original substitution. -/
@[simp]
theorem liftSubstitution_down (O : ColoredSetOperad.{u, 0} Color)
    (d : ColoredSubstitutionData Color)
    (ops : (ColoredOperadObj.substitutionSource (liftCollection.{u, v} O)).obj d) :
    ((liftSubstitution.{u, v} O).app d ops).down =
      O.subst.app d (fun o ↦ (ops o).down) :=
  rfl

/-- Full substitution in the lifted operad projects to full substitution in the original operad. -/
@[simp]
theorem liftFullSubstitution_down (O : ColoredSetOperad.{u, 0} Color)
    (d : ColoredSubstitutionData Color)
    (outer : (liftCollection.{u, v} O).obj d.outerProfile)
    (inner : ∀ i, (liftCollection.{u, v} O).obj (d.inner.obj i)) :
    (fullSubstitutionOf (liftCollection.{u, v} O) (liftSubstitution.{u, v} O) d
      outer inner).down =
      fullSubstitutionOf O.toCollection O.subst d outer.down (fun i ↦ (inner i).down) :=
  by
    unfold fullSubstitutionOf
    rw [liftSubstitution_down]
    congr 1
    funext o
    cases o <;> rfl

/-- Lifting preserves the right unit law of an arbitrary small colored set operad. -/
theorem liftIsRightUnit (O : ColoredSetOperad.{u, 0} Color) :
    ColoredOperadObj.IsRightUnit (liftCollection.{u, v} O)
      (liftUnit.{u, v} O) (liftSubstitution.{u, v} O) := by
  intro P
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  have hInsert : ColoredOperadObj.rightUnitInsert
      (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩ =
      substitutionInputOf (liftCollection.{u, v} O)
        (ColoredSubstitutionData.rightUnit P) ⟨x⟩
        (fun i ↦ (liftUnit.{u, v} O) (P.inputColor i) emptyTensorElement) := by
    funext o
    cases o with
    | none =>
        with_unfolding_all
          exact rightUnitInsert_apply_none
            (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩
    | some i =>
        with_unfolding_all
          exact rightUnitInsert_apply_some
            (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩ i
  with_unfolding_all
    change (liftCollection.{u, v} O).map
      (ColoredSubstitutionData.rightUnitTotalHom P)
      ((liftSubstitution.{u, v} O).app (ColoredSubstitutionData.rightUnit P)
        (ColoredOperadObj.rightUnitInsert
          (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩)) = ⟨x⟩
  rw [hInsert]
  apply ULift.ext
  have hInsertSmall : ColoredOperadObj.rightUnitInsert O.toCollection O.unit P x =
      substitutionInputOf O.toCollection (ColoredSubstitutionData.rightUnit P) x
        (fun i ↦ O.unit (P.inputColor i) emptyTensorElement) := by
    funext o
    cases o with
    | none => simpa only [substitutionInputOf] using
        rightUnitInsert_apply_none O.toCollection O.unit P x
    | some i => simpa only [substitutionInputOf] using
        rightUnitInsert_apply_some O.toCollection O.unit P x i
  have hSmall := congrArg (fun k ↦ k x) (O.right_unit P)
  with_unfolding_all
    change O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.rightUnit P)
        (ColoredOperadObj.rightUnitInsert O.toCollection O.unit P x)) = x at hSmall
  rw [hInsertSmall] at hSmall
  with_unfolding_all
    change O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.rightUnit P) (fun o ↦
        (substitutionInputOf (liftCollection.{u, v} O)
          (ColoredSubstitutionData.rightUnit P) ⟨x⟩
          (fun i ↦ (liftUnit.{u, v} O) (P.inputColor i) emptyTensorElement) o).down)) = x
  have hInput : (fun o ↦
      (substitutionInputOf (liftCollection.{u, v} O)
        (ColoredSubstitutionData.rightUnit P) ⟨x⟩
        (fun i ↦ (liftUnit.{u, v} O) (P.inputColor i) emptyTensorElement) o).down) =
      substitutionInputOf O.toCollection (ColoredSubstitutionData.rightUnit P) x
        (fun i ↦ O.unit (P.inputColor i) emptyTensorElement) := by
    funext o
    cases o <;> rfl
  exact (congrArg
    (fun q ↦ O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.rightUnit P) q)) hInput).trans hSmall

/-- Lifting preserves the left unit law of an arbitrary small colored set operad. -/
theorem liftIsLeftUnit (O : ColoredSetOperad.{u, 0} Color) :
    ColoredOperadObj.IsLeftUnit (liftCollection.{u, v} O)
      (liftUnit.{u, v} O) (liftSubstitution.{u, v} O) := by
  intro P
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  have hInsert : ColoredOperadObj.leftUnitInsert
      (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩ =
      substitutionInputOf (liftCollection.{u, v} O)
        (ColoredSubstitutionData.leftUnit P)
        ((liftUnit.{u, v} O) P.outputColor emptyTensorElement) (fun _ ↦ ⟨x⟩) := by
    funext o
    cases o with
    | none =>
        with_unfolding_all
          exact leftUnitInsert_apply_none
            (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩
    | some i =>
        with_unfolding_all
          exact leftUnitInsert_apply_some
            (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩ i
  with_unfolding_all
    change (liftCollection.{u, v} O).map
      (ColoredSubstitutionData.leftUnitTotalHom P)
      ((liftSubstitution.{u, v} O).app (ColoredSubstitutionData.leftUnit P)
        (ColoredOperadObj.leftUnitInsert
          (liftCollection.{u, v} O) (liftUnit.{u, v} O) P ⟨x⟩)) = ⟨x⟩
  rw [hInsert]
  apply ULift.ext
  have hInsertSmall : ColoredOperadObj.leftUnitInsert O.toCollection O.unit P x =
      substitutionInputOf O.toCollection (ColoredSubstitutionData.leftUnit P)
        (O.unit P.outputColor emptyTensorElement) (fun _ ↦ x) := by
    funext o
    cases o with
    | none => simpa only [substitutionInputOf] using
        leftUnitInsert_apply_none O.toCollection O.unit P x
    | some i => simpa only [substitutionInputOf] using
        leftUnitInsert_apply_some O.toCollection O.unit P x i
  have hSmall := congrArg (fun k ↦ k x) (O.left_unit P)
  with_unfolding_all
    change O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.leftUnit P)
        (ColoredOperadObj.leftUnitInsert O.toCollection O.unit P x)) = x at hSmall
  rw [hInsertSmall] at hSmall
  with_unfolding_all
    change O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.leftUnit P) (fun o ↦
        (substitutionInputOf (liftCollection.{u, v} O)
          (ColoredSubstitutionData.leftUnit P)
          ((liftUnit.{u, v} O) P.outputColor emptyTensorElement)
          (fun _ ↦ ⟨x⟩) o).down)) = x
  have hInput : (fun o ↦
      (substitutionInputOf (liftCollection.{u, v} O)
        (ColoredSubstitutionData.leftUnit P)
        ((liftUnit.{u, v} O) P.outputColor emptyTensorElement) (fun _ ↦ ⟨x⟩) o).down) =
      substitutionInputOf O.toCollection (ColoredSubstitutionData.leftUnit P)
        (O.unit P.outputColor emptyTensorElement) (fun _ ↦ x) := by
    funext o
    cases o <;> rfl
  exact (congrArg
    (fun q ↦ O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
      (O.subst.app (ColoredSubstitutionData.leftUnit P) q)) hInput).trans hSmall

/-- Lifting preserves associativity of an arbitrary small colored set operad. -/
theorem liftIsAssociative (O : ColoredSetOperad.{u, 0} Color) :
    ColoredOperadObj.IsAssociative (liftCollection.{u, v} O)
      (liftSubstitution.{u, v} O) := by
  intro d
  apply ConcreteCategory.hom_ext
  intro ops
  let outer : O.toCollection.obj d.middleData.outerProfile := (ops ⟨none, PUnit.unit⟩).down
  let middle : (i : d.branches.index) → O.toCollection.obj (d.localData i).outerProfile :=
    fun i ↦ (ops ⟨some i, none⟩).down
  let inner : (i : d.branches.index) → (j : (d.localData i).inner.index) →
      O.toCollection.obj ((d.localData i).inner.obj j) :=
    fun i j ↦ (ops ⟨some i, some j⟩).down
  have hops : associativityInput (liftCollection.{u, v} O) d
      ⟨outer⟩ (fun i ↦ ⟨middle i⟩) (fun i j ↦ ⟨inner i j⟩) = ops := by
    funext p
    obtain ⟨o, j⟩ := p
    cases o with
    | none => cases j; apply ULift.ext; rfl
    | some i => cases j <;> apply ULift.ext <;> rfl
  rw [← hops]
  have hA := associativityRouteA_apply_of (liftCollection.{u, v} O)
    (liftSubstitution.{u, v} O) d ⟨outer⟩ (fun i ↦ ⟨middle i⟩) (fun i j ↦ ⟨inner i j⟩)
  have hB := associativityRouteB_apply_of (liftCollection.{u, v} O)
    (liftSubstitution.{u, v} O) d ⟨outer⟩ (fun i ↦ ⟨middle i⟩) (fun i j ↦ ⟨inner i j⟩)
  rw [hA, hB]
  apply ULift.ext
  let localLift (i : d.branches.index) :=
    fullSubstitutionOf (liftCollection.{u, v} O) (liftSubstitution.{u, v} O)
      (d.localData i) ⟨middle i⟩ (fun j ↦ ⟨inner i j⟩)
  have hLocal (i : d.branches.index) : (localLift i).down =
      fullSubstitutionOf O.toCollection O.subst (d.localData i) (middle i) (inner i) :=
    liftFullSubstitution_down O (d.localData i) ⟨middle i⟩ (fun j ↦ ⟨inner i j⟩)
  let middleLift := fullSubstitutionOf (liftCollection.{u, v} O)
    (liftSubstitution.{u, v} O) d.middleData ⟨outer⟩ (fun i ↦ ⟨middle i⟩)
  have hMiddle : middleLift.down =
      fullSubstitutionOf O.toCollection O.subst d.middleData outer middle :=
    liftFullSubstitution_down O d.middleData ⟨outer⟩ (fun i ↦ ⟨middle i⟩)
  let innerLift := fullSubstitutionOf (liftCollection.{u, v} O)
    (liftSubstitution.{u, v} O) d.innerData middleLift (fun p ↦ ⟨inner p.1 p.2⟩)
  have hInner : innerLift.down =
      fullSubstitutionOf O.toCollection O.subst d.innerData middleLift.down
        (fun p ↦ inner p.1 p.2) :=
    liftFullSubstitution_down O d.innerData middleLift (fun p ↦ ⟨inner p.1 p.2⟩)
  have hSmall := congrArg
    (fun k ↦ k (associativityInput O.toCollection d outer middle inner))
    (O.assoc d)
  rw [associativityRouteA_apply_of, associativityRouteB_apply_of] at hSmall
  calc
    (fullSubstitutionOf (liftCollection.{u, v} O) (liftSubstitution.{u, v} O)
        d.outerAfterInnerData ⟨outer⟩ (fun i ↦ localLift i)).down =
        fullSubstitutionOf O.toCollection O.subst d.outerAfterInnerData outer
          (fun i ↦ (localLift i).down) :=
      liftFullSubstitution_down O d.outerAfterInnerData ⟨outer⟩ (fun i ↦ localLift i)
    _ = fullSubstitutionOf O.toCollection O.subst d.outerAfterInnerData outer
          (fun i ↦ fullSubstitutionOf O.toCollection O.subst
            (d.localData i) (middle i) (inner i)) := by
      congr 1
      funext i
      exact hLocal i
    _ = O.toCollection.map d.totalHom
          (fullSubstitutionOf O.toCollection O.subst d.innerData
            (fullSubstitutionOf O.toCollection O.subst d.middleData outer middle)
            (fun p ↦ inner p.1 p.2)) := hSmall
    _ = O.toCollection.map d.totalHom
          (fullSubstitutionOf O.toCollection O.subst d.innerData middleLift.down
            (fun p ↦ inner p.1 p.2)) := by rw [hMiddle]
    _ = O.toCollection.map d.totalHom innerLift.down := by rw [hInner]
    _ = ((liftCollection.{u, v} O).map d.totalHom innerLift).down := rfl

/-- Lift a small colored set operad into an arbitrary operation universe. -/
def liftOperad (O : ColoredSetOperad.{u, 0} Color) : ColoredSetOperad.{u, v} Color where
  toCollection := liftCollection.{u, v} O
  unit := liftUnit.{u, v} O
  subst := liftSubstitution.{u, v} O
  right_unit := liftIsRightUnit.{u, v} O
  left_unit := liftIsLeftUnit.{u, v} O
  assoc := liftIsAssociative.{u, v} O

/-- Operations in a lifted operad are the original operations, up to `ULift`. -/
def liftOperationEquiv (O : ColoredSetOperad.{u, 0} Color) (P : ColoredProfile Color) :
    (liftOperad.{u, v} O).toCollection.obj P ≃ O.toCollection.obj P := by
  change ULift.{v} (O.toCollection.obj P) ≃ O.toCollection.obj P
  exact Equiv.ulift

/-- Projecting a lifted operation recovers the original operation. -/
@[simp]
theorem liftOperationEquiv_apply (O : ColoredSetOperad.{u, 0} Color)
    (P : ColoredProfile Color) (x : (liftOperad.{u, v} O).toCollection.obj P) :
    liftOperationEquiv O P x = x.down :=
  rfl

/-- Lifting an original operation wraps it in `ULift`. -/
@[simp]
theorem liftOperationEquiv_symm_apply (O : ColoredSetOperad.{u, 0} Color)
    (P : ColoredProfile Color) (x : O.toCollection.obj P) :
    (liftOperationEquiv O P).symm x = ⟨x⟩ :=
  rfl

end CategoryTheory.Operad.ColoredSetOperad

namespace CategoryTheory.Operad.SetOperad

universe v

/-- Lift an ordinary small set operad to an arbitrary operation universe.

The construction reuses the one-color equivalence and the colored-operad universe lift, rather
than duplicating the operad laws. Its operation types are canonically `ULift`-equivalent to the
original operations. -/
noncomputable def ulift (O : SetOperad.{0}) : SetOperad.{v} :=
  ColoredOperadObj.OneColor.uncolorFunctor.{v + 1, v, 0}.obj
    (ColoredSetOperad.liftOperad.{0, v}
      (ColoredOperadObj.OneColor.colorizeFunctor.{1, 0, 0}.obj O))

/-- Operations in the lifted ordinary operad are canonically equivalent to the original
operations. -/
noncomputable def uliftOperationEquiv (O : SetOperad.{0}) (I : FintypeCat) :
    (ulift.{v} O).toCollection.eval I ≃ O.toCollection.eval I := by
  change ULift.{v} (O.toCollection.eval I) ≃ O.toCollection.eval I
  exact Equiv.ulift

@[simp]
theorem uliftOperationEquiv_apply (O : SetOperad.{0}) (I : FintypeCat)
    (x : (ulift.{v} O).toCollection.eval I) :
    uliftOperationEquiv O I x = x.down :=
  rfl

@[simp]
theorem uliftOperationEquiv_symm_apply (O : SetOperad.{0}) (I : FintypeCat)
    (x : O.toCollection.eval I) :
    (uliftOperationEquiv.{v} O I).symm x = ⟨x⟩ :=
  rfl

end CategoryTheory.Operad.SetOperad
