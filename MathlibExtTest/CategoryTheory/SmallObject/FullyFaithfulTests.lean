/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.FullyFaithful
import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Presentable.Type

/-!
# Tests for fully faithful small-object transfer

These tests exercise attachment and relative-cell mapping, the cardinal
transfer signature, and both directions of the generated-left-class
comparison. A concrete client in `Type u` derives every hypothesis of both
endpoints instead of assuming it.
-/

set_option autoImplicit false

noncomputable section

universe w v uC uD

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra

variable {C : Type uC} [Category.{v} C]
variable {D : Type uD} [Category.{v} D]

section AttachCells

variable (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]

example {A B : Empty → C} {g : (a : Empty) → A a ⟶ B a}
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) :
    AttachCells.{w} (fun a ↦ F.map (g a)) (F.map f) :=
  c.map F

example {A B : PUnit → C} {g : (a : PUnit) → A a ⟶ B a}
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) :
    AttachCells.{w} (fun a ↦ F.map (g a)) (F.map f) :=
  c.map F

end AttachCells

section RelativeCellComplex

variable (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K]
  [WellFoundedLT K]
variable [PreservesColimitsOfShape K F]
  [PreservesWellOrderContinuousOfShape K F]

example {alpha : K → Type*}
    {A B : (k : K) → alpha k → C}
    {cell : (k : K) → (a : alpha k) → A k a ⟶ B k a}
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} cell f) :
    RelativeCellComplex.{w} (fun k a ↦ F.map (cell k a)) (F.map f) :=
  c.map F

example (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F)
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : K) ↦ P.homFamily) f) :
    RelativeCellComplex.{w} (fun (_ : K) ↦ Q.homFamily) (F.map f) :=
  c.mapOfLE F P Q hPQ

end RelativeCellComplex

section LimitStageRelativeCellComplex

variable (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
variable [PreservesColimitsOfShape (WithTop ℕ) F]
  [PreservesWellOrderContinuousOfShape (WithTop ℕ) F]

example {A B : (k : WithTop ℕ) → Empty → C}
    {cell : (k : WithTop ℕ) → (a : Empty) → A k a ⟶ B k a}
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} cell f) :
    RelativeCellComplex.{w} (fun k a ↦ F.map (cell k a)) (F.map f) :=
  c.map F

end LimitStageRelativeCellComplex

section CardinalTransfer

variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable (P : MorphismProperty C) (Q : MorphismProperty D)
variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
variable [P.IsSmall.{w}] [LocallySmall.{w} C]
variable [HasPushouts C] [HasCoproducts.{w} C]
variable [HasIterationOfShape κ.ord.ToType C]
variable [PreservesColimitsOfSize.{w, w} F]
variable [Q.IsCardinalForSmallObjectArgument κ]

example (hPQ : P ≤ Q.inverseImage F) :
    P.IsCardinalForSmallObjectArgument κ :=
  MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful
    F P Q κ hPQ

end CardinalTransfer

section GeneratedLeftClass

variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable (P : MorphismProperty C) (Q : MorphismProperty D)
variable [P.HasSmallObjectArgument.{w}]
variable [PreservesColimitsOfSize.{w, w} F]
variable (hPQ : P ≤ Q.inverseImage F)
variable (hrlp : P.rlp = Q.rlp.inverseImage F)

example {X Y : C} {f : X ⟶ Y} (hf : P.rlp.llp f) :
    Q.rlp.llp (F.map f) := by
  rw [MorphismProperty.rlp_llp_eq_inverseImage_of_fullyFaithful
    F P Q hPQ hrlp] at hf
  exact hf

example {X Y : C} {f : X ⟶ Y} (hf : Q.rlp.llp (F.map f)) :
    P.rlp.llp f := by
  rw [MorphismProperty.rlp_llp_eq_inverseImage_of_fullyFaithful
    F P Q hPQ hrlp]
  exact hf

end GeneratedLeftClass

section MissingColimitFalsifier

variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable (P : MorphismProperty C) (Q : MorphismProperty D)
variable [P.HasSmallObjectArgument.{w}]

example (_hPQ : P ≤ Q.inverseImage F)
    (_hrlp : P.rlp = Q.rlp.inverseImage F) : True := by
  fail_if_success
    have _ := MorphismProperty.rlp_llp_eq_inverseImage_of_fullyFaithful
      F P Q _hPQ _hrlp
  trivial

end MissingColimitFalsifier

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MorphismProperty.fullyFaithfulCoyonedaIso

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MorphismProperty.colimitsOfShape_le_inverseImage_map

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MorphismProperty.coproducts_le_inverseImage_map

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MorphismProperty.pushouts_le_inverseImage_map

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MorphismProperty.transfiniteCompositions_le_inverseImage_map

#print axioms HomotopicalAlgebra.AttachCells.map
#print axioms HomotopicalAlgebra.RelativeCellComplex.map
#print axioms HomotopicalAlgebra.RelativeCellComplex.mapOfLE
#print axioms CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful
#print axioms CategoryTheory.MorphismProperty.rlp_llp_eq_inverseImage_of_fullyFaithful


namespace IndependentHomUniverseClients

universe vC vD t uAlpha

variable {C₁ : Type uC} [Category.{vC} C₁]
variable {D₁ : Type uD} [Category.{vD} D₁]
variable (F : C₁ ⥤ D₁) [PreservesColimitsOfSize.{w, w} F]

section Attachments

variable {alpha : Type uAlpha} {A B : alpha → C₁}
  {g : (a : alpha) → A a ⟶ B a}
  {X Y : C₁} {f : X ⟶ Y} (c : AttachCells.{w} g f)

example : AttachCells.{w} (fun a => F.map (g a)) (F.map f) := c.map F

example : (c.map F).cofan₁.pt = F.obj c.cofan₁.pt := rfl
example : (c.map F).cofan₂.pt = F.obj c.cofan₂.pt := rfl
example : (c.map F).g₁ = F.map c.g₁ := rfl
example : (c.map F).g₂ = F.map c.g₂ := rfl

end Attachments

section Complexes

variable {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
variable [PreservesColimitsOfShape T F] [PreservesWellOrderContinuousOfShape T F]

example {alpha : T → Type uAlpha}
    {A B : (k : T) → alpha k → C₁}
    {cell : (k : T) → (a : alpha k) → A k a ⟶ B k a}
    {X Y : C₁} {f : X ⟶ Y} (c : RelativeCellComplex.{w} cell f) :
    RelativeCellComplex.{w} (fun k a => F.map (cell k a)) (F.map f) := c.map F

example {alpha : T → Type uAlpha}
    {A B : (k : T) → alpha k → C₁}
    {cell : (k : T) → (a : alpha k) → A k a ⟶ B k a}
    {X Y : C₁} {f : X ⟶ Y} (c : RelativeCellComplex.{w} cell f) :
    (c.map F).F = c.F ⋙ F := rfl

example (P : MorphismProperty C₁) (Q : MorphismProperty D₁)
    (hPQ : P ≤ Q.inverseImage F) {X Y : C₁} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f) :
    RelativeCellComplex.{w} (fun (_ : T) => Q.homFamily) (F.map f) :=
  c.mapOfLE F P Q hPQ

example (P : MorphismProperty C₁) (Q : MorphismProperty D₁)
    (hPQ : P ≤ Q.inverseImage F) {X Y : C₁} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f) :
    (c.mapOfLE F P Q hPQ).F = c.F ⋙ F := rfl

end Complexes

end IndependentHomUniverseClients

namespace IndependentCardinalTransferClients

universe vC vD t

variable {C₁ : Type uC} [Category.{vC} C₁]
  {D₁ : Type uD} [Category.{vD} D₁]
  (F : C₁ ⥤ D₁) [F.Full] [F.Faithful]
  (P : MorphismProperty C₁) (Q : MorphismProperty D₁)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsSmall.{w}] [LocallySmall.{w} C₁]
  [HasPushouts C₁] [HasCoproducts.{w} C₁]
  [HasIterationOfShape κ.ord.ToType C₁]
  [PreservesColimitsOfSize.{w, w} F] [Q.IsCardinalForSmallObjectArgument κ]
  (hPQ : P ≤ Q.inverseImage F)

example : P.IsCardinalForSmallObjectArgument κ :=
  MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful F P Q κ hPQ

example :
    letI : P.IsCardinalForSmallObjectArgument κ :=
      MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful F P Q κ hPQ
    P.IsSmall.{w} ∧ LocallySmall.{w} C₁ ∧ HasPushouts C₁ ∧ HasCoproducts.{w} C₁ ∧
      HasIterationOfShape κ.ord.ToType C₁ := by
  let _ : P.IsCardinalForSmallObjectArgument κ :=
    MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful F P Q κ hPQ
  exact ⟨SmallObject.isSmall P κ, SmallObject.locallySmall P κ,
    SmallObject.hasPushouts P κ, SmallObject.hasCoproducts P κ,
    SmallObject.hasIterationOfShape P κ⟩

example {A B X Y : C₁} (i : A ⟶ B) (hi : P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => P.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) := by
  let _ : P.IsCardinalForSmallObjectArgument κ :=
    MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful F P Q κ hPQ
  exact SmallObject.preservesColimit P κ i hi f c

example {A B X Y : C₁} (i : A ⟶ B) (hi : P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => P.homFamily) f)
    [HasColimit c.F] :
    IsColimit ((coyoneda.obj (Opposite.op A)).mapCocone (colimit.cocone c.F)) := by
  let _ : P.IsCardinalForSmallObjectArgument κ :=
    MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful F P Q κ hPQ
  let _ : PreservesColimit c.F (coyoneda.obj (Opposite.op A)) :=
    SmallObject.preservesColimit P κ i hi f c
  exact isColimitOfPreserves (coyoneda.obj (Opposite.op A)) (colimit.isColimit c.F)

section OriginalMappedChain

variable {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  [PreservesColimitsOfShape T F] [PreservesWellOrderContinuousOfShape T F]

example {X Y : C₁} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun _ : T => P.homFamily) f) :
    (c.mapOfLE F P Q hPQ).F = c.F ⋙ F := rfl

example {X Y : C₁} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun _ : T => P.homFamily) f) :
    (c.mapOfLE F P Q hPQ).incl =
      (c.toTransfiniteCompositionOfShape.map F).incl := rfl

end OriginalMappedChain

end IndependentCardinalTransferClients

namespace RaisedAndNonthinCardinalClients

universe vC
variable {C₁ : Type uC} [Category.{vC} C₁]

/-- The regression uses the stock category on the raised original object type. -/
local instance raisedObjectCategory : Category.{vC} (ULift.{uC + 1} C₁) :=
  uliftCategory C₁
/-- The regression independently raises the Hom universe using the stock category. -/
local instance raisedHomCategory :
    Category.{max (vC + 1) vC} (ULiftHom.{vC + 1} (ULift.{uC + 1} C₁)) :=
  @ULiftHom.category (ULift.{uC + 1} C₁) (inferInstance : Category.{vC} (ULift.{uC + 1} C₁))

example (P : MorphismProperty C₁)
    (Q : MorphismProperty (ULiftHom.{vC + 1} (ULift.{uC + 1} C₁)))
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [P.IsSmall.{w}] [LocallySmall.{w} C₁]
    [HasPushouts C₁] [HasCoproducts.{w} C₁] [HasIterationOfShape κ.ord.ToType C₁]
    [Q.IsCardinalForSmallObjectArgument κ]
    (hPQ : P ≤ Q.inverseImage (ULiftHomULiftCategory.equiv.{vC + 1, uC + 1} C₁).functor) :
    P.IsCardinalForSmallObjectArgument κ :=
  MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful
    (ULiftHomULiftCategory.equiv.{vC + 1, uC + 1} C₁).functor P Q κ hPQ

end RaisedAndNonthinCardinalClients

/-! A concrete client: the generating map `∅ ⟶ PUnit` of `Type u`, transferred along the fully
faithful, colimit-preserving `uliftFunctor`. The target family is eligible because it is small in
the locally presentable category `Type u`, and every other hypothesis of both endpoints is found by
instance search, so neither endpoint is applied to an assumed or unsatisfiable family. -/
namespace ConcreteTypeClient

/-- The generating map `∅ ⟶ PUnit` of `Type u`. -/
def gen : PEmpty.{uC + 1} ⟶ PUnit.{uC + 1} := TypeCat.ofHom PEmpty.elim

/-- The generators: the single map `gen`. -/
abbrev P : MorphismProperty (Type uC) :=
  MorphismProperty.ofHoms (fun _ : PUnit.{uC + 1} ↦ gen.{uC})

/-- The fully faithful functor `X ↦ ULift X`, which preserves colimits. -/
abbrev F : Type uC ⥤ Type uC := uliftFunctor.{uC, uC}

/-- The target generators: the image of `gen`. -/
abbrev Q : MorphismProperty (Type uC) :=
  MorphismProperty.ofHoms (fun _ : PUnit.{uC + 1} ↦ F.{uC}.map gen.{uC})

theorem hPQ : P.{uC} ≤ Q.{uC}.inverseImage F.{uC} := by
  rintro _ _ _ ⟨i⟩
  exact MorphismProperty.ofHoms.mk i

/-- The cardinal transfer along `uliftFunctor`, at a rank where the small target family `Q` is
eligible, makes the generators eligible at that same rank. -/
theorem p_hasSmallObjectArgument : (P.{uC}).HasSmallObjectArgument.{uC} := by
  have hQ : (Q.{uC}).HasSmallObjectArgument.{uC} :=
    MorphismProperty.hasSmallObjectArgument_of_isSmall Q.{uC}
  obtain ⟨κ, _, _, _⟩ := hQ
  exact ⟨κ, inferInstance, inferInstance,
    MorphismProperty.IsCardinalForSmallObjectArgument.of_fullyFaithful
      F.{uC} P.{uC} Q.{uC} κ hPQ⟩

/-- The right classes agree along `uliftFunctor`: lifting against `F.map gen` after applying the
fully faithful `F` is lifting against `gen`. -/
theorem hrlp : P.{uC}.rlp = Q.{uC}.rlp.inverseImage F.{uC} := by
  ext X Y p
  constructor
  · rintro hp _ _ _ ⟨i⟩
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful F.{uC} gen.{uC} p).mpr
      (hp _ (MorphismProperty.ofHoms.mk i))
  · rintro hp _ _ _ ⟨i⟩
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful F.{uC} gen.{uC} p).mp
      (hp _ (MorphismProperty.ofHoms.mk i))

/-- With that eligibility, the generated left classes compare along `uliftFunctor`. -/
example : (P.{uC}).rlp.llp = (Q.{uC}).rlp.llp.inverseImage F.{uC} := by
  have := p_hasSmallObjectArgument.{uC}
  exact MorphismProperty.rlp_llp_eq_inverseImage_of_fullyFaithful F.{uC} P.{uC} Q.{uC}
    hPQ hrlp

end ConcreteTypeClient

namespace LegacySharedHomTypeGuards

variable {C₀ : Type uC} [Category.{v} C₀]
variable {D₀ : Type uD} [Category.{v} D₀]

private noncomputable def legacyAttachCellsMap
    {alpha : Type*} {A B : alpha → C₀}
    {g : (a : alpha) → A a ⟶ B a}
    {X Y : C₀} {f : X ⟶ Y}
    (c : AttachCells.{w} g f) (F : C₀ ⥤ D₀)
    [PreservesColimitsOfSize.{w, w} F] :
    AttachCells.{w} (fun a => F.map (g a)) (F.map f) := c.map F

private noncomputable def legacyRelativeCellMap
    {K : Type*} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
    {alpha : K → Type*} {A B : (k : K) → alpha k → C₀}
    {cell : (k : K) → (a : alpha k) → A k a ⟶ B k a}
    {X Y : C₀} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} cell f) (F : C₀ ⥤ D₀)
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape K F] [PreservesWellOrderContinuousOfShape K F] :
    RelativeCellComplex.{w} (fun k a => F.map (cell k a)) (F.map f) := c.map F

private noncomputable def legacyRelativeCellMapOfLE
    (F : C₀ ⥤ D₀) (P : MorphismProperty C₀) (Q : MorphismProperty D₀)
    (hPQ : P ≤ Q.inverseImage F)
    {K : Type*} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
    {X Y : C₀} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : K) => P.homFamily) f)
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape K F] [PreservesWellOrderContinuousOfShape K F] :
    RelativeCellComplex.{w} (fun (_ : K) => Q.homFamily) (F.map f) :=
  c.mapOfLE F P Q hPQ

/- The new target hom universe specializes to the exact complete old types. -/
open Lean Elab Command Meta in
set_option maxRecDepth 512 in
set_option maxHeartbeats 200000 in
run_cmd liftTermElabM do
  let pairs : Array (Name × Name) := #[
    (``HomotopicalAlgebra.AttachCells.map, ``legacyAttachCellsMap),
    (``HomotopicalAlgebra.RelativeCellComplex.map, ``legacyRelativeCellMap),
    (``HomotopicalAlgebra.RelativeCellComplex.mapOfLE, ``legacyRelativeCellMapOfLE)]
  for (actualName, legacyName) in pairs do
    let actual ← getConstInfo actualName
    let legacy ← getConstInfo legacyName
    unless actual.levelParams.contains `vD do
      throwError "{actualName} has no independent target hom universe"
    let kept := actual.levelParams.filter (fun n => n != `vD)
    unless kept.length == legacy.levelParams.length && kept.all (legacy.levelParams.contains ·) do
      throwError "{actualName} changed other universe parameters"
    let levels := actual.levelParams.map fun n => Level.param (if n == `vD then `v else n)
    let specialized := actual.type.instantiateLevelParams actual.levelParams levels
    unless ← isDefEq specialized legacy.type do
      throwError "{actualName} changed its complete legacy specialization type"
    logInfo m!"complete legacy shared-hom type preserved: {actualName}"

end LegacySharedHomTypeGuards
