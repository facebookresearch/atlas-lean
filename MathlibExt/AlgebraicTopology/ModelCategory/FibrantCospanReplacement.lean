/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Fibrant replacements of walking cospans

This file packages fibrant replacements of walking cospans and proves that their limit
comparisons with the original cospan limit are independent up to an existential weak map under
the common domain. No comparison choice is public or claimed canonical.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A fibrant replacement of a walking cospan. -/
structure FibrantCospanReplacement (D : WalkingCospan ⥤ C) where
  P : WalkingCospan ⥤ C
  unit : D ⟶ P
  isFibrant_one : IsFibrant (P.obj WalkingCospan.one)
  fibration_inl : Fibration (P.map WalkingCospan.Hom.inl)
  fibration_inr : Fibration (P.map WalkingCospan.Hom.inr)
  unit_app_mem_trivialCofibrations (j : WalkingCospan) :
    trivialCofibrations C (unit.app j)

private noncomputable def chosenFibrantCospanReplacement
    (D : WalkingCospan ⥤ C) : FibrantCospanReplacement D := by
  let d1 := factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from (D.obj WalkingCospan.one))
  let dL := factorizationData (trivialCofibrations C) (fibrations C)
    (D.map WalkingCospan.Hom.inl ≫ d1.i)
  let dR := factorizationData (trivialCofibrations C) (fibrations C)
    (D.map WalkingCospan.Hom.inr ≫ d1.i)
  let P : WalkingCospan ⥤ C := cospan dL.p dR.p
  let η : D ⟶ P := cospanHomMk d1.i dL.i dR.i dL.fac.symm dR.fac.symm
  refine
    { P := P
      unit := η
      isFibrant_one := ?_
      fibration_inl := ?_
      fibration_inr := ?_
      unit_app_mem_trivialCofibrations := ?_ }
  · change IsFibrant d1.Z
    rw [isFibrant_iff_of_isTerminal d1.p terminalIsTerminal]
    exact (fibration_iff d1.p).2 d1.hp
  · change Fibration dL.p
    exact (fibration_iff dL.p).2 dL.hp
  · change Fibration dR.p
    exact (fibration_iff dR.p).2 dR.hp
  · rintro (_ | _ | _)
    · exact d1.hi
    · exact dL.hi
    · exact dR.hi

namespace FibrantCospanReplacement

/-- Fibrant cospan replacements exist in every model category. -/
theorem nonempty (D : WalkingCospan ⥤ C) :
    Nonempty (FibrantCospanReplacement D) :=
  ⟨chosenFibrantCospanReplacement D⟩

/-! The common comparison domain is the chosen walking-cospan limit. -/

/-- The limit object of a fibrant cospan replacement. -/
noncomputable abbrev pullbackObj {D : WalkingCospan ⥤ C}
    (R : FibrantCospanReplacement D) : C :=
  limit R.P

/-- Comparison from the original cospan limit to the replacement limit. -/
noncomputable def fromPullback {D : WalkingCospan ⥤ C}
    (R : FibrantCospanReplacement D) :
    limit D ⟶ R.pullbackObj :=
  lim.map R.unit

@[reassoc]
theorem fromPullback_inl {D : WalkingCospan ⥤ C}
    (R : FibrantCospanReplacement D) :
    R.fromPullback ≫ limit.π R.P WalkingCospan.left =
      limit.π D WalkingCospan.left ≫
        R.unit.app WalkingCospan.left := by
  exact limMap_π R.unit WalkingCospan.left

@[reassoc]
theorem fromPullback_inr {D : WalkingCospan ⥤ C}
    (R : FibrantCospanReplacement D) :
    R.fromPullback ≫ limit.π R.P WalkingCospan.right =
      limit.π D WalkingCospan.right ≫
        R.unit.app WalkingCospan.right := by
  exact limMap_π R.unit WalkingCospan.right

private noncomputable def replacementCospanLimitIso (F : WalkingCospan ⥤ C) :
    limit F ≅ pullback (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr) :=
  HasLimit.isoOfNatIso (diagramIsoCospan F)

private theorem replacementCospanLimit_isPullback (F : WalkingCospan ⥤ C) :
    IsPullback (limit.π F WalkingCospan.left)
      (limit.π F WalkingCospan.right)
      (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr) :=
  IsPullback.of_isLimit_cone (limit.isLimit F)

private structure Comparison {D : WalkingCospan ⥤ C}
    (R S : FibrantCospanReplacement D) where
  hom : S.P ⟶ R.P
  fac : S.unit ≫ hom = R.unit

private noncomputable def comparison {D : WalkingCospan ⥤ C}
    (R S : FibrantCospanReplacement D) : Comparison R S := by
  have hS1 := (mem_trivialCofibrations_iff (S.unit.app WalkingCospan.one)).1
    (S.unit_app_mem_trivialCofibrations WalkingCospan.one)
  let _ : Cofibration (S.unit.app WalkingCospan.one) := hS1.1
  let _ : WeakEquivalence (S.unit.app WalkingCospan.one) := hS1.2
  let _ : Fibration (R.P.map WalkingCospan.Hom.inl) := R.fibration_inl
  let _ : Fibration (R.P.map WalkingCospan.Hom.inr) := R.fibration_inr
  let _ : IsFibrant (R.P.obj WalkingCospan.one) := R.isFibrant_one
  let sq1 : CommSq (R.unit.app WalkingCospan.one)
      (S.unit.app WalkingCospan.one) (terminal.from _) (terminal.from _) := .mk
  let z : S.P.obj WalkingCospan.one ⟶ R.P.obj WalkingCospan.one := sq1.lift
  have hSL := (mem_trivialCofibrations_iff (S.unit.app WalkingCospan.left)).1
    (S.unit_app_mem_trivialCofibrations WalkingCospan.left)
  let _ : Cofibration (S.unit.app WalkingCospan.left) := hSL.1
  let _ : WeakEquivalence (S.unit.app WalkingCospan.left) := hSL.2
  let sqL : CommSq (R.unit.app WalkingCospan.left)
      (S.unit.app WalkingCospan.left)
      (R.P.map WalkingCospan.Hom.inl)
      (S.P.map WalkingCospan.Hom.inl ≫ z) := ⟨by
        calc
          R.unit.app WalkingCospan.left ≫
                R.P.map WalkingCospan.Hom.inl =
              D.map WalkingCospan.Hom.inl ≫
                R.unit.app WalkingCospan.one :=
            (R.unit.naturality WalkingCospan.Hom.inl).symm
          _ = D.map WalkingCospan.Hom.inl ≫
                (S.unit.app WalkingCospan.one ≫ z) := by
            rw [sq1.fac_left]
          _ = (D.map WalkingCospan.Hom.inl ≫
                S.unit.app WalkingCospan.one) ≫ z :=
            (Category.assoc _ _ _).symm
          _ = (S.unit.app WalkingCospan.left ≫
                S.P.map WalkingCospan.Hom.inl) ≫ z := by
            rw [S.unit.naturality WalkingCospan.Hom.inl]
          _ = S.unit.app WalkingCospan.left ≫
                S.P.map WalkingCospan.Hom.inl ≫ z :=
            Category.assoc _ _ _⟩
  let l : S.P.obj WalkingCospan.left ⟶ R.P.obj WalkingCospan.left := sqL.lift
  have hSR := (mem_trivialCofibrations_iff (S.unit.app WalkingCospan.right)).1
    (S.unit_app_mem_trivialCofibrations WalkingCospan.right)
  let _ : Cofibration (S.unit.app WalkingCospan.right) := hSR.1
  let _ : WeakEquivalence (S.unit.app WalkingCospan.right) := hSR.2
  let sqR : CommSq (R.unit.app WalkingCospan.right)
      (S.unit.app WalkingCospan.right)
      (R.P.map WalkingCospan.Hom.inr)
      (S.P.map WalkingCospan.Hom.inr ≫ z) := ⟨by
        calc
          R.unit.app WalkingCospan.right ≫
                R.P.map WalkingCospan.Hom.inr =
              D.map WalkingCospan.Hom.inr ≫
                R.unit.app WalkingCospan.one :=
            (R.unit.naturality WalkingCospan.Hom.inr).symm
          _ = D.map WalkingCospan.Hom.inr ≫
                (S.unit.app WalkingCospan.one ≫ z) := by
            rw [sq1.fac_left]
          _ = (D.map WalkingCospan.Hom.inr ≫
                S.unit.app WalkingCospan.one) ≫ z :=
            (Category.assoc _ _ _).symm
          _ = (S.unit.app WalkingCospan.right ≫
                S.P.map WalkingCospan.Hom.inr) ≫ z := by
            rw [S.unit.naturality WalkingCospan.Hom.inr]
          _ = S.unit.app WalkingCospan.right ≫
                S.P.map WalkingCospan.Hom.inr ≫ z :=
            Category.assoc _ _ _⟩
  let r : S.P.obj WalkingCospan.right ⟶ R.P.obj WalkingCospan.right := sqR.lift
  let α : S.P ⟶ R.P := cospanHomMk z l r sqL.fac_right.symm sqR.fac_right.symm
  refine ⟨α, ?_⟩
  ext j
  rcases j with (_ | _ | _)
  · exact sq1.fac_left
  · exact sqL.fac_left
  · exact sqR.fac_left

private theorem Comparison.weakEquivalence_app {D : WalkingCospan ⥤ C}
    {R S : FibrantCospanReplacement D} (T : Comparison R S)
    (j : WalkingCospan) : WeakEquivalence (T.hom.app j) := by
  have hR := (mem_trivialCofibrations_iff (R.unit.app j)).1
    (R.unit_app_mem_trivialCofibrations j)
  have hS := (mem_trivialCofibrations_iff (S.unit.app j)).1
    (S.unit_app_mem_trivialCofibrations j)
  let _ : WeakEquivalence (R.unit.app j) := hR.2
  let _ : WeakEquivalence (S.unit.app j) := hS.2
  have hj : S.unit.app j ≫ T.hom.app j = R.unit.app j := by
    simpa using congr_app T.fac j
  exact weakEquivalence_of_precomp_of_fac hj

private theorem weakEquivalence_pullbackMap_of_fibrant
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    {u₀ : Q₀ ⟶ P₀} {v₀ : R₀ ⟶ P₀}
    {u₁ : Q₁ ⟶ P₁} {v₁ : R₁ ⟶ P₁}
    {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
    (hu : u₀ ≫ wP = wQ ≫ u₁) (hv : v₀ ≫ wP = wR ≫ v₁)
    [Fibration u₀] [Fibration u₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR]
    [IsFibrant P₀] [IsFibrant P₁] [IsFibrant R₀] [IsFibrant R₁] :
    WeakEquivalence (pullback.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) := by
  let _ : IsCofibrant (Opposite.op P₀) :=
    (isCofibrant_iff_of_isInitial (terminal.from P₀).op terminalIsTerminal.op).2 (by
      rw [cofibration_op_iff]
      exact inferInstance)
  let _ : IsCofibrant (Opposite.op P₁) :=
    (isCofibrant_iff_of_isInitial (terminal.from P₁).op terminalIsTerminal.op).2 (by
      rw [cofibration_op_iff]
      exact inferInstance)
  let _ : IsCofibrant (Opposite.op R₀) :=
    (isCofibrant_iff_of_isInitial (terminal.from R₀).op terminalIsTerminal.op).2 (by
      rw [cofibration_op_iff]
      exact inferInstance)
  let _ : IsCofibrant (Opposite.op R₁) :=
    (isCofibrant_iff_of_isInitial (terminal.from R₁).op terminalIsTerminal.op).2 (by
      rw [cofibration_op_iff]
      exact inferInstance)
  let _ : WeakEquivalence wP.op := (weakEquivalences_op_iff wP).2 inferInstance
  let _ : WeakEquivalence wQ.op := (weakEquivalences_op_iff wQ).2 inferInstance
  let _ : WeakEquivalence wR.op := (weakEquivalences_op_iff wR).2 inferInstance
  have hPush : WeakEquivalence
      (pushout.map u₁.op v₁.op u₀.op v₀.op wQ.op wR.op wP.op
        (by simpa only [← op_comp] using congrArg Quiver.Hom.op hu.symm)
        (by simpa only [← op_comp] using congrArg Quiver.Hom.op hv.symm)) := by
    apply weakEquivalence_pushoutMap_of_cofibrant
  rw [← weakEquivalences_op_iff,
    op_pullbackMap u₀ v₀ u₁ v₁ wQ wR wP hu hv]
  infer_instance

private noncomputable def Comparison.pullbackMap {D : WalkingCospan ⥤ C}
    {R S : FibrantCospanReplacement D} (T : Comparison R S) :
    S.pullbackObj ⟶ R.pullbackObj :=
  lim.map T.hom

private theorem Comparison.weakEquivalence_pullbackMap
    {D : WalkingCospan ⥤ C} {R S : FibrantCospanReplacement D}
    (T : Comparison R S) : WeakEquivalence T.pullbackMap := by
  let _ : IsFibrant (S.P.obj WalkingCospan.one) := S.isFibrant_one
  let _ : IsFibrant (R.P.obj WalkingCospan.one) := R.isFibrant_one
  let _ : Fibration (S.P.map WalkingCospan.Hom.inl) := S.fibration_inl
  let _ : Fibration (S.P.map WalkingCospan.Hom.inr) := S.fibration_inr
  let _ : Fibration (R.P.map WalkingCospan.Hom.inl) := R.fibration_inl
  let _ : Fibration (R.P.map WalkingCospan.Hom.inr) := R.fibration_inr
  let _ : IsFibrant (S.P.obj WalkingCospan.right) :=
    isFibrant_of_fibration (S.P.map WalkingCospan.Hom.inr)
  let _ : IsFibrant (R.P.obj WalkingCospan.right) :=
    isFibrant_of_fibration (R.P.map WalkingCospan.Hom.inr)
  let _ : WeakEquivalence (T.hom.app WalkingCospan.one) :=
    T.weakEquivalence_app WalkingCospan.one
  let _ : WeakEquivalence (T.hom.app WalkingCospan.left) :=
    T.weakEquivalence_app WalkingCospan.left
  let _ : WeakEquivalence (T.hom.app WalkingCospan.right) :=
    T.weakEquivalence_app WalkingCospan.right
  let m := pullback.map
    (S.P.map WalkingCospan.Hom.inl) (S.P.map WalkingCospan.Hom.inr)
    (R.P.map WalkingCospan.Hom.inl) (R.P.map WalkingCospan.Hom.inr)
    (T.hom.app WalkingCospan.left) (T.hom.app WalkingCospan.right)
    (T.hom.app WalkingCospan.one)
    (T.hom.naturality WalkingCospan.Hom.inl)
    (T.hom.naturality WalkingCospan.Hom.inr)
  let _ : WeakEquivalence m := weakEquivalence_pullbackMap_of_fibrant
    (T.hom.naturality WalkingCospan.Hom.inl)
    (T.hom.naturality WalkingCospan.Hom.inr)
  let eS := replacementCospanLimitIso S.P
  let eR := replacementCospanLimitIso R.P
  have heSLeft : eS.hom ≫
      pullback.fst (S.P.map WalkingCospan.Hom.inl)
        (S.P.map WalkingCospan.Hom.inr) =
      limit.π S.P WalkingCospan.left := by
    simp [eS, replacementCospanLimitIso]
  have heSRight : eS.hom ≫
      pullback.snd (S.P.map WalkingCospan.Hom.inl)
        (S.P.map WalkingCospan.Hom.inr) =
      limit.π S.P WalkingCospan.right := by
    simp [eS, replacementCospanLimitIso]
  have heRLeft : eR.inv ≫ limit.π R.P WalkingCospan.left =
      pullback.fst (R.P.map WalkingCospan.Hom.inl)
        (R.P.map WalkingCospan.Hom.inr) := by
    simp [eR, replacementCospanLimitIso]
  have heRRight : eR.inv ≫ limit.π R.P WalkingCospan.right =
      pullback.snd (R.P.map WalkingCospan.Hom.inl)
        (R.P.map WalkingCospan.Hom.inr) := by
    simp [eR, replacementCospanLimitIso]
  have hmLeft : m ≫
      pullback.fst (R.P.map WalkingCospan.Hom.inl)
        (R.P.map WalkingCospan.Hom.inr) =
      pullback.fst (S.P.map WalkingCospan.Hom.inl)
          (S.P.map WalkingCospan.Hom.inr) ≫
        T.hom.app WalkingCospan.left := by
    dsimp [m]
    apply pullback.lift_fst
  have hmRight : m ≫
      pullback.snd (R.P.map WalkingCospan.Hom.inl)
        (R.P.map WalkingCospan.Hom.inr) =
      pullback.snd (S.P.map WalkingCospan.Hom.inl)
          (S.P.map WalkingCospan.Hom.inr) ≫
        T.hom.app WalkingCospan.right := by
    dsimp [m]
    apply pullback.lift_snd
  have hlimLeft : T.pullbackMap ≫ limit.π R.P WalkingCospan.left =
      limit.π S.P WalkingCospan.left ≫
        T.hom.app WalkingCospan.left := by
    exact limMap_π T.hom WalkingCospan.left
  have hlimRight : T.pullbackMap ≫ limit.π R.P WalkingCospan.right =
      limit.π S.P WalkingCospan.right ≫
        T.hom.app WalkingCospan.right := by
    exact limMap_π T.hom WalkingCospan.right
  have h : T.pullbackMap = eS.hom ≫ m ≫ eR.inv := by
    apply (replacementCospanLimit_isPullback R.P).hom_ext
    · rw [hlimLeft]
      symm
      simp only [Category.assoc, heRLeft, hmLeft]
      rw [← Category.assoc, heSLeft]
    · rw [hlimRight]
      symm
      simp only [Category.assoc, heRRight, hmRight]
      rw [← Category.assoc, heSRight]
  rw [h]
  infer_instance

private theorem Comparison.fromPullback_pullbackMap
    {D : WalkingCospan ⥤ C} {R S : FibrantCospanReplacement D}
    (T : Comparison R S) : S.fromPullback ≫ T.pullbackMap = R.fromPullback := by
  change lim.map S.unit ≫ lim.map T.hom = lim.map R.unit
  rw [← lim.map_comp, T.fac]

/-- Two arbitrary fibrant cospan replacements have a weak comparison under
the ordinary pullback. -/
theorem exists_weakEquivalence_pullbackObj {D : WalkingCospan ⥤ C}
    (R S : FibrantCospanReplacement D) :
    ∃ f : S.pullbackObj ⟶ R.pullbackObj,
      WeakEquivalence f ∧ S.fromPullback ≫ f = R.fromPullback := by
  let T := comparison R S
  exact ⟨T.pullbackMap, T.weakEquivalence_pullbackMap,
    T.fromPullback_pullbackMap⟩

/-- Weakness of the comparison from the ordinary pullback is independent of
the chosen fibrant cospan replacement. -/
theorem weakEquivalence_fromPullback_iff {D : WalkingCospan ⥤ C}
    (R S : FibrantCospanReplacement D) :
    WeakEquivalence R.fromPullback ↔ WeakEquivalence S.fromPullback := by
  obtain ⟨f, hf, hfac⟩ := exists_weakEquivalence_pullbackObj R S
  let _ : WeakEquivalence f := hf
  constructor
  · intro hR
    let _ : WeakEquivalence R.fromPullback := hR
    have : WeakEquivalence (S.fromPullback ≫ f) := by
      rw [hfac]
      infer_instance
    exact weakEquivalence_of_postcomp S.fromPullback f
  · intro hS
    let _ : WeakEquivalence S.fromPullback := hS
    have : WeakEquivalence (S.fromPullback ≫ f) := by infer_instance
    rw [hfac] at this
    exact this

end FibrantCospanReplacement

end HomotopicalAlgebra
