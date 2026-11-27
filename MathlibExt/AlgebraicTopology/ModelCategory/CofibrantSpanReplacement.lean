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

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Cofibrant replacements of walking spans

This file packages cofibrant replacements of walking spans and proves that their colimit
comparisons with the original span colimit are independent up to an existential weak map over the
common codomain. No comparison choice is public or claimed canonical.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A cofibrant replacement of a walking span. -/
structure CofibrantSpanReplacement (D : WalkingSpan ⥤ C) where
  /-- The complete replacement span. -/
  Q : WalkingSpan ⥤ C
  /-- The full natural comparison to the original span. -/
  counit : Q ⟶ D
  isCofibrant_zero : IsCofibrant (Q.obj WalkingSpan.zero)
  cofibration_fst : Cofibration (Q.map WalkingSpan.Hom.fst)
  cofibration_snd : Cofibration (Q.map WalkingSpan.Hom.snd)
  counit_app_mem_trivialFibrations (j : WalkingSpan) :
    trivialFibrations C (counit.app j)

private noncomputable def chosenCofibrantSpanReplacement
    (D : WalkingSpan ⥤ C) : CofibrantSpanReplacement D := by
  let d0 := factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to (D.obj WalkingSpan.zero))
  let dL := factorizationData (cofibrations C) (trivialFibrations C)
    (d0.p ≫ D.map WalkingSpan.Hom.fst)
  let dR := factorizationData (cofibrations C) (trivialFibrations C)
    (d0.p ≫ D.map WalkingSpan.Hom.snd)
  let Q : WalkingSpan ⥤ C := span dL.i dR.i
  let q : Q ⟶ D := spanHomMk d0.p dL.p dR.p dL.fac dR.fac
  refine
    { Q := Q
      counit := q
      isCofibrant_zero := ?_
      cofibration_fst := ?_
      cofibration_snd := ?_
      counit_app_mem_trivialFibrations := ?_ }
  · change IsCofibrant d0.Z
    rw [isCofibrant_iff_of_isInitial d0.i initialIsInitial]
    exact (cofibration_iff d0.i).2 d0.hi
  · change Cofibration dL.i
    exact (cofibration_iff dL.i).2 dL.hi
  · change Cofibration dR.i
    exact (cofibration_iff dR.i).2 dR.hi
  · rintro (_ | _ | _)
    · exact d0.hp
    · exact dL.hp
    · exact dR.hp

namespace CofibrantSpanReplacement

/-- Cofibrant span replacements exist in every model category. -/
theorem nonempty (D : WalkingSpan ⥤ C) :
    Nonempty (CofibrantSpanReplacement D) :=
  ⟨chosenCofibrantSpanReplacement D⟩

/-! The common comparison codomain is the chosen walking-span colimit. -/

/-- The colimit object of a cofibrant span replacement. -/
noncomputable abbrev pushoutObj {D : WalkingSpan ⥤ C}
    (R : CofibrantSpanReplacement D) : C :=
  colimit R.Q

/-- Comparison from the replacement colimit to the original span colimit. -/
noncomputable def toPushout {D : WalkingSpan ⥤ C}
    (R : CofibrantSpanReplacement D) :
    R.pushoutObj ⟶ colimit D :=
  colim.map R.counit

@[reassoc]
theorem inl_toPushout {D : WalkingSpan ⥤ C}
    (R : CofibrantSpanReplacement D) :
    colimit.ι R.Q WalkingSpan.left ≫ R.toPushout =
      R.counit.app WalkingSpan.left ≫
        colimit.ι D WalkingSpan.left := by
  exact ι_colimMap R.counit WalkingSpan.left

@[reassoc]
theorem inr_toPushout {D : WalkingSpan ⥤ C}
    (R : CofibrantSpanReplacement D) :
    colimit.ι R.Q WalkingSpan.right ≫ R.toPushout =
      R.counit.app WalkingSpan.right ≫
        colimit.ι D WalkingSpan.right := by
  exact ι_colimMap R.counit WalkingSpan.right

private noncomputable def replacementSpanColimitIso (F : WalkingSpan ⥤ C) :
    colimit F ≅
      pushout (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) :=
  HasColimit.isoOfNatIso (diagramIsoSpan F)

private theorem replacementSpanColimitIso_left (F : WalkingSpan ⥤ C) :
    colimit.ι F WalkingSpan.left ≫ (replacementSpanColimitIso F).hom =
      pushout.inl (F.map WalkingSpan.Hom.fst)
        (F.map WalkingSpan.Hom.snd) := by
  simp [replacementSpanColimitIso]

private theorem replacementSpanColimitIso_right (F : WalkingSpan ⥤ C) :
    colimit.ι F WalkingSpan.right ≫ (replacementSpanColimitIso F).hom =
      pushout.inr (F.map WalkingSpan.Hom.fst)
        (F.map WalkingSpan.Hom.snd) := by
  simp [replacementSpanColimitIso]

private theorem replacementSpanColimit_isPushout (F : WalkingSpan ⥤ C) :
    IsPushout (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
      (colimit.ι F WalkingSpan.left)
      (colimit.ι F WalkingSpan.right) := by
  apply IsPushout.of_iso
    (IsPushout.of_hasPushout
      (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (replacementSpanColimitIso F).symm
  · simp
  · simp
  · simpa using
      (Iso.comp_inv_eq (replacementSpanColimitIso F)).2
        (replacementSpanColimitIso_left F).symm
  · simpa using
      (Iso.comp_inv_eq (replacementSpanColimitIso F)).2
        (replacementSpanColimitIso_right F).symm

private structure Comparison {D : WalkingSpan ⥤ C}
    (R S : CofibrantSpanReplacement D) where
  hom : R.Q ⟶ S.Q
  fac : hom ≫ S.counit = R.counit

private noncomputable def comparison {D : WalkingSpan ⥤ C}
    (R S : CofibrantSpanReplacement D) : Comparison R S := by
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
  have hS0 := (mem_trivialFibrations_iff (S.counit.app WalkingSpan.zero)).1
    (S.counit_app_mem_trivialFibrations WalkingSpan.zero)
  let _ : Fibration (S.counit.app WalkingSpan.zero) := hS0.1
  let _ : WeakEquivalence (S.counit.app WalkingSpan.zero) := hS0.2
  let sq0 : CommSq (initial.to _) (initial.to _)
      (S.counit.app WalkingSpan.zero)
      (R.counit.app WalkingSpan.zero) := .mk
  let z : R.Q.obj WalkingSpan.zero ⟶ S.Q.obj WalkingSpan.zero := sq0.lift
  have hSL := (mem_trivialFibrations_iff (S.counit.app WalkingSpan.left)).1
    (S.counit_app_mem_trivialFibrations WalkingSpan.left)
  let _ : Fibration (S.counit.app WalkingSpan.left) := hSL.1
  let _ : WeakEquivalence (S.counit.app WalkingSpan.left) := hSL.2
  let sqL : CommSq (z ≫ S.Q.map WalkingSpan.Hom.fst)
      (R.Q.map WalkingSpan.Hom.fst) (S.counit.app WalkingSpan.left)
      (R.counit.app WalkingSpan.left) := ⟨by
        rw [Category.assoc, S.counit.naturality,
          ← Category.assoc, sq0.fac_right, R.counit.naturality]⟩
  let l : R.Q.obj WalkingSpan.left ⟶ S.Q.obj WalkingSpan.left := sqL.lift
  have hSR := (mem_trivialFibrations_iff (S.counit.app WalkingSpan.right)).1
    (S.counit_app_mem_trivialFibrations WalkingSpan.right)
  let _ : Fibration (S.counit.app WalkingSpan.right) := hSR.1
  let _ : WeakEquivalence (S.counit.app WalkingSpan.right) := hSR.2
  let sqR : CommSq (z ≫ S.Q.map WalkingSpan.Hom.snd)
      (R.Q.map WalkingSpan.Hom.snd) (S.counit.app WalkingSpan.right)
      (R.counit.app WalkingSpan.right) := ⟨by
        rw [Category.assoc, S.counit.naturality,
          ← Category.assoc, sq0.fac_right, R.counit.naturality]⟩
  let r : R.Q.obj WalkingSpan.right ⟶ S.Q.obj WalkingSpan.right := sqR.lift
  let α : R.Q ⟶ S.Q := spanHomMk z l r sqL.fac_left sqR.fac_left
  refine ⟨α, ?_⟩
  ext j
  rcases j with (_ | _ | _)
  · exact sq0.fac_right
  · exact sqL.fac_right
  · exact sqR.fac_right

private theorem Comparison.weakEquivalence_app {D : WalkingSpan ⥤ C}
    {R S : CofibrantSpanReplacement D} (T : Comparison R S)
    (j : WalkingSpan) : WeakEquivalence (T.hom.app j) := by
  have hR := (mem_trivialFibrations_iff (R.counit.app j)).1
    (R.counit_app_mem_trivialFibrations j)
  have hS := (mem_trivialFibrations_iff (S.counit.app j)).1
    (S.counit_app_mem_trivialFibrations j)
  let _ : WeakEquivalence (R.counit.app j) := hR.2
  let _ : WeakEquivalence (S.counit.app j) := hS.2
  have hj : T.hom.app j ≫ S.counit.app j = R.counit.app j := by
    simpa using congr_app T.fac j
  exact weakEquivalence_of_postcomp_of_fac hj

private noncomputable def Comparison.pushoutMap {D : WalkingSpan ⥤ C}
    {R S : CofibrantSpanReplacement D} (T : Comparison R S) :
    R.pushoutObj ⟶ S.pushoutObj :=
  colim.map T.hom

private theorem Comparison.weakEquivalence_pushoutMap
    {D : WalkingSpan ⥤ C} {R S : CofibrantSpanReplacement D}
    (T : Comparison R S) : WeakEquivalence T.pushoutMap := by
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : IsCofibrant (S.Q.obj WalkingSpan.zero) := S.isCofibrant_zero
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
  let _ : Cofibration (S.Q.map WalkingSpan.Hom.fst) := S.cofibration_fst
  let _ : Cofibration (S.Q.map WalkingSpan.Hom.snd) := S.cofibration_snd
  let _ : IsCofibrant (R.Q.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (R.Q.map WalkingSpan.Hom.snd)
  let _ : IsCofibrant (S.Q.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (S.Q.map WalkingSpan.Hom.snd)
  let _ : WeakEquivalence (T.hom.app WalkingSpan.zero) :=
    T.weakEquivalence_app WalkingSpan.zero
  let _ : WeakEquivalence (T.hom.app WalkingSpan.left) :=
    T.weakEquivalence_app WalkingSpan.left
  let _ : WeakEquivalence (T.hom.app WalkingSpan.right) :=
    T.weakEquivalence_app WalkingSpan.right
  change WeakEquivalence (colim.map T.hom)
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (replacementSpanColimit_isPushout R.Q)
    (replacementSpanColimit_isPushout S.Q)
    (T.hom.naturality WalkingSpan.Hom.fst)
    (T.hom.naturality WalkingSpan.Hom.snd)
    (ι_colimMap T.hom WalkingSpan.left)
    (ι_colimMap T.hom WalkingSpan.right)

private theorem Comparison.pushoutMap_toPushout
    {D : WalkingSpan ⥤ C} {R S : CofibrantSpanReplacement D}
    (T : Comparison R S) : T.pushoutMap ≫ S.toPushout = R.toPushout := by
  change colim.map T.hom ≫ colim.map S.counit = colim.map R.counit
  rw [← colim.map_comp, T.fac]

/-- Two arbitrary cofibrant span replacements admit a weak comparison over
the ordinary pushout. -/
theorem exists_weakEquivalence_pushoutObj {D : WalkingSpan ⥤ C}
    (R S : CofibrantSpanReplacement D) :
    ∃ f : R.pushoutObj ⟶ S.pushoutObj,
      WeakEquivalence f ∧ f ≫ S.toPushout = R.toPushout := by
  let T := comparison R S
  exact ⟨T.pushoutMap, T.weakEquivalence_pushoutMap,
    T.pushoutMap_toPushout⟩

/-- Weakness of the comparison to the ordinary pushout is independent of
the chosen cofibrant span replacement. -/
theorem weakEquivalence_toPushout_iff {D : WalkingSpan ⥤ C}
    (R S : CofibrantSpanReplacement D) :
    WeakEquivalence R.toPushout ↔ WeakEquivalence S.toPushout := by
  obtain ⟨f, hf, hfac⟩ := exists_weakEquivalence_pushoutObj R S
  let _ : WeakEquivalence f := hf
  constructor
  · intro hR
    let _ : WeakEquivalence R.toPushout := hR
    have : WeakEquivalence (f ≫ S.toPushout) := by
      rw [hfac]
      infer_instance
    exact weakEquivalence_of_precomp f S.toPushout
  · intro hS
    let _ : WeakEquivalence S.toPushout := hS
    have : WeakEquivalence (f ≫ S.toPushout) := by infer_instance
    rw [hfac] at this
    exact this

end CofibrantSpanReplacement

end HomotopicalAlgebra
