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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.FinCases

/-!
# Canonical degree-one Waldhausen stage functor

Forward-direction foundation for the blueprint theorem `C ≌ Stage C 1`:
the forward functor `stageOne` from `C` to `Stage C 1` whose interval `(0, 1)` value
is the input object and whose diagonal values are the chosen zero object.
This assignment stops before packaging the equivalence.

Reuses `Ar`, `interval`, `diag`, `horiz`, `vert`, `IsStage`, `Stage`,
`stageProperty`, and `ObjectProperty.FullSubcategory.lift`/`homMk`;
`WaldhausenCategoryWithoutGluing.zero_isCofibration`, identity-cofibration via
`MorphismProperty.id_mem`, the existing `IsCofibrationSequence`/pushout
APIs (`IsPushout.of_id_fst`, `IsPushout.of_id_snd`), `Arrow.mk`,
`Arrow.homMk'`, `homOfLE`/`leOfHom`, and finite-index case analysis.

The two nontrivial degree-one triples reduce to the zero-to-`X` identity
sequence and the identity-to-zero sequence, preserving the actual
orientation. No `C ≌ Stage C 1` theorem, simplicial object, nerve,
realization, or K/G-theory definition is claimed yet.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Object assignment for the degree-one stage diagram: diagonals map to the
chosen zero object, the unique off-diagonal interval maps to `X`. -/
noncomputable def stageOneDiagramObj (X : C) (A : Ar 1) : C :=
  if A.left = A.right then (0 : C) else X

omit [WaldhausenCategoryWithoutGluing C] in
/-- A diagonal `Ar 1` object is sent to the chosen zero object. -/
theorem stageOneDiagramObj_of_eq (X : C) {A : Ar 1} (h : A.left = A.right) :
    stageOneDiagramObj C X A = (0 : C) := by
  simp [stageOneDiagramObj, h]

omit [WaldhausenCategoryWithoutGluing C] in
/-- An off-diagonal `Ar 1` object is sent to the input object. -/
theorem stageOneDiagramObj_of_ne (X : C) {A : Ar 1} (h : ¬ A.left = A.right) :
    stageOneDiagramObj C X A = X := by
  simp [stageOneDiagramObj, h]

/-- Every `Ar 1` object is diagonal or the `(0, 1)` interval. -/
theorem ar1_zero_one_of_ne {A : Ar 1} (hne : ¬ A.left = A.right) :
    A.left = 0 ∧ A.right = 1 := by
  cases A with
  | mk l r h =>
    have hne' : ¬ l = r := by simpa using hne
    have hle : l ≤ r := leOfHom h
    have hend : l = 0 ∧ r = 1 := by
      fin_cases l <;> fin_cases r <;> simp_all
    exact hend

/-- Every off-diagonal `Ar 1` object is the unique `(0, 1)` interval. -/
theorem ar1_eq_interval01_of_ne {A : Ar 1} (hne : ¬ A.left = A.right) :
    A = interval (0 : Fin 2) 1 (by decide) := by
  cases A with
  | mk l r h =>
    have hend : l = 0 ∧ r = 1 := by
      simpa using ar1_zero_one_of_ne hne
    obtain ⟨h0, h1⟩ := hend
    subst h0
    subst h1
    have hhom : h = homOfLE (by decide : (0 : Fin 2) ≤ 1) := Subsingleton.elim _ _
    subst hhom
    rfl

/-- Morphism assignment: `𝟙` on like-to-like values, the unique zero leg
otherwise, via `(isZero_zero _).to_`/`from_`. -/
noncomputable def stageOneDiagramMap (X : C) {A B : Ar 1} (_φ : A ⟶ B) :
    stageOneDiagramObj C X A ⟶ stageOneDiagramObj C X B := by
  by_cases ha : A.left = A.right
  · by_cases hb : B.left = B.right
    · rw [stageOneDiagramObj_of_eq C X ha, stageOneDiagramObj_of_eq C X hb]
      exact 𝟙 (0 : C)
    · rw [stageOneDiagramObj_of_eq C X ha, stageOneDiagramObj_of_ne C X hb]
      exact (isZero_zero C).to_ X
  · by_cases hb : B.left = B.right
    · rw [stageOneDiagramObj_of_ne C X ha, stageOneDiagramObj_of_eq C X hb]
      exact (isZero_zero C).from_ X
    · rw [stageOneDiagramObj_of_ne C X ha, stageOneDiagramObj_of_ne C X hb]
      exact 𝟙 X

/-- Canonical degree-one diagram with `(0, 1)` value `X` and zero diagonals. -/
noncomputable def stageOneDiagram (X : C) : Ar 1 ⥤ C where
  obj := stageOneDiagramObj C X
  map := stageOneDiagramMap C X
  map_id A := by
    by_cases ha : A.left = A.right
    · have hObj : stageOneDiagramObj C X A = (0 : C) :=
        stageOneDiagramObj_of_eq C X ha
      have hZ : IsZero (stageOneDiagramObj C X A) := hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne ha
      subst hA
      rfl
  map_comp {A B D} φ ψ := by
    by_cases ha : A.left = A.right
    · by_cases hb : B.left = B.right
      · by_cases hd : D.left = D.right
        · have hA : stageOneDiagramObj C X A = (0 : C) :=
            stageOneDiagramObj_of_eq C X ha
          have hZ : IsZero (stageOneDiagramObj C X A) :=
            hA.symm ▸ isZero_zero C
          exact hZ.eq_of_src _ _
        · have hA : stageOneDiagramObj C X A = (0 : C) :=
            stageOneDiagramObj_of_eq C X ha
          have hZ : IsZero (stageOneDiagramObj C X A) :=
            hA.symm ▸ isZero_zero C
          exact hZ.eq_of_src _ _
      · by_cases hd : D.left = D.right
        · have hA : stageOneDiagramObj C X A = (0 : C) :=
            stageOneDiagramObj_of_eq C X ha
          have hZ : IsZero (stageOneDiagramObj C X A) :=
            hA.symm ▸ isZero_zero C
          exact hZ.eq_of_src _ _
        · have hA : stageOneDiagramObj C X A = (0 : C) :=
            stageOneDiagramObj_of_eq C X ha
          have hZ : IsZero (stageOneDiagramObj C X A) :=
            hA.symm ▸ isZero_zero C
          exact hZ.eq_of_src _ _
    · by_cases hb : B.left = B.right
      · by_cases hd : D.left = D.right
        · have hD : stageOneDiagramObj C X D = (0 : C) :=
            stageOneDiagramObj_of_eq C X hd
          have hZ : IsZero (stageOneDiagramObj C X D) :=
            hD.symm ▸ isZero_zero C
          exact hZ.eq_of_tgt _ _
        · exfalso
          obtain ⟨hA0, hA1⟩ := ar1_zero_one_of_ne ha
          obtain ⟨hD0, hD1⟩ := ar1_zero_one_of_ne hd
          have hφR : A.right ≤ B.right := leOfHom φ.right
          have hψL : B.left ≤ D.left := leOfHom ψ.left
          have h1B : (1 : Fin 2) ≤ B.right := hA1 ▸ hφR
          have hB0 : B.left ≤ (0 : Fin 2) := hD0 ▸ hψL
          have hBt : B.right = B.left := hb.symm
          rw [hBt] at h1B
          have h10 : (1 : Fin 2) ≤ (0 : Fin 2) := le_trans h1B hB0
          have hF : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)) := by decide
          exact hF h10
      · by_cases hd : D.left = D.right
        · have hD : stageOneDiagramObj C X D = (0 : C) :=
            stageOneDiagramObj_of_eq C X hd
          have hZ : IsZero (stageOneDiagramObj C X D) :=
            hD.symm ▸ isZero_zero C
          exact hZ.eq_of_tgt _ _
        · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
            ar1_eq_interval01_of_ne ha
          have hB : B = interval (0 : Fin 2) 1 (by decide) :=
            ar1_eq_interval01_of_ne hb
          have hD : D = interval (0 : Fin 2) 1 (by decide) :=
            ar1_eq_interval01_of_ne hd
          subst hA
          subst hB
          subst hD
          have hφ : φ = 𝟙 _ :=
            Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
          have hψ : ψ = 𝟙 _ :=
            Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
          subst hφ
          subst hψ
          have hArg : (𝟙 (interval (0 : Fin 2) 1 (by decide)) ≫ 𝟙 _) = 𝟙 _ := by
            simp
          have hM : stageOneDiagramMap C X
              (𝟙 (interval (0 : Fin 2) 1 (by decide))) = 𝟙 X := rfl
          rw [hArg, hM]
          exact (Category.id_comp _).symm

omit [WaldhausenCategoryWithoutGluing C] in
/-- The diagram sends every diagonal to the chosen zero object. -/
theorem stageOneDiagram_diag (X : C) (i : Fin 2) :
    (stageOneDiagram C X).obj (diag i) = (0 : C) := by
  simp [stageOneDiagram, stageOneDiagramObj, diag, interval]

omit [WaldhausenCategoryWithoutGluing C] in
/-- The diagram sends the `(0, 1)` interval to `X`. -/
theorem stageOneDiagram_interval_zero_one (X : C)
    (h : (0 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).obj (interval 0 1 h) = X := by
  have h01 : ¬ (0 : Fin 2) = 1 := by decide
  simp [stageOneDiagram, stageOneDiagramObj, interval, h01]

omit [WaldhausenCategoryWithoutGluing C] in
/-- Image of the `(0, 0, 1)` horizontal leg: the zero-to-`X` map. -/
theorem stageOneDiagram_horiz_zero_zero_one (X : C)
    (h00 : (0 : Fin 2) ≤ 0) (h01 : (0 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).map (horiz h00 h01) = (isZero_zero C).to_ X := by
  rfl

omit [WaldhausenCategoryWithoutGluing C] in
/-- Image of the `(0, 0, 1)` vertical leg: the identity on `X`. -/
theorem stageOneDiagram_vert_zero_zero_one (X : C)
    (h00 : (0 : Fin 2) ≤ 0) (h01 : (0 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).map (vert h00 h01) = 𝟙 X := by
  rfl

omit [WaldhausenCategoryWithoutGluing C] in
/-- Image of the `(0, 1, 1)` horizontal leg: the identity on `X`. -/
theorem stageOneDiagram_horiz_zero_one_one (X : C)
    (h01 : (0 : Fin 2) ≤ 1) (h11 : (1 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).map (horiz h01 h11) = 𝟙 X := by
  rfl

omit [WaldhausenCategoryWithoutGluing C] in
/-- Image of the `(0, 1, 1)` vertical leg: the `X`-to-zero map. -/
theorem stageOneDiagram_vert_zero_one_one (X : C)
    (h01 : (0 : Fin 2) ≤ 1) (h11 : (1 : Fin 2) ≤ 1) :
    (stageOneDiagram C X).map (vert h01 h11) = (isZero_zero C).from_ X := by
  rfl

/-- The degree-one diagram is a finite stage: diagonals are zero and every
non-strict triple is a cofibration sequence. The `(0, 0, 1)` triple is the
zero-to-`X` identity sequence; the `(0, 1, 1)` triple is the identity-to-zero
sequence; diagonal triples use the identity sequence on zero. -/
theorem isStage_stageOneDiagram (X : C) : IsStage 1 (stageOneDiagram C X) where
  diag_isZero i := by
    rw [stageOneDiagram_diag]
    exact isZero_zero C
  cofiber_triple {i j k} hij hjk := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · have eH : (stageOneDiagram C X).map (horiz hij hjk) = 𝟙 (0 : C) := by
        rfl
      have eV : (stageOneDiagram C X).map (vert hij hjk) = 𝟙 (0 : C) := by
        rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩
    · have eH := stageOneDiagram_horiz_zero_zero_one C X hij hjk
      have eV := stageOneDiagram_vert_zero_zero_one C X hij hjk
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), (isZero_zero C).to_ X, IsPushout.of_id_fst⟩
    · have hF : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)) := by decide
      exact False.elim (hF hjk)
    · have eH := stageOneDiagram_horiz_zero_one_one C X hij hjk
      have eV := stageOneDiagram_vert_zero_one_one C X hij hjk
      rw [eH, eV]
      exact ⟨MorphismProperty.id_mem (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _,
        (isZero_zero C).from_ X, 𝟙 (0 : C), IsPushout.of_id_snd⟩
    · have hF : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)) := by decide
      exact False.elim (hF hij)
    · have hF : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)) := by decide
      exact False.elim (hF hij)
    · have hF : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)) := by decide
      exact False.elim (hF hjk)
    · have eH : (stageOneDiagram C X).map (horiz hij hjk) = 𝟙 (0 : C) := by
        rfl
      have eV : (stageOneDiagram C X).map (vert hij hjk) = 𝟙 (0 : C) := by
        rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩

/-- Functoriality in `X`: identities on diagonals, `f` on `(0, 1)`. -/
noncomputable def stageOneDiagramFunctor : C ⥤ (Ar 1 ⥤ C) where
  obj X := stageOneDiagram C X
  map {X Y} f := NatTrans.mk (fun A => by
    by_cases ha : A.left = A.right
    · have hX : (stageOneDiagram C X).obj A = (0 : C) := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      have hY : (stageOneDiagram C Y).obj A = (0 : C) := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      rw [hX, hY]
      exact 𝟙 (0 : C)
    · have hX : (stageOneDiagram C X).obj A = X := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      have hY : (stageOneDiagram C Y).obj A = Y := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      rw [hX, hY]
      exact f) (fun {A B} φ => by
    by_cases ha : A.left = A.right
    · by_cases hb : B.left = B.right
      · have hASrc : (stageOneDiagram C X).obj A = (0 : C) :=
          stageOneDiagramObj_of_eq C X ha
        have hZ : IsZero ((stageOneDiagram C X).obj A) :=
          hASrc.symm ▸ isZero_zero C
        exact hZ.eq_of_src _ _
      · have hASrc : (stageOneDiagram C X).obj A = (0 : C) :=
          stageOneDiagramObj_of_eq C X ha
        have hZ : IsZero ((stageOneDiagram C X).obj A) :=
          hASrc.symm ▸ isZero_zero C
        exact hZ.eq_of_src _ _
    · by_cases hb : B.left = B.right
      · have hBTgt : (stageOneDiagram C Y).obj B = (0 : C) :=
          stageOneDiagramObj_of_eq C Y hb
        have hZ : IsZero ((stageOneDiagram C Y).obj B) :=
          hBTgt.symm ▸ isZero_zero C
        exact hZ.eq_of_tgt _ _
      · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
          ar1_eq_interval01_of_ne ha
        have hB : B = interval (0 : Fin 2) 1 (by decide) :=
          ar1_eq_interval01_of_ne hb
        subst hA
        subst hB
        have hφ : φ = 𝟙 _ :=
          Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
        subst hφ
        simp [stageOneDiagram, stageOneDiagramObj,
          Category.id_comp, Category.comp_id])
  map_id X := by
    ext A
    by_cases ha : A.left = A.right
    · have hObj : (stageOneDiagram C X).obj A = (0 : C) := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      have hZ : IsZero ((stageOneDiagram C X).obj A) := hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne ha
      subst hA
      rfl
  map_comp {X Y Z} f g := by
    ext A
    by_cases ha : A.left = A.right
    · have hObj : (stageOneDiagram C X).obj A = (0 : C) := by
        simp [stageOneDiagram, stageOneDiagramObj, ha]
      have hZ : IsZero ((stageOneDiagram C X).obj A) := hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · have hA : A = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne ha
      subst hA
      rfl

/-- Canonical functor from `C` to `Stage C 1`, via the full-subcategory lift.
The interval `(0, 1)` value is the input object; diagonal values are zero. -/
noncomputable def stageOne : C ⥤ Stage C 1 :=
  (stageProperty C 1).lift (stageOneDiagramFunctor C) (fun X => isStage_stageOneDiagram C X)

/-- The underlying diagram of `stageOne.obj X` at a diagonal is zero. -/
theorem stageOne_obj_diag (X : C) (i : Fin 2) :
    ((stageOne C).obj X).obj.obj (diag i) = (0 : C) :=
  stageOneDiagram_diag C X i

/-- The underlying diagram of `stageOne.obj X` at `(0, 1)` is `X`. -/
theorem stageOne_obj_interval_zero_one (X : C) (h : (0 : Fin 2) ≤ 1) :
    ((stageOne C).obj X).obj.obj (interval 0 1 h) = X :=
  stageOneDiagram_interval_zero_one C X h

/-- Functoriality at the `(0, 1)` interval is the input morphism. -/
theorem stageOne_map_interval_zero_one {X Y : C} (f : X ⟶ Y) :
    ((stageOne C).map f).hom.app (interval (0 : Fin 2) 1 (by decide)) = f := by
  rfl

/-- Functoriality at a diagonal is the identity on zero. -/
theorem stageOne_map_diag {X Y : C} (f : X ⟶ Y) (i : Fin 2) :
    eqToHom (stageOne_obj_diag C X i).symm ≫ ((stageOne C).map f).hom.app (diag i) ≫
      eqToHom (stageOne_obj_diag C Y i) = 𝟙 (0 : C) := by
  exact (isZero_zero C).eq_of_src _ _

end CategoryTheory.Waldhausen.SConstruction
