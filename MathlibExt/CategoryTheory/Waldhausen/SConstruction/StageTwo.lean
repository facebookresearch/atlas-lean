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
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.FinCases

/-!
# Object-level degree-two converse from cofiber-sequence data

Given `f : X ⟶ Y`, `g : Y ⟶ Z` with `hSeq : IsCofibrationSequence f g`,
construct the six-object `Ar 2` diagram with diagonals at zero and
`(0,1)/(0,2)/(1,2)` at `X/Y/Z`. The direct `(0,1) ⟶ (1,2)` map is `f ≫ g`,
which is zero by `hSeq`, so the via-diagonal factorization agrees.
Proves functor laws and `IsStage`, bundles a named `Stage C 2`.

Nonclaims: no cofiber-sequence category or morphism functor/equivalence,
no reindexing, no simplicial object, no nerve/realization, no K/G-theory,
and no Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Object assignment: diagonals to zero, `(0,1)/(0,2)` to `X/Y`, else `Z`. -/
noncomputable def stageTwoDiagramObj (X Y Z : C) (A : Ar 2) : C :=
  if A.left = A.right then (0 : C)
  else if A.left.val = 0 ∧ A.right.val = 1 then X
  else if A.left.val = 0 ∧ A.right.val = 2 then Y
  else Z

omit [WaldhausenCategoryWithoutGluing C] in
/-- A diagonal object is sent to the chosen zero object. -/
theorem stageTwoDiagramObj_of_eq (X Y Z : C) {A : Ar 2} (h : A.left = A.right) :
    stageTwoDiagramObj C X Y Z A = (0 : C) := by
  simp [stageTwoDiagramObj, h]

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(0,1)` interval is sent to `X`. -/
theorem stageTwoDiagramObj_of_01 (X Y Z : C) {A : Ar 2}
    (hne : ¬ A.left = A.right) (h01 : A.left.val = 0 ∧ A.right.val = 1) :
    stageTwoDiagramObj C X Y Z A = X := by
  simp [stageTwoDiagramObj, hne, h01]

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(0,2)` interval is sent to `Y`. -/
theorem stageTwoDiagramObj_of_02 (X Y Z : C) {A : Ar 2}
    (hne : ¬ A.left = A.right) (_h01 : ¬ (A.left.val = 0 ∧ A.right.val = 1))
    (h02 : A.left.val = 0 ∧ A.right.val = 2) :
    stageTwoDiagramObj C X Y Z A = Y := by
  simp [stageTwoDiagramObj, hne, h02]

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(1,2)` interval is sent to `Z`. -/
theorem stageTwoDiagramObj_of_12 (X Y Z : C) {A : Ar 2}
    (hne : ¬ A.left = A.right) (h01 : ¬ (A.left.val = 0 ∧ A.right.val = 1))
    (h02 : ¬ (A.left.val = 0 ∧ A.right.val = 2)) :
    stageTwoDiagramObj C X Y Z A = Z := by
  unfold stageTwoDiagramObj
  rw [ite_eq_right hne, ite_eq_right h01, ite_eq_right h02]

omit [WaldhausenCategoryWithoutGluing C] in
/-- Diagonal objects are zero. -/
theorem stageTwoDiagramObj_diag (X Y Z : C) (i : Fin 3) :
    stageTwoDiagramObj C X Y Z (diag i) = (0 : C) := by
  simp [stageTwoDiagramObj, diag, interval]

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(0,1)` object is `X`. -/
theorem stageTwoDiagramObj_interval01 (X Y Z : C) (h : (0 : Fin 3) ≤ 1) :
    stageTwoDiagramObj C X Y Z (interval 0 1 h) = X := by
  have hne : ¬ (interval (0 : Fin 3) 1 h).left = (interval (0 : Fin 3) 1 h).right := by
    change ¬ (0 : Fin 3) = 1
    decide
  have h01 : (interval (0 : Fin 3) 1 h).left.val = 0 ∧
      (interval (0 : Fin 3) 1 h).right.val = 1 := by
    change (0 : Fin 3).val = 0 ∧ (1 : Fin 3).val = 1
    decide
  exact stageTwoDiagramObj_of_01 C X Y Z hne h01

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(0,2)` object is `Y`. -/
theorem stageTwoDiagramObj_interval02 (X Y Z : C) (h : (0 : Fin 3) ≤ 2) :
    stageTwoDiagramObj C X Y Z (interval 0 2 h) = Y := by
  have hne : ¬ (interval (0 : Fin 3) 2 h).left = (interval (0 : Fin 3) 2 h).right := by
    change ¬ (0 : Fin 3) = 2
    decide
  have h01 : ¬ ((interval (0 : Fin 3) 2 h).left.val = 0 ∧
      (interval (0 : Fin 3) 2 h).right.val = 1) := by
    change ¬ ((0 : Fin 3).val = 0 ∧ (2 : Fin 3).val = 1)
    decide
  have h02 : (interval (0 : Fin 3) 2 h).left.val = 0 ∧
      (interval (0 : Fin 3) 2 h).right.val = 2 := by
    change (0 : Fin 3).val = 0 ∧ (2 : Fin 3).val = 2
    decide
  exact stageTwoDiagramObj_of_02 C X Y Z hne h01 h02

omit [WaldhausenCategoryWithoutGluing C] in
/-- The `(1,2)` object is `Z`. -/
theorem stageTwoDiagramObj_interval12 (X Y Z : C) (h : (1 : Fin 3) ≤ 2) :
    stageTwoDiagramObj C X Y Z (interval 1 2 h) = Z := by
  have hne : ¬ (interval (1 : Fin 3) 2 h).left = (interval (1 : Fin 3) 2 h).right := by
    change ¬ (1 : Fin 3) = 2
    decide
  have h01 : ¬ ((interval (1 : Fin 3) 2 h).left.val = 0 ∧
      (interval (1 : Fin 3) 2 h).right.val = 1) := by
    change ¬ ((1 : Fin 3).val = 0 ∧ (2 : Fin 3).val = 1)
    decide
  have h02 : ¬ ((interval (1 : Fin 3) 2 h).left.val = 0 ∧
      (interval (1 : Fin 3) 2 h).right.val = 2) := by
    change ¬ ((1 : Fin 3).val = 0 ∧ (2 : Fin 3).val = 2)
    decide
  exact stageTwoDiagramObj_of_12 C X Y Z hne h01 h02

/-- Every off-diagonal `Ar 2` object with endpoints `(0, 1)` is the `(0, 1)` interval. -/
theorem stageTwo_ar2_eq_interval01 {A : Ar 2}
    (h01 : A.left.val = 0 ∧ A.right.val = 1) :
    A = interval (0 : Fin 3) 1 (by decide) := by
  cases A with
  | mk l r h =>
    obtain ⟨h0, h1⟩ := h01
    have hl : l = 0 := Fin.ext (by simpa using h0)
    have hr : r = 1 := Fin.ext (by simpa using h1)
    subst hl
    subst hr
    have hhom : h = homOfLE (by decide : (0 : Fin 3) ≤ 1) := Subsingleton.elim _ _
    subst hhom
    rfl

/-- Every off-diagonal `Ar 2` object with endpoints `(0, 2)` is the `(0, 2)` interval. -/
theorem stageTwo_ar2_eq_interval02 {A : Ar 2}
    (h02 : A.left.val = 0 ∧ A.right.val = 2) :
    A = interval (0 : Fin 3) 2 (by decide) := by
  cases A with
  | mk l r h =>
    obtain ⟨h0, h2⟩ := h02
    have hl : l = 0 := Fin.ext (by simpa using h0)
    have hr : r = 2 := Fin.ext (by simpa using h2)
    subst hl
    subst hr
    have hhom : h = homOfLE (by decide : (0 : Fin 3) ≤ 2) := Subsingleton.elim _ _
    subst hhom
    rfl

/-- Every off-diagonal `Ar 2` object with endpoints `(1, 2)` is the `(1, 2)` interval. -/
theorem stageTwo_ar2_eq_interval12 {A : Ar 2}
    (hne : ¬ A.left = A.right) (_h01 : ¬ (A.left.val = 0 ∧ A.right.val = 1))
    (_h02 : ¬ (A.left.val = 0 ∧ A.right.val = 2)) :
    A = interval (1 : Fin 3) 2 (by decide) := by
  cases A with
  | mk l r h =>
    have hle : l ≤ r := leOfHom h
    have hdiag : ¬ l = r := by simpa using hne
    have hlr : l.val = 1 ∧ r.val = 2 := by
      fin_cases l <;> fin_cases r <;> simp_all
    obtain ⟨h1, h2⟩ := hlr
    have hl : l = 1 := Fin.ext (by simpa using h1)
    have hr : r = 2 := Fin.ext (by simpa using h2)
    subst hl
    subst hr
    have hhom : h = homOfLE (by decide : (1 : Fin 3) ≤ 2) := Subsingleton.elim _ _
    subst hhom
    rfl

private theorem stageTwo_fg_eq_zero {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    f ≫ g = (isZero_zero C).from_ X ≫ (isZero_zero C).to_ Z := by
  obtain ⟨_, h, q, hpush⟩ := hSeq
  have hh : h = (isZero_zero C).from_ X := (isZero_zero C).eq_of_tgt _ _
  have hq : q = (isZero_zero C).to_ Z := (isZero_zero C).eq_of_src _ _
  have hw : h ≫ q = f ≫ g := hpush.w
  rw [hh, hq] at hw
  exact hw.symm

/-- The morphism assignment underlying the public degree-two diagram, using
    identities, zero legs, `f`, `g`, and `f ≫ g` according to interval endpoints. -/
noncomputable def stageTwoDiagramMap (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    {A B : Ar 2} (_φ : A ⟶ B) :
    stageTwoDiagramObj C X Y Z A ⟶ stageTwoDiagramObj C X Y Z B := by
  by_cases ha : A.left = A.right
  · by_cases hb : B.left = B.right
    · rw [stageTwoDiagramObj_of_eq C X Y Z ha,
        stageTwoDiagramObj_of_eq C X Y Z hb]
      exact 𝟙 (0 : C)
    · rw [stageTwoDiagramObj_of_eq C X Y Z ha]
      exact (isZero_zero C).to_ _
  · by_cases hb : B.left = B.right
    · rw [stageTwoDiagramObj_of_eq C X Y Z hb]
      exact (isZero_zero C).from_ _
    · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
      · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
        · rw [stageTwoDiagramObj_of_01 C X Y Z ha ha01,
            stageTwoDiagramObj_of_01 C X Y Z hb hb01]
          exact 𝟙 X
        · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
          · rw [stageTwoDiagramObj_of_01 C X Y Z ha ha01,
              stageTwoDiagramObj_of_02 C X Y Z hb hb01 hb02]
            exact f
          · rw [stageTwoDiagramObj_of_01 C X Y Z ha ha01,
              stageTwoDiagramObj_of_12 C X Y Z hb hb01 hb02]
            exact f ≫ g
      · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
        · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
          · rw [stageTwoDiagramObj_of_02 C X Y Z ha ha01 ha02,
              stageTwoDiagramObj_of_01 C X Y Z hb hb01]
            exact (isZero_zero C).from_ Y ≫ (isZero_zero C).to_ X
          · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
            · rw [stageTwoDiagramObj_of_02 C X Y Z ha ha01 ha02,
                stageTwoDiagramObj_of_02 C X Y Z hb hb01 hb02]
              exact 𝟙 Y
            · rw [stageTwoDiagramObj_of_02 C X Y Z ha ha01 ha02,
                stageTwoDiagramObj_of_12 C X Y Z hb hb01 hb02]
              exact g
        · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
          · rw [stageTwoDiagramObj_of_12 C X Y Z ha ha01 ha02,
              stageTwoDiagramObj_of_01 C X Y Z hb hb01]
            exact (isZero_zero C).from_ Z ≫ (isZero_zero C).to_ X
          · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
            · rw [stageTwoDiagramObj_of_12 C X Y Z ha ha01 ha02,
                stageTwoDiagramObj_of_02 C X Y Z hb hb01 hb02]
              exact (isZero_zero C).from_ Z ≫ (isZero_zero C).to_ Y
            · rw [stageTwoDiagramObj_of_12 C X Y Z ha ha01 ha02,
                stageTwoDiagramObj_of_12 C X Y Z hb hb01 hb02]
              exact 𝟙 Z

/-- Degree-two diagram from cofiber-sequence data. -/
noncomputable def stageTwoDiagram (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) : Ar 2 ⥤ C where
  obj := stageTwoDiagramObj C X Y Z
  map := stageTwoDiagramMap C X Y Z f g
  map_id A := by
    by_cases ha : A.left = A.right
    · have hObj : stageTwoDiagramObj C X Y Z A = (0 : C) :=
        stageTwoDiagramObj_of_eq C X Y Z ha
      have hZ : IsZero (stageTwoDiagramObj C X Y Z A) := hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
      · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
          stageTwo_ar2_eq_interval01 ha01
        subst hA
        rfl
      · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
        · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval02 ha02
          subst hA
          rfl
        · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval12 ha ha01 ha02
          subst hA
          rfl
  map_comp {A B D} φ ψ := by
    by_cases ha : A.left = A.right
    · have hA : stageTwoDiagramObj C X Y Z A = (0 : C) :=
        stageTwoDiagramObj_of_eq C X Y Z ha
      have hZ : IsZero (stageTwoDiagramObj C X Y Z A) :=
        hA.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · by_cases hd : D.left = D.right
      · have hD : stageTwoDiagramObj C X Y Z D = (0 : C) :=
          stageTwoDiagramObj_of_eq C X Y Z hd
        have hZ : IsZero (stageTwoDiagramObj C X Y Z D) :=
          hD.symm ▸ isZero_zero C
        exact hZ.eq_of_tgt _ _
      · by_cases hb : B.left = B.right
        · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
          · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
            · exfalso
              have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 ha01
              have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 hd01
              subst hA
              subst hD
              have hφL : (0 : Fin 3) ≤ B.left := by
                have h := leOfHom φ.left
                simp
              have hψL : B.left ≤ (0 : Fin 3) := by
                have h := leOfHom ψ.left
                simpa [interval] using h
              have hB01 : B.left = 0 := le_antisymm hψL hφL
              have hφR : (1 : Fin 3) ≤ B.right := by
                have h := leOfHom φ.right
                simpa [interval] using h
              have hψR : B.right ≤ (1 : Fin 3) := by
                have h := leOfHom ψ.right
                simpa [interval] using h
              have hB11 : B.right = 1 := le_antisymm hψR hφR
              rw [hB01, hB11] at hb
              exact absurd hb (by decide)
            · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
              · exfalso
                have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 ha01
                have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 hd02
                subst hA
                subst hD
                have hψL : B.left ≤ (0 : Fin 3) := by
                  have h := leOfHom ψ.left
                  simpa [interval] using h
                have hφL : (0 : Fin 3) ≤ B.left := by
                  have h := leOfHom φ.left
                  simp
                have hB0 : B.left = 0 := le_antisymm hψL hφL
                have hφR : (1 : Fin 3) ≤ B.right := by
                  have h := leOfHom φ.right
                  simpa [interval] using h
                have hBR0 : B.right = 0 := hb ▸ hB0
                rw [hBR0] at hφR
                exact absurd hφR (by decide)
              · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 ha01
                have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 hd hd01 hd02
                subst hA
                subst hD
                have hφL : (0 : Fin 3) ≤ B.left := by
                  have h := leOfHom φ.left
                  simp
                have hφR : (1 : Fin 3) ≤ B.right := by
                  have h := leOfHom φ.right
                  simpa [interval] using h
                have hψL : B.left ≤ (1 : Fin 3) := by
                  have h := leOfHom ψ.left
                  simpa [interval] using h
                have hψR : B.right ≤ (2 : Fin 3) := by
                  have h := leOfHom ψ.right
                  simpa [interval] using h
                have hB1 : B.left = 1 := le_antisymm hψL (hb ▸ hφR)
                have hB1r : B.right = 1 := hb ▸ hB1
                have hB11 : B = diag (1 : Fin 3) := by
                  cases B with
                  | mk l r h =>
                    simp only [Nat.reduceAdd, Fin.isValue] at hb hB1 hB1r ⊢
                    subst hB1
                    subst hB1r
                    have hhom : h = homOfLE (le_rfl : (1 : Fin 3) ≤ 1) :=
                      Subsingleton.elim _ _
                    subst hhom
                    rfl
                subst hB11
                have hfg := stageTwo_fg_eq_zero (C := C) f g hSeq
                have eφ : stageTwoDiagramMap C X Y Z f g φ =
                    (isZero_zero C).from_ X := by rfl
                have eψ : stageTwoDiagramMap C X Y Z f g ψ =
                    (isZero_zero C).to_ Z := by rfl
                have ecomp : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f ≫ g := by
                  rfl
                rw [ecomp, eφ, eψ]
                exact hfg
          · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
            · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 ha02
              subst hA
              have hφR : (2 : Fin 3) ≤ B.right := by
                have h := leOfHom φ.right
                simpa [interval] using h
              have h2B : (2 : Fin 3) ≤ B.left := hb ▸ hφR
              by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
              · exfalso
                have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hd01
                subst hD
                have hψL : B.left ≤ (0 : Fin 3) := by
                  have h := leOfHom ψ.left
                  simpa [interval] using h
                have h20 : (2 : Fin 3) ≤ (0 : Fin 3) := le_trans h2B hψL
                exact absurd h20 (by decide)
              · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                · exfalso
                  have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hd02
                  subst hD
                  have hψL : B.left ≤ (0 : Fin 3) := by
                    have h := leOfHom ψ.left
                    simpa [interval] using h
                  have h20 : (2 : Fin 3) ≤ (0 : Fin 3) := le_trans h2B hψL
                  exact absurd h20 (by decide)
                · exfalso
                  have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hd hd01 hd02
                  subst hD
                  have hψL : B.left ≤ (1 : Fin 3) := by
                    have h := leOfHom ψ.left
                    simpa [interval] using h
                  have h21 : (2 : Fin 3) ≤ (1 : Fin 3) := le_trans h2B hψL
                  exact absurd h21 (by decide)
            · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 ha ha01 ha02
              subst hA
              have hφR : (2 : Fin 3) ≤ B.right := by
                have h := leOfHom φ.right
                simpa [interval] using h
              have h2B : (2 : Fin 3) ≤ B.left := hb ▸ hφR
              by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
              · exfalso
                have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hd01
                subst hD
                have hψL : B.left ≤ (0 : Fin 3) := by
                  have h := leOfHom ψ.left
                  simpa [interval] using h
                have h20 : (2 : Fin 3) ≤ (0 : Fin 3) := le_trans h2B hψL
                exact absurd h20 (by decide)
              · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                · exfalso
                  have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hd02
                  subst hD
                  have hψL : B.left ≤ (0 : Fin 3) := by
                    have h := leOfHom ψ.left
                    simpa [interval] using h
                  have h20 : (2 : Fin 3) ≤ (0 : Fin 3) := le_trans h2B hψL
                  exact absurd h20 (by decide)
                · exfalso
                  have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hd hd01 hd02
                  subst hD
                  have hψL : B.left ≤ (1 : Fin 3) := by
                    have h := leOfHom ψ.left
                    simpa [interval] using h
                  have h21 : (2 : Fin 3) ≤ (1 : Fin 3) := le_trans h2B hψL
                  exact absurd h21 (by decide)
        · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
          · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
            · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
              · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                    stageTwo_ar2_eq_interval01 ha01
                have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hb01
                have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hd01
                subst hA
                subst hB
                subst hD
                have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = 𝟙 X := rfl
                have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 X := rfl
                have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 X := rfl
                rw [eL, e1, e2]
                exact (Category.comp_id _).symm
              · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                      stageTwo_ar2_eq_interval01 ha01
                  have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                    stageTwo_ar2_eq_interval01 hb01
                  have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hd02
                  subst hA
                  subst hB
                  subst hD
                  have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f := rfl
                  have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 X := rfl
                  have e2 : stageTwoDiagramMap C X Y Z f g ψ = f := rfl
                  rw [eL, e1, e2]
                  exact (Category.id_comp _).symm
                · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                      stageTwo_ar2_eq_interval01 ha01
                  have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                    stageTwo_ar2_eq_interval01 hb01
                  have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hd hd01 hd02
                  subst hA
                  subst hB
                  subst hD
                  have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f ≫ g := rfl
                  have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 X := rfl
                  have e2 : stageTwoDiagramMap C X Y Z f g ψ = f ≫ g := rfl
                  rw [eL, e1, e2]
                  exact (Category.id_comp _).symm
            · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
              · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
                · exfalso
                  have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hb02
                  have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                    stageTwo_ar2_eq_interval01 hd01
                  subst hB
                  subst hD
                  have hψR : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom ψ.right
                  exact absurd hψR (by decide)
                · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                  · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                        stageTwo_ar2_eq_interval01 ha01
                    have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval02 hb02
                    have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval02 hd02
                    subst hA
                    subst hB
                    subst hD
                    have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f := rfl
                    have e1 : stageTwoDiagramMap C X Y Z f g φ = f := rfl
                    have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 Y := rfl
                    rw [eL, e1, e2]
                    exact (Category.comp_id _).symm
                  · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                        stageTwo_ar2_eq_interval01 ha01
                    have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval02 hb02
                    have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval12 hd hd01 hd02
                    subst hA
                    subst hB
                    subst hD
                    have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f ≫ g := rfl
                    have e1 : stageTwoDiagramMap C X Y Z f g φ = f := rfl
                    have e2 : stageTwoDiagramMap C X Y Z f g ψ = g := rfl
                    rw [eL, e1, e2]
                    rfl
              · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 hb hb01 hb02
                by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
                · exfalso
                  have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                    stageTwo_ar2_eq_interval01 hd01
                  subst hB
                  subst hD
                  have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                  exact absurd hψL (by decide)
                · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                  · exfalso
                    have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval02 hd02
                    subst hB
                    subst hD
                    have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                    exact absurd hψL (by decide)
                  · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                        stageTwo_ar2_eq_interval01 ha01
                    have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval12 hd hd01 hd02
                    subst hA
                    subst hB
                    subst hD
                    have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = f ≫ g := rfl
                    have e1 : stageTwoDiagramMap C X Y Z f g φ = f ≫ g := rfl
                    have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 Z := rfl
                    rw [eL, e1, e2]
                    exact (Category.comp_id _).symm
          · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
            · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
              · exfalso
                have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 ha02
                have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hb01
                subst hA
                subst hB
                have hφR : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom φ.right
                exact absurd hφR (by decide)
              · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
                · by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
                  · exfalso
                    have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                      stageTwo_ar2_eq_interval02 hb02
                    have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                      stageTwo_ar2_eq_interval01 hd01
                    subst hB
                    subst hD
                    have hψR : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom ψ.right
                    exact absurd hψR (by decide)
                  · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                    · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                          stageTwo_ar2_eq_interval02 ha02
                      have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval02 hb02
                      have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval02 hd02
                      subst hA
                      subst hB
                      subst hD
                      have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = 𝟙 Y := rfl
                      have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 Y := rfl
                      have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 Y := rfl
                      rw [eL, e1, e2]
                      exact (Category.comp_id _).symm
                    · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                          stageTwo_ar2_eq_interval02 ha02
                      have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval02 hb02
                      have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval12 hd hd01 hd02
                      subst hA
                      subst hB
                      subst hD
                      have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = g := rfl
                      have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 Y := rfl
                      have e2 : stageTwoDiagramMap C X Y Z f g ψ = g := rfl
                      rw [eL, e1, e2]
                      exact (Category.id_comp _).symm
                · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hb hb01 hb02
                  by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
                  · exfalso
                    have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                      stageTwo_ar2_eq_interval01 hd01
                    subst hB
                    subst hD
                    have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                    exact absurd hψL (by decide)
                  · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                    · exfalso
                      have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval02 hd02
                      subst hB
                      subst hD
                      have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                      exact absurd hψL (by decide)
                    · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                          stageTwo_ar2_eq_interval02 ha02
                      have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval12 hd hd01 hd02
                      subst hA
                      subst hB
                      subst hD
                      have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = g := rfl
                      have e1 : stageTwoDiagramMap C X Y Z f g φ = g := rfl
                      have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 Z := rfl
                      rw [eL, e1, e2]
                      exact (Category.comp_id _).symm
            · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 ha ha01 ha02
              by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
              · exfalso
                have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hb01
                subst hA
                subst hB
                have hφL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom φ.left
                exact absurd hφL (by decide)
              · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
                · exfalso
                  have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hb02
                  subst hA
                  subst hB
                  have hφL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom φ.left
                  exact absurd hφL (by decide)
                · have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hb hb01 hb02
                  by_cases hd01 : D.left.val = 0 ∧ D.right.val = 1
                  · exfalso
                    have hD : D = interval (0 : Fin 3) 1 (by decide) :=
                      stageTwo_ar2_eq_interval01 hd01
                    subst hB
                    subst hD
                    have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                    exact absurd hψL (by decide)
                  · by_cases hd02 : D.left.val = 0 ∧ D.right.val = 2
                    · exfalso
                      have hD : D = interval (0 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval02 hd02
                      subst hB
                      subst hD
                      have hψL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom ψ.left
                      exact absurd hψL (by decide)
                    · have hD : D = interval (1 : Fin 3) 2 (by decide) :=
                        stageTwo_ar2_eq_interval12 hd hd01 hd02
                      subst hA
                      subst hB
                      subst hD
                      have eL : stageTwoDiagramMap C X Y Z f g (φ ≫ ψ) = 𝟙 Z := rfl
                      have e1 : stageTwoDiagramMap C X Y Z f g φ = 𝟙 Z := rfl
                      have e2 : stageTwoDiagramMap C X Y Z f g ψ = 𝟙 Z := rfl
                      rw [eL, e1, e2]
                      exact (Category.comp_id _).symm

/-- The degree-two diagram is a finite stage. -/
theorem isStage_stageTwoDiagram (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    IsStage 2 (stageTwoDiagram C X Y Z f g hSeq) where
  diag_isZero i := by
    rw [show (stageTwoDiagram C X Y Z f g hSeq).obj (diag i) = (0 : C) from
      stageTwoDiagramObj_diag C X Y Z i]
    exact isZero_zero C
  cofiber_triple {i j k} hij hjk := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 (0 : C) := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 (0 : C) := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          (isZero_zero C).to_ X := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 X := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), (isZero_zero C).to_ X, IsPushout.of_id_fst⟩
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          (isZero_zero C).to_ Y := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 Y := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), (isZero_zero C).to_ Y, IsPushout.of_id_fst⟩
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3))) hjk)
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 X := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          (isZero_zero C).from_ X := rfl
      rw [eH, eV]
      exact ⟨MorphismProperty.id_mem (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _,
        (isZero_zero C).from_ X, 𝟙 (0 : C), IsPushout.of_id_snd⟩
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) = f := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) = g := rfl
      rw [eH, eV]
      exact hSeq
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hjk)
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 Y := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          (isZero_zero C).from_ Y := rfl
      rw [eH, eV]
      exact ⟨MorphismProperty.id_mem (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _,
        (isZero_zero C).from_ Y, 𝟙 (0 : C), IsPushout.of_id_snd⟩
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3))) hjk)
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 (0 : C) := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 (0 : C) := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          (isZero_zero C).to_ Z := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 Z := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), (isZero_zero C).to_ Z, IsPushout.of_id_fst⟩
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hjk)
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 Z := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          (isZero_zero C).from_ Z := rfl
      rw [eH, eV]
      exact ⟨MorphismProperty.id_mem (WaldhausenCategoryWithoutGluing.cofibrations (C := C)) _,
        (isZero_zero C).from_ Z, 𝟙 (0 : C), IsPushout.of_id_snd⟩
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3))) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3))) hjk)
    · have eH : (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) =
          𝟙 (0 : C) := rfl
      have eV : (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) =
          𝟙 (0 : C) := rfl
      rw [eH, eV]
      exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration _ _,
        𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩

/-- Bundled degree-two stage from cofiber-sequence data. -/
noncomputable def stageTwo (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) : Stage C 2 :=
  ⟨stageTwoDiagram C X Y Z f g hSeq, isStage_stageTwoDiagram C X Y Z f g hSeq⟩

/-- The bundled stage sends `(0,1)` to `X`. -/
theorem stageTwo_obj_01 (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) (h : (0 : Fin 3) ≤ 1) :
    (stageTwo C X Y Z f g hSeq).obj.obj (interval 0 1 h) = X :=
  stageTwoDiagramObj_interval01 C X Y Z h

/-- The bundled stage sends `(0,2)` to `Y`. -/
theorem stageTwo_obj_02 (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) (h : (0 : Fin 3) ≤ 2) :
    (stageTwo C X Y Z f g hSeq).obj.obj (interval 0 2 h) = Y :=
  stageTwoDiagramObj_interval02 C X Y Z h

/-- The bundled stage sends `(1,2)` to `Z`. -/
theorem stageTwo_obj_12 (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) (h : (1 : Fin 3) ≤ 2) :
    (stageTwo C X Y Z f g hSeq).obj.obj (interval 1 2 h) = Z :=
  stageTwoDiagramObj_interval12 C X Y Z h

/-- The `(0,1) ⟶ (0,2)` map is `f`. -/
theorem stageTwo_map_horiz_012 (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g)
    (hij : (0 : Fin 3) ≤ 1) (hjk : (1 : Fin 3) ≤ 2) :
    (stageTwo C X Y Z f g hSeq).obj.map (horiz hij hjk) = f := by
  change (stageTwoDiagram C X Y Z f g hSeq).map (horiz hij hjk) = f
  rfl

/-- The `(0,2) ⟶ (1,2)` map is `g`. -/
theorem stageTwo_map_vert_012 (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g)
    (hij : (0 : Fin 3) ≤ 1) (hjk : (1 : Fin 3) ≤ 2) :
    (stageTwo C X Y Z f g hSeq).obj.map (vert hij hjk) = g := by
  change (stageTwoDiagram C X Y Z f g hSeq).map (vert hij hjk) = g
  rfl

end CategoryTheory.Waldhausen.SConstruction
