/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCompleteBoundary
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Single

/-!
# Nonzero first-page and boundary coordinates over the integers

Both vertical rows are concentrated in degree zero on Z. The horizontal map is multiplication
by two, which is not surjective and therefore cannot be a split epimorphism. A chosen cycle
has coordinate one in the new first-page column. The transported horizontal cycle map has
coordinate -2, whereas the finite filtered boundary has coordinate +2. These detect the
untwisting sign and the order of the actual boundary construction on nonzero coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients

/-- The integer coefficient object. -/
abbrev Z := ModuleCat.of ℤ ℤ

/-- A vertical row concentrated in degree zero. -/
def row : ChainComplex (ModuleCat ℤ) ℕ :=
  (ChainComplex.single₀ (ModuleCat ℤ)).obj Z

/-- The actual horizontal doubling map. -/
def double : row ⟶ row := 𝟙 row + 𝟙 row

/-- The two-row integer bicomplex with doubling horizontally and zero vertically. -/
def K : HomologicalComplex₂ (ModuleCat ℤ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.mk row row 0 double 0 (by simp) (fun S => ⟨0, 0, by simp⟩)

theorem horizontal_component : (K.d 1 0).f 0 = 𝟙 Z + 𝟙 Z := by
  rw [show K.d 1 0 = double from ChainComplex.mk_d_1_0 _ _ _ _ _ _ _]
  rfl

/-- The vertical cycle corresponding to the integer one. -/
def verticalCycle : Z ⟶ row.cycles 0 :=
  row.liftCycles (𝟙 Z) ((ComplexShape.down ℕ).next 0) rfl
    (by change (𝟙 Z) ≫ 0 = 0; exact comp_zero)

/-- The same cycle in the sign-normalized direct-column coordinates. -/
def sourceCycle : Z ⟶ (HomologicalComplex₂.horizontalDirectColumnCochain K 1).cycles (-1) :=
  verticalCycle ≫ (HomologicalComplex₂.horizontalDirectColumnVerticalCyclesIso K 1 0).inv

@[reassoc]
theorem source_coordinate : sourceCycle ≫
    (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
    (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom = 𝟙 Z := by
  unfold sourceCycle
  have he := HomologicalComplex₂.horizontalDirectColumnVerticalCyclesIso_hom_iCycles K 1 0
  have he' : (HomologicalComplex₂.horizontalDirectColumnVerticalCyclesIso K 1 0).hom ≫
      (K.X 1).iCycles 0 =
    (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
      (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom := by
    simpa only [Nat.cast_one, Nat.cast_zero, sub_zero] using he
  simp only [Category.assoc]
  rw [← he']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, verticalCycle,
    HomologicalComplex.liftCycles_i]

/-- Recover the preceding coordinate after the finite-stage inclusion. -/
def lowerRecovery : HomologicalComplex₂.horizontalFilteredTotalObj K 1 0 ⟶ Z :=
  HomologicalComplex₂.horizontalFilteredTotalToTotal K 1 0 ≫
    HomologicalComplex₂.horizontalTotalTopProjection K 0 0

@[reassoc]
theorem previous_recovery :
    HomologicalComplex₂.horizontalFilteredPreviousColumnInclusion K 0 0 ≫
      lowerRecovery = 𝟙 Z := by
  have h := HomologicalComplex₂.horizontalFilteredTotalι_toTotal K 1 0
    ⟨⟨(0, 0), rfl⟩, by decide⟩
  change HomologicalComplex₂.horizontalFilteredPreviousColumnInclusion K 0 0 ≫
    HomologicalComplex₂.horizontalFilteredTotalToTotal K 1 0 =
      K.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl at h
  have hc := congrArg
    (fun f => f ≫ HomologicalComplex₂.horizontalTotalTopProjection K 0 0) h
  have hp : K.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫
      HomologicalComplex₂.horizontalTotalTopProjection K 0 0 = 𝟙 Z := by
    simpa using HomologicalComplex₂.ιTotal_horizontalTotalTopProjection K 0 0 0 0 rfl
  simpa only [lowerRecovery, Category.assoc] using hc.trans hp

/-- The public horizontal cycle map carries the nonzero negative coordinate. -/
theorem horizontal_cycle_coordinate : sourceCycle ≫
    HomologicalComplex₂.horizontalDirectColumnHorizontalCyclesMap K 0 0 ≫
    (HomologicalComplex₂.horizontalDirectColumnCochain K 0).iCycles 0 ≫
    (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 0 0).hom =
      (1 : ℤ).negOnePow • (K.d 1 0).f 0 := by
  have h := HomologicalComplex₂.horizontalDirectColumnHorizontalCyclesMap_iCycles K 0 0
  have h' : HomologicalComplex₂.horizontalDirectColumnHorizontalCyclesMap K 0 0 ≫
      (HomologicalComplex₂.horizontalDirectColumnCochain K 0).iCycles 0 =
    (1 : ℤ).negOnePow •
      ((HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
        (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom ≫
        (K.d 1 0).f 0 ≫
        (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 0 0).inv) := by
    simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_one, Nat.cast_zero,
      neg_zero, sub_zero] using h
  have hc := congrArg
    (fun f => sourceCycle ≫ f ≫
      (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 0 0).hom) h'
  simpa only [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
    Iso.inv_hom_id_assoc, source_coordinate_assoc, Category.id_comp] using hc

/-- The finite boundary has the positive horizontal coordinate. -/
theorem finite_boundary_coordinate : sourceCycle ≫
    (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
    (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom ≫
    HomologicalComplex₂.horizontalFilteredTopInclusion K 1 0 ≫
    HomologicalComplex₂.horizontalFilteredTotalD K 1 1 0 ≫ lowerRecovery =
      (K.d 1 0).f 0 := by
  have h := HomologicalComplex₂.horizontalDirectColumnTopInclusion_d_eq_previous K 0 0
  have h' : (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
      (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom ≫
      HomologicalComplex₂.horizontalFilteredTopInclusion K 1 0 ≫
      HomologicalComplex₂.horizontalFilteredTotalD K 1 1 0 =
    (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
      (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom ≫
      (K.d 1 0).f 0 ≫
      HomologicalComplex₂.horizontalFilteredPreviousColumnInclusion K 0 0 := by
    simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_one, Nat.cast_zero,
      neg_zero, sub_zero] using h
  have hc := congrArg (fun f => sourceCycle ≫ f ≫ lowerRecovery) h'
  simpa only [Category.assoc, source_coordinate_assoc, Category.id_comp,
    previous_recovery, Category.comp_id] using hc

example : (sourceCycle ≫
    HomologicalComplex₂.horizontalDirectColumnHorizontalCyclesMap K 0 0 ≫
    (HomologicalComplex₂.horizontalDirectColumnCochain K 0).iCycles 0 ≫
    (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 0 0).hom).hom (1 : ℤ) = (-2 : ℤ) := by
  rw [horizontal_cycle_coordinate, horizontal_component]
  change (1 : ℤ).negOnePow • ((1 : ℤ) + 1) = -2
  decide

example : (sourceCycle ≫
    (HomologicalComplex₂.horizontalDirectColumnCochain K 1).iCycles (-1) ≫
    (HomologicalComplex₂.horizontalDirectColumnCochainXIso K 1 0).hom ≫
    HomologicalComplex₂.horizontalFilteredTopInclusion K 1 0 ≫
    HomologicalComplex₂.horizontalFilteredTotalD K 1 1 0 ≫ lowerRecovery).hom (1 : ℤ) = 2 := by
  rw [finite_boundary_coordinate, horizontal_component]
  rfl

example : ¬ Function.Surjective ((K.d 1 0).f 0).hom := by
  intro h
  obtain ⟨x, hx⟩ := h (1 : ℤ)
  rw [horizontal_component] at hx
  have hx' : (x : ℤ) + x = 1 := hx
  omega

end MathlibExtTest.Algebra.Homology.FirstQuadrantFirstPageFocusedClients
