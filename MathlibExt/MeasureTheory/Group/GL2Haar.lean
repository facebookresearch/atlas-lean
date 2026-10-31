/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.lean`
and
`P2M/Sol/S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.lean`
and
`Theorems/Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_
isInvInvariant_of_isHaarMeasure_fin_two.lean`
and
`P2M/Sol/S_Matrix_GeneralLinearGroup_isMulRightInvariant_and_
isInvInvariant_of_isHaarMeasure_fin_two.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Unimodularity of `GL (2, F)`

The modular character of `GL (2, F)` is trivial for any topological field `F`:
every element is a product of transvections and a diagonal matrix, and the
modular character is `1` on each of these. Consequently every Haar measure
on `GL (2, F)` is right-invariant and inversion-invariant.
-/

@[expose] public section

open scoped NNReal

namespace GL2HaarAux

open MeasureTheory MeasureTheory.Measure

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [LocallyCompactSpace (GL (Fin 2) F)]

section Elements

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/-- Build an element of `GL (2, F)` from a matrix with nonzero determinant. -/
private def glOf (M : Matrix (Fin 2) (Fin 2) F) (h : M.det ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero M h

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
@[simp]
private theorem coe_glOf (M : Matrix (Fin 2) (Fin 2) F) (h : M.det ≠ 0) :
    ((glOf M h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem det_T01 (c : F) : (!![(1 : F), c; 0, 1]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem det_T10 (c : F) : (!![(1 : F), 0; c, 1]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem det_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![a, 0; 0, b]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp [ha, hb]

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem det_W : (!![(0 : F), 1; 1, 0]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/-- The elementary transvection with `c` in the `(0, 1)` entry. -/
private def T01 (c : F) : GL (Fin 2) F := glOf !![(1 : F), c; 0, 1] (det_T01 c)

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/-- The elementary transvection with `c` in the `(1, 0)` entry. -/
private def T10 (c : F) : GL (Fin 2) F := glOf !![(1 : F), 0; c, 1] (det_T10 c)

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/-- The diagonal matrix with entries `a` and `b`. -/
private def Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : GL (Fin 2) F :=
  glOf !![a, 0; 0, b] (det_Dg ha hb)

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/-- The Weyl element swapping the two basis vectors. -/
private def W : GL (Fin 2) F := glOf !![(0 : F), 1; 1, 0] det_W

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem T01_mul_T01 (c : F) : T01 c * T01 c = T01 (c + c) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem T10_mul_T10 (c : F) : T10 c * T10 c = T10 (c + c) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T10, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem T01_zero : T01 (0 : F) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [T01, coe_glOf, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem T10_zero : T10 (0 : F) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [T10, coe_glOf, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem Dg_mul_T01 (h2 : (2 : F) ≠ 0) (c : F) :
    Dg h2 one_ne_zero * T01 c = T01 (c + c) * Dg h2 one_ne_zero := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem Dg_mul_T10 (h2 : (2 : F) ≠ 0) (c : F) :
    Dg one_ne_zero h2 * T10 c = T10 (c + c) * Dg one_ne_zero h2 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T10, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem W_mul_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    W * Dg ha hb = Dg hb ha * W := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, W, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem Dg_mul_Dg_comm {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (g : GL (Fin 2) F) :
    g * (Dg ha hb * Dg hb ha) = Dg ha hb * Dg hb ha * g := by
  have hval : ((Dg ha hb : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((Dg hb ha : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a * b) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    simp only [Dg, coe_glOf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  apply Units.ext
  simp only [Units.val_mul]
  rw [hval, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

end Elements

/-- The modular character of `GL (2, F)`. -/
private noncomputable abbrev mc : GL (Fin 2) F →* ℝ≥0 := modularCharacter

private theorem mc_pos (g : GL (Fin 2) F) : 0 < mc g := modularCharacterFun_pos g

private theorem mc_eq_of_mul_eq_mul {x y y' : GL (Fin 2) F} (h : x * y = y' * x) :
    mc y = mc y' := by
  have h1 : mc x * mc y = mc y' * mc x := by rw [← map_mul, ← map_mul, h]
  rw [mul_comm (mc y') (mc x)] at h1
  exact mul_left_cancel₀ (mc_pos x).ne' h1

private theorem mc_eq_one_of_forall_comm {z : GL (Fin 2) F}
    (hz : ∀ g : GL (Fin 2) F, g * z = z * g) : mc z = 1 := by
  let : MeasurableSpace (GL (Fin 2) F) := borel (GL (Fin 2) F)
  have : BorelSpace (GL (Fin 2) F) := ⟨rfl⟩
  change modularCharacterFun z = 1
  rw [modularCharacterFun_eq_haarScalarFactor haar z]
  have hfun : (fun x : GL (Fin 2) F => x * z) = fun x => z * x := funext fun x => hz x
  have h1 : Measure.map (fun x : GL (Fin 2) F => x * z) haar = haar := by
    rw [hfun]
    exact map_mul_left_eq_self haar z
  have hfin : IsFiniteMeasureOnCompacts
      (Measure.map (fun x : GL (Fin 2) F => x * z) haar) :=
    IsFiniteMeasureOnCompacts.map haar (Homeomorph.mulRight z)
  have key : ∀ (μ' : Measure (GL (Fin 2) F)) [IsFiniteMeasureOnCompacts μ']
      [IsMulLeftInvariant μ'],
      μ' = haar → haarScalarFactor μ' haar = 1 := by
    intro μ' _ _ h
    subst h
    exact haarScalarFactor_self _
  exact key _ h1

private theorem nnreal_eq_one_of_mul_self_eq_one {a : ℝ≥0} (h : a * a = 1) : a = 1 := by
  have h' : (a : ℝ) * a = 1 := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have : (a : ℝ) = 1 := by nlinarith
  exact_mod_cast this

private theorem nnreal_eq_one_of_mul_self_eq_self {a : ℝ≥0} (ha : a ≠ 0) (h : a * a = a) :
    a = 1 := by
  have h2 : a * a = 1 * a := by rw [one_mul]; exact h
  exact mul_right_cancel₀ ha h2

private theorem mc_T01 (c : F) : mc (T01 c) = 1 := by
  by_cases h2 : (2 : F) = 0
  · have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    apply nnreal_eq_one_of_mul_self_eq_one
    rw [← map_mul, T01_mul_T01, hcc, T01_zero, map_one]
  · apply nnreal_eq_one_of_mul_self_eq_self (mc_pos _).ne'
    rw [← map_mul, T01_mul_T01]
    exact (mc_eq_of_mul_eq_mul (Dg_mul_T01 h2 c)).symm

private theorem mc_T10 (c : F) : mc (T10 c) = 1 := by
  by_cases h2 : (2 : F) = 0
  · have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    apply nnreal_eq_one_of_mul_self_eq_one
    rw [← map_mul, T10_mul_T10, hcc, T10_zero, map_one]
  · apply nnreal_eq_one_of_mul_self_eq_self (mc_pos _).ne'
    rw [← map_mul, T10_mul_T10]
    exact (mc_eq_of_mul_eq_mul (Dg_mul_T10 h2 c)).symm

private theorem mc_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : mc (Dg ha hb) = 1 := by
  apply nnreal_eq_one_of_mul_self_eq_one
  have h1 : mc (Dg ha hb) = mc (Dg hb ha) := mc_eq_of_mul_eq_mul (W_mul_Dg ha hb)
  calc mc (Dg ha hb) * mc (Dg ha hb) = mc (Dg ha hb) * mc (Dg hb ha) := by rw [← h1]
    _ = mc (Dg ha hb * Dg hb ha) := (map_mul _ _ _).symm
    _ = 1 := mc_eq_one_of_forall_comm (Dg_mul_Dg_comm ha hb)

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem glOf_toMatrix_eq (t : Matrix.TransvectionStruct (Fin 2) F)
    (h : t.toMatrix.det ≠ 0) :
    glOf t.toMatrix h = T01 t.c ∨ glOf t.toMatrix h = T10 t.c := by
  obtain ⟨i, j, hij, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · left
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    simp only [coe_glOf, T01, Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · right
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    simp only [coe_glOf, T10, Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · exact absurd rfl hij

private theorem mc_glOf_toMatrix (t : Matrix.TransvectionStruct (Fin 2) F)
    (h : t.toMatrix.det ≠ 0) : mc (glOf t.toMatrix h) = 1 := by
  rcases glOf_toMatrix_eq t h with h' | h' <;> rw [h']
  · exact mc_T01 _
  · exact mc_T10 _

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
private theorem det_prod_toMatrix_ne_zero (L : List (Matrix.TransvectionStruct (Fin 2) F)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det ≠ 0 := by
  rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero

private theorem mc_glOf_prod (L : List (Matrix.TransvectionStruct (Fin 2) F)) :
    mc (glOf (L.map Matrix.TransvectionStruct.toMatrix).prod
        (det_prod_toMatrix_ne_zero L)) = 1 := by
  induction L with
  | nil =>
    have : glOf (([] : List (Matrix.TransvectionStruct (Fin 2) F)).map
          Matrix.TransvectionStruct.toMatrix).prod
        (det_prod_toMatrix_ne_zero []) = 1 := Units.ext (by simp)
    rw [this, map_one]
  | cons t L ih =>
    have ht : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
    have hsplit : glOf ((t :: L).map Matrix.TransvectionStruct.toMatrix).prod
        (det_prod_toMatrix_ne_zero (t :: L)) =
        glOf t.toMatrix ht * glOf (L.map Matrix.TransvectionStruct.toMatrix).prod
          (det_prod_toMatrix_ne_zero L) := Units.ext (by simp)
    rw [hsplit, map_mul, mc_glOf_toMatrix, ih, one_mul]

private theorem modularCharacter_eq_one (g : GL (Fin 2) F) : modularCharacter g = 1 := by
  obtain ⟨L, L', D, hg⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin 2) (Fin 2) F)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
    Matrix.TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, Fin.prod_univ_two, one_mul,
    mul_one] at hdet
  have hD0 : D 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hD1 : D 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hdiag : glOf (Matrix.diagonal D) (by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]; exact mul_ne_zero hD0 hD1) = Dg hD0 hD1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [coe_glOf, Dg]
    fin_cases i <;> fin_cases j <;> simp
  have hgU : g = glOf (L.map Matrix.TransvectionStruct.toMatrix).prod
      (det_prod_toMatrix_ne_zero L) *
      glOf (Matrix.diagonal D) (by
        rw [Matrix.det_diagonal, Fin.prod_univ_two]; exact mul_ne_zero hD0 hD1) *
      glOf (L'.map Matrix.TransvectionStruct.toMatrix).prod (det_prod_toMatrix_ne_zero L') := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glOf, coe_glOf, coe_glOf]
    exact hg
  change mc g = 1
  rw [hgU, map_mul, map_mul, mc_glOf_prod, mc_glOf_prod, hdiag, mc_Dg, one_mul, one_mul]

end GL2HaarAux

namespace Matrix.GeneralLinearGroup

/-- The modular character of `GL (2, F)` is trivial: `GL (2, F)` is unimodular. -/
theorem modularCharacter_fin_two_eq_one
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1 :=
  GL2HaarAux.modularCharacter_eq_one g

/-- Every Haar measure on `GL (2, F)` is right-invariant and inversion-invariant. -/
theorem isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : MeasureTheory.Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  have hright : μ.IsMulRightInvariant := ⟨fun g => by
    have hmc : MeasureTheory.Measure.modularCharacterFun g = 1 :=
      modularCharacter_fin_two_eq_one g
    rw [MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul μ g, hmc,
      one_smul]⟩
  refine ⟨hright, ?_⟩
  constructor
  let c : ℝ≥0 := MeasureTheory.Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : MeasureTheory.Measure.map Inv.inv (MeasureTheory.Measure.map Inv.inv μ) =
      c ^ 2 • μ := by
    rw [← MeasureTheory.Measure.inv_def μ, hc,
      MeasureTheory.Measure.map_smul _ continuous_inv.aemeasurable,
      ← MeasureTheory.Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [MeasureTheory.Measure.map_map continuous_inv.measurable continuous_inv.measurable]
      at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, MeasureTheory.Measure.map_id]
      using h2
  have K : TopologicalSpace.PositiveCompacts (GL (Fin 2) F) := Classical.arbitrary _
  have h3 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h4 : (c : ENNReal) ^ 2 = (1 : ENNReal) ^ 2 :=
    (ENNReal.mul_left_inj (MeasureTheory.Measure.measure_pos_of_nonempty_interior _
          K.interior_nonempty).ne' K.isCompact.measure_lt_top.ne).1 h3
  have h5 : (c : ENNReal) = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  have h6 : c = 1 := by exact_mod_cast h5
  rw [hc, h6, one_smul]

end Matrix.GeneralLinearGroup
