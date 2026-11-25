/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCColumnComparison

/-!
# Literal b and printed degree-signed B arrows of the Loday BC diagram

The full column coordinate change gives the unsigned vertical b and the
printed horizontal (-1)^(n+1)B. The underlying degree n is the original
supported mixed degree. Native totalization supplies the remaining column
sign; the total comparison therefore preserves both actual differential
components rather than changing B in isolation.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
  (M : MixedComplex C)

omit [CategoryTheory.Limits.HasZeroObject C] in
private theorem B_coordinate_transport (i n j : ℕ) (hi : i = n) (hj : j = n + 1)
    (hij : i + 1 = j) :
    M.B i ≫ eqToHom (congrArg M.underlying.X hij) =
      eqToHom (congrArg M.underlying.X hi) ≫ M.B n ≫
        eqToHom (congrArg M.underlying.X hj.symm) := by
  subst i
  subst j
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

omit [CategoryTheory.Limits.HasZeroObject C] in
private theorem differential_coordinate_transport (i n j p : ℕ)
    (hi : i = n + 1) (hj : j = n) (hij : i = j + 1) :
    ((-1 : ℤˣ) ^ p) •
        (eqToHom (congrArg M.underlying.X hij) ≫ ((-1 : ℤ) ^ p • M.mixedDifferential j)) =
      eqToHom (congrArg M.underlying.X hi) ≫ M.underlying.d (n + 1) n ≫
        eqToHom (congrArg M.underlying.X hj.symm) := by
  subst j
  subst i
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Units.smul_def,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, smul_smul,
    ← pow_add, (show Even (p + p) from ⟨p, rfl⟩).neg_one_pow, one_smul]

/-- The printed model retains the same original supported cell coordinates. -/
abbrev lodayBCCellIso (p q : ℕ) (hpq : p ≤ q) :
    (M.lodayBCBicomplex.X p).X q ≅ M.underlying.X (q - p) :=
  M.connesBicomplexCellIso p q hpq

/-- In original source/target cell coordinates, the horizontal printed arrow is (-1)^(n+1)B. -/
theorem lodayBC_horizontal_coordinate (p n : ℕ) :
    (M.lodayBCCellIso (p + 1) (n + p + 1) (by omega)).inv ≫
      (M.lodayBCHorizontal p).f (n + p + 1) ≫
        (M.lodayBCCellIso p (n + p + 1) (by omega)).hom =
      ((-1 : ℤˣ) ^ (n + 1)) •
        (eqToHom (congrArg M.underlying.X (by omega : n + p + 1 - (p + 1) = n)) ≫
          M.B n ≫ eqToHom (congrArg M.underlying.X (by omega : n + 1 = n + p + 1 - p))) := by
  dsimp only [lodayBCHorizontal]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    M.lodayBCColumnIso_hom_f, M.lodayBCColumnIso_inv_f]
  erw [M.connesDoubleData.horizontal_eq p (n + p + 1) (by omega)]
  dsimp only [lodayBCCellIso, lodayBCColumn, HomologicalComplex₂.signedRow,
    lodayBCBicomplex, connesDoubleData] at ⊢
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
    Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Nat.add_sub_add_right, Nat.add_sub_cancel, smul_smul]
  rw [mul_comm (lodayCellSign p (n + p + 1)), lodayCellSign_horizontal_degree]
  exact congrArg (fun f => ((-1 : ℤˣ) ^ (n + 1)) • f)
    (B_coordinate_transport M (n + p + 1 - (p + 1)) n (n + p + 1 - p)
      (by omega) (by omega) (by omega))

/-- The actual unsigned stored vertical arrow is the original b in supported cell coordinates. -/
theorem lodayBC_vertical_coordinate (p n : ℕ) :
    (M.lodayBCCellIso p (n + p + 1) (by omega)).inv ≫
      (M.lodayBCColumn p).d (n + p + 1) (n + p) ≫
        (M.lodayBCCellIso p (n + p) (by omega)).hom =
      eqToHom (congrArg M.underlying.X (by omega : n + p + 1 - p = n + 1)) ≫
        M.underlying.d (n + 1) n ≫
          eqToHom (congrArg M.underlying.X (by omega : n = n + p - p)) := by
  change (M.connesBicomplexCellIso p (n + p + 1) (by omega)).inv ≫
      (((ComplexShape.down ℕ).ε p) • (M.connesBicomplex.X p).d (n + p + 1) (n + p)) ≫
        (M.connesBicomplexCellIso p (n + p) (by omega)).hom = _
  have hd := M.connesDoubleData.vertical_eq p (n + p) (by omega)
  erw [hd]
  dsimp only [lodayBCCellIso, lodayBCColumn, HomologicalComplex₂.signedRow,
    lodayBCBicomplex, connesDoubleData] at ⊢
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Nat.add_sub_cancel,
    eqToHom_refl, Category.id_comp]
  rw [ComplexShape.ε_down_ℕ]
  exact differential_coordinate_transport M (n + p + 1 - p) n (n + p - p) p
    (by omega) (by omega) (by omega)

/-- The printed arrows satisfy the genuine commuting-column chain square, with the original b intact. -/
theorem lodayBC_horizontal_comm (p q : ℕ) :
    (M.lodayBCHorizontal p).f (q + 1) ≫ (M.lodayBCColumn p).d (q + 1) q =
      (M.lodayBCColumn (p + 1)).d (q + 1) q ≫ (M.lodayBCHorizontal p).f q :=
  (M.lodayBCHorizontal p).comm (q + 1) q

section Total

variable [CategoryTheory.Limits.HasFiniteCoproducts C]

/-- The actual full coordinate comparison is a chain isomorphism on the original total differential. -/
theorem lodayBCTotalIso_comm (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ (M.connesBicomplex.total (ComplexShape.down ℕ)).d i j =
      (M.lodayBCBicomplex.total (ComplexShape.down ℕ)).d i j ≫ M.lodayBCTotalIso.hom.f j :=
  M.lodayBCTotalIso.hom.comm i j

end Total

end MixedComplex
