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
# The b and B arrows in supported BC cell coordinates

Let M be a mixed complex in a preadditive category with zero object. For p≤q, the BC cell (p,q)
identifies with M_{q-p}. Its vertical arrow from underlying degree n+1 to n is unsigned b_n. Its
horizontal arrow from column p+1 to p, at q=n+p+1, is (-1)^{n+1}B_n.

The horizontal maps are chain maps of these unsigned columns. Finite-diagonal totalization
supplies the additional vertical factor (-1)^p; the full cell-coordinate comparison intertwines
the resulting total differential with the Connes total differential.
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

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. For p,q∈ℕ with p≤q, the
coefficient object C_BC(p,q) is isomorphic to M_{q-p} through the supported Connes cell
identification. This cell identification itself uses the same coefficient object. -/
abbrev lodayBCCellIso (p q : ℕ) (hpq : p ≤ q) :
    (M.lodayBCBicomplex.X p).X q ≅ M.underlying.X (q - p) :=
  M.connesBicomplexCellIso p q hpq

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. For p,n∈ℕ put q=n+p+1. Through
the supported cell isomorphisms C_BC(p+1,q)≅M_n and C_BC(p,q)≅M_{n+1}, the horizontal map is
(-1)^{n+1}B_n. The equality includes the canonical transports of the indices q-(p+1)=n and
q-p=n+1. -/
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

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. For p,n∈ℕ, the supported
vertical map C_BC(p,n+p+1)→C_BC(p,n+p) becomes b_n:M_{n+1}→M_n under the cell identifications.
The index transports are the equalities n+p+1-p=n+1 and n+p-p=n. -/
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

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. For p,q∈ℕ,
d^BC_{p+1,p}(q+1)≫b^BC_p(q+1,q)=b^BC_{p+1}(q+1,q)≫d^BC_{p+1,p}(q). This is the chain-map square
between the two BC columns. -/
theorem lodayBC_horizontal_comm (p q : ℕ) :
    (M.lodayBCHorizontal p).f (q + 1) ≫ (M.lodayBCColumn p).d (q + 1) q =
      (M.lodayBCColumn (p + 1)).d (q + 1) q ≫ (M.lodayBCHorizontal p).f q :=
  (M.lodayBCHorizontal p).comm (q + 1) q

section Total

variable [CategoryTheory.Limits.HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. Assume finite coproducts and
let V:Tot(C_BC)≅Tot(C_can). For i,j∈ℕ, V_i≫d^can_{i,j}=d^BC_{i,j}≫V_j. Both horizontal and
signed vertical total components are included. -/
theorem lodayBCTotalIso_comm (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ (M.connesBicomplex.total (ComplexShape.down ℕ)).d i j =
      (M.lodayBCBicomplex.total (ComplexShape.down ℕ)).d i j ≫ M.lodayBCTotalIso.hom.f j :=
  M.lodayBCTotalIso.hom.comm i j

end Total

end MixedComplex
