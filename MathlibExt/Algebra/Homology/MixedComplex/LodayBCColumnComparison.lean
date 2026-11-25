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

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCColumnSigns

/-!
# The full printed BC coordinate comparison

The printed column is the native signed row of the canonical mixed Connes
bicomplex: its internal vertical differential is the unsigned original b.
The explicit triangular column sign times the native signed-row iso determines
the actual horizontal arrows by conjugation. Native component isomorphisms
then give the full bicomplex and finite-diagonal total comparison. No desired
map, invertibility or quasi-isomorphism certificate is an input.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
  (M : MixedComplex C)

/-- The actual printed BC column has the native unsigned row differential. -/
abbrev lodayBCColumn (p : ℕ) : ChainComplex C ℕ := M.connesBicomplex.signedRow p


/-- The full actual column coordinate map, including its triangular constant sign. -/
def lodayBCColumnIso (p : ℕ) : M.lodayBCColumn p ≅ M.connesBicomplex.X p where
  hom := lodayColumnSign p • (M.connesBicomplex.signedRowIso p).hom
  inv := (lodayColumnSign p)⁻¹ • (M.connesBicomplex.signedRowIso p).inv
  hom_inv_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, mul_inv_cancel,
      one_smul, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, inv_mul_cancel,
      one_smul, Iso.inv_hom_id]

/-- Every forward entry coordinate has the exact original cell sign. -/
@[simp]
theorem lodayBCColumnIso_hom_f (p q : ℕ) :
    (M.lodayBCColumnIso p).hom.f q = lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) := by
  change lodayColumnSign p •
      (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 ((M.connesBicomplex.X p).X q)) = _
  rw [smul_smul]
  rfl

/-- Every inverse entry coordinate is the same involutive cell sign. -/
@[simp]
theorem lodayBCColumnIso_inv_f (p q : ℕ) :
    (M.lodayBCColumnIso p).inv.f q = lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) := by
  change (lodayColumnSign p)⁻¹ •
      ((((ComplexShape.down ℕ).ε p) ^ q)⁻¹ • 𝟙 ((M.connesBicomplex.X p).X q)) = _
  have he : ((((ComplexShape.down ℕ).ε p) ^ q)⁻¹) = ((ComplexShape.down ℕ).ε p) ^ q := by
    apply (mul_left_cancel (a := ((ComplexShape.down ℕ).ε p) ^ q))
    rw [mul_inv_cancel]
    rw [ComplexShape.ε_down_ℕ, ← pow_mul]
    rw [← pow_add]
    exact (show Even (p * q + p * q) from ⟨p * q, rfl⟩).neg_one_pow |>.symm
  rw [lodayColumnSign_inv, he, smul_smul]
  rfl

/-- The printed horizontal map is the original canonical map in the full entry coordinates. -/
def lodayBCHorizontal (p : ℕ) : M.lodayBCColumn (p + 1) ⟶ M.lodayBCColumn p :=
  (M.lodayBCColumnIso (p + 1)).hom ≫ M.connesBicomplex.d (p + 1) p ≫
    (M.lodayBCColumnIso p).inv

/-- Original consecutive maps still compose to zero after the actual coordinate changes. -/
theorem lodayBCHorizontal_squared (p : ℕ) :
    M.lodayBCHorizontal (p + 1) ≫ M.lodayBCHorizontal p = 0 := by
  simp only [lodayBCHorizontal, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc (M.connesBicomplex.d (p + 2) (p + 1))
    (M.connesBicomplex.d (p + 1) p)]
  rw [HomologicalComplex.d_comp_d, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- The actual full BC bicomplex in the printed unsigned-column coordinates. -/
def lodayBCBicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of M.lodayBCColumn M.lodayBCHorizontal M.lodayBCHorizontal_squared


/-- The explicit full column maps construct the actual original bicomplex comparison. -/
def lodayBCBicomplexIso : M.lodayBCBicomplex ≅ M.connesBicomplex :=
  HomologicalComplex.Hom.isoOfComponents M.lodayBCColumnIso (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    dsimp only [lodayBCBicomplex]
    rw [ChainComplex.of_d]
    simp only [lodayBCHorizontal, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The whole bicomplex comparison has the original full entry sign in every cell. -/
@[simp]
theorem lodayBCBicomplexIso_hom_f_f (p q : ℕ) :
    ((M.lodayBCBicomplexIso.hom).f p).f q =
      lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) :=
  M.lodayBCColumnIso_hom_f p q

section Total

variable [CategoryTheory.Limits.HasFiniteCoproducts C]

/-- Native finite-diagonal totalization carries the actual full bicomplex coordinate comparison. -/
def lodayBCTotalIso : M.lodayBCBicomplex.total (ComplexShape.down ℕ) ≅
    M.connesBicomplex.total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso M.lodayBCBicomplexIso (ComplexShape.down ℕ)

/-- Every original printed BC coprojection is transported by its full cell sign. -/
@[reassoc]
theorem lodayBCTotalIso_ι (p q n : ℕ) (h : p + q = n) :
    M.lodayBCBicomplex.ιTotal (ComplexShape.down ℕ) p q n h ≫ M.lodayBCTotalIso.hom.f n =
      (lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q)) ≫
        M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q n h := by
  change M.lodayBCBicomplex.ιTotal (ComplexShape.down ℕ) p q n h ≫
      (HomologicalComplex₂.total.map M.lodayBCBicomplexIso.hom (ComplexShape.down ℕ)).f n = _
  exact (HomologicalComplex₂.ιTotal_map M.lodayBCBicomplex M.connesBicomplex
      M.lodayBCBicomplexIso.hom (ComplexShape.down ℕ) p q n h).trans
    (congrArg (fun f => f ≫ M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q n h)
      (M.lodayBCBicomplexIso_hom_f_f p q))

end Total

end MixedComplex
