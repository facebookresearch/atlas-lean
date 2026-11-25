/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Signed rows in total degree

For a nonnegative bicomplex and a first-coordinate degree p, its pth
row is placed in total degree p + q. Its vertical differential is
multiplied by the totalization sign (-1)^p.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The `p`th row of a natural bicomplex with its differential multiplied by
the vertical sign occurring in the total complex. -/
@[simps! X d]
noncomputable def signedRow (p : ℕ) : ChainComplex C ℕ where
  X q := (B.X p).X q
  d q q' := (ComplexShape.down ℕ).ε p • (B.X p).d q q'
  shape q q' h := by
    rw [(B.X p).shape q q' h, smul_zero]
  d_comp_d' q q' q'' _ _ := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      HomologicalComplex.d_comp_d, smul_zero]

/-- The signed `p`th row, extended by zero so that row degree `q` occurs in
total degree `p + q`. -/
noncomputable def totalRow (p : ℕ) : ChainComplex C ℕ :=
  (B.signedRow p).extend (ComplexShape.embeddingDown'Add 1 p)

/-- The coordinate isomorphism from the signed extended row in total degree
`p + q` to the original bicomplex entry in bidegree `(p,q)`. -/
noncomputable def totalRowXIso (p q n : ℕ) (h : p + q = n) :
    (B.totalRow p).X n ≅ (B.X p).X q :=
  (B.signedRow p).extendXIso (ComplexShape.embeddingDown'Add 1 p) (by
    change q + p = n
    omega)

/-- Below total degree `p`, the signed extended `p`th row is zero. -/
theorem totalRow_isZero_X (p n : ℕ) (h : n < p) :
    IsZero ((B.totalRow p).X n) := by
  apply (B.signedRow p).isZero_extend_X
    (ComplexShape.embeddingDown'Add 1 p)
  intro q hq
  change q + p = n at hq
  omega

/-- The differential of the signed extended row in row coordinates. -/
theorem totalRow_d_eq (p q q' n n' : ℕ)
    (h : p + q = n) (h' : p + q' = n') :
    (B.totalRow p).d n n' =
      (B.totalRowXIso p q n h).hom ≫
        ((ComplexShape.down ℕ).ε p • (B.X p).d q q') ≫
        (B.totalRowXIso p q' n' h').inv := by
  change ((B.signedRow p).extend
      (ComplexShape.embeddingDown'Add 1 p)).d n n' = _
  apply HomologicalComplex.extend_d_eq

/-- The quotient-facing form of the signed-row differential formula. -/
@[reassoc]
theorem totalRowXIso_inv_comp_d (p q q' n n' : ℕ)
    (h : p + q = n) (h' : p + q' = n') :
    (B.totalRowXIso p q n h).inv ≫ (B.totalRow p).d n n' =
      ((ComplexShape.down ℕ).ε p • (B.X p).d q q') ≫
        (B.totalRowXIso p q' n' h').inv := by
  rw [B.totalRow_d_eq p q q' n n' h h', Iso.inv_hom_id_assoc]

variable {B}
variable {B' B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex morphism induces a morphism between its signed rows. -/
@[simps! f]
def signedRowMap (φ : B ⟶ B') (p : ℕ) :
    B.signedRow p ⟶ B'.signedRow p where
  f q := (φ.f p).f q
  comm' q q' _ := by
    change (φ.f p).f q ≫
        ((ComplexShape.down ℕ).ε p • (B'.X p).d q q') =
      ((ComplexShape.down ℕ).ε p • (B.X p).d q q') ≫
        (φ.f p).f q'
    rw [Linear.comp_units_smul, Linear.units_smul_comp, (φ.f p).comm]

/-- A bicomplex morphism induces a morphism between its signed extended
rows. -/
noncomputable def totalRowMap (φ : B ⟶ B') (p : ℕ) :
    B.totalRow p ⟶ B'.totalRow p :=
  HomologicalComplex.extendMap (signedRowMap φ p)
    (ComplexShape.embeddingDown'Add 1 p)

/-- The component of `totalRowMap` in a degree in the shifted row's
support. -/
theorem totalRowMap_f (φ : B ⟶ B') (p q n : ℕ) (h : p + q = n) :
    (totalRowMap φ p).f n =
      (B.totalRowXIso p q n h).hom ≫ (φ.f p).f q ≫
        (B'.totalRowXIso p q n h).inv := by
  change (HomologicalComplex.extendMap (signedRowMap φ p)
    (ComplexShape.embeddingDown'Add 1 p)).f n = _
  apply HomologicalComplex.extendMap_f

omit [HasZeroObject C] in
@[simp]
theorem signedRowMap_id (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p : ℕ) :
    signedRowMap (𝟙 B) p = 𝟙 _ := by
  ext q
  rfl

omit [HasZeroObject C] in
@[simp, reassoc]
theorem signedRowMap_comp (φ : B ⟶ B') (ψ : B' ⟶ B'') (p : ℕ) :
    signedRowMap (φ ≫ ψ) p = signedRowMap φ p ≫ signedRowMap ψ p := by
  ext q
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem totalRowMap_id (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p : ℕ) :
    totalRowMap (𝟙 B) p = 𝟙 _ := by
  dsimp only [totalRowMap]
  rw [signedRowMap_id, HomologicalComplex.extendMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem totalRowMap_comp (φ : B ⟶ B') (ψ : B' ⟶ B'') (p : ℕ) :
    totalRowMap (φ ≫ ψ) p = totalRowMap φ p ≫ totalRowMap ψ p := by
  dsimp only [totalRowMap]
  rw [signedRowMap_comp, HomologicalComplex.extendMap_comp]

/-- The signed row in a fixed outer degree, functorial in the bicomplex. -/
noncomputable abbrev totalRowFunctor (p : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ChainComplex C ℕ where
  obj B := B.totalRow p
  map φ := totalRowMap φ p
  map_id B := totalRowMap_id B p
  map_comp φ ψ := totalRowMap_comp φ ψ p

@[simp]
theorem totalRowFunctor_obj (p : ℕ)
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (totalRowFunctor (C := C) p).obj B = B.totalRow p :=
  rfl

@[simp]
theorem totalRowFunctor_map (p : ℕ) (φ : B ⟶ B') :
    (totalRowFunctor (C := C) p).map φ = totalRowMap φ p :=
  rfl

/-- The zero signed row in total degree is canonically the original zero column.
This is the native extension-coordinate isomorphism, with no homology assumption. -/
noncomputable def totalRowZeroIso
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    B.totalRow 0 ≅ B.X 0 :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ B.totalRowXIso 0 q q (Nat.zero_add q))
    (fun i j _ ↦ by
      rw [B.totalRow_d_eq 0 i j i j (Nat.zero_add i) (Nat.zero_add j)]
      simp)

/-- The zero-row comparison uses the original native extension coordinate. -/
@[simp]
theorem totalRowZeroIso_hom_f
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (n : ℕ) :
    (B.totalRowZeroIso).hom.f n = (B.totalRowXIso 0 n n (Nat.zero_add n)).hom := rfl

/-- Its inverse uses the inverse of that same native coordinate. -/
@[simp]
theorem totalRowZeroIso_inv_f
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (n : ℕ) :
    (B.totalRowZeroIso).inv.f n = (B.totalRowXIso 0 n n (Nat.zero_add n)).inv := rfl

/-- Original bicomplex maps commute with the canonical zero-row comparison. -/
@[reassoc]
theorem totalRowZeroIso_hom_naturality
    {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ : B ⟶ B') :
    totalRowMap φ 0 ≫ B'.totalRowZeroIso.hom = B.totalRowZeroIso.hom ≫ φ.f 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (totalRowMap φ 0).f n ≫ (B'.totalRowXIso 0 n n (Nat.zero_add n)).hom =
    (B.totalRowXIso 0 n n (Nat.zero_add n)).hom ≫ (φ.f 0).f n
  rw [totalRowMap_f φ 0 n n (Nat.zero_add n)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex₂

end
