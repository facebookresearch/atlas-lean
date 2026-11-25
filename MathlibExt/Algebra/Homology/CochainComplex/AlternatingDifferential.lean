/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Linear.Basic
public import MathlibExt.Algebra.Ring.NegOnePow

/-!
# Changing the target-degree sign of a cochain differential

The objects and morphism components remain the objects and
components. Multiplying `d i j` by `j.negOnePow` gives another cochain
complex, naturally isomorphic to the by the triangular signs.
This is the sign comparison needed for the two total-Hom conventions.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The cochain objects with differential `(-1)^j d i j`. -/
def alternatingDifferential (K : CochainComplex C ℤ) : CochainComplex C ℤ where
  X := K.X
  d i j := j.negOnePow • K.d i j
  shape i j hij := by rw [K.shape i j hij, smul_zero]
  d_comp_d' i j k hij hjk := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, K.d_comp_d,
      smul_zero, smul_zero]

@[simp]
theorem alternatingDifferential_X (K : CochainComplex C ℤ) (i : ℤ) :
    (alternatingDifferential K).X i = K.X i := rfl

@[simp]
theorem alternatingDifferential_d (K : CochainComplex C ℤ) (i j : ℤ) :
    (alternatingDifferential K).d i j = j.negOnePow • K.d i j := rfl

/-- The morphism components commute with both signed differentials. -/
def alternatingDifferentialMap {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    alternatingDifferential K ⟶ alternatingDifferential L where
  f := f.f
  comm' i j hij := by
    change f.f i ≫ (j.negOnePow • L.d i j) = (j.negOnePow • K.d i j) ≫ f.f j
    rw [Linear.comp_units_smul, Linear.units_smul_comp, f.comm]

@[simp]
theorem alternatingDifferentialMap_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    (alternatingDifferentialMap f).f i = f.f i := rfl

/-- Changing the signs is functorial on the components. -/
def alternatingDifferentialFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := alternatingDifferential
  map := alternatingDifferentialMap
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext i
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    rfl

/-- The scalar comparison to the cochain complex. -/
def alternatingDifferentialIso (K : CochainComplex C ℤ) :
    alternatingDifferential K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := alternatingDifferential K) (C₂ := K)
    (fun i => Int.triangularSign i • Iso.refl (K.X i)) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      change (Int.triangularSign i • 𝟙 (K.X i)) ≫ K.d i (i + 1) =
        ((i + 1).negOnePow • K.d i (i + 1)) ≫
          (Int.triangularSign (i + 1) • 𝟙 (K.X (i + 1)))
      rw [Linear.units_smul_comp, Category.id_comp, Linear.comp_units_smul,
        Category.comp_id, smul_smul, Int.triangularSign_succ_mul_negOnePow])

@[simp]
theorem alternatingDifferentialIso_hom_f (K : CochainComplex C ℤ) (i : ℤ) :
    (alternatingDifferentialIso K).hom.f i = Int.triangularSign i • 𝟙 (K.X i) := rfl

@[simp]
theorem alternatingDifferentialIso_inv_f (K : CochainComplex C ℤ) (i : ℤ) :
    (alternatingDifferentialIso K).inv.f i = (Int.triangularSign i)⁻¹ • 𝟙 (K.X i) := rfl

/-- The sign comparisons form a natural isomorphism to the identity. -/
def alternatingDifferentialNatIso :
    alternatingDifferentialFunctor (C := C) ≅ 𝟭 (CochainComplex C ℤ) :=
  NatIso.ofComponents alternatingDifferentialIso (by
    intro K L f
    apply HomologicalComplex.Hom.ext
    funext i
    change f.f i ≫ (Int.triangularSign i • 𝟙 (L.X i)) =
      (Int.triangularSign i • 𝟙 (K.X i)) ≫ f.f i
    rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.comp_id, Category.id_comp])

end CochainComplex
