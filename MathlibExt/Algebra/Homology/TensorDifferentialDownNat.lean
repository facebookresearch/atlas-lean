/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal

universe v u

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

namespace HomologicalComplex

private lemma d₂_eq_down_nat (K L : ChainComplex C ℕ) [HasTensor K L]
    (p q n : ℕ) (hq : q ≠ 0) (h : p + (q - 1) = n) :
    mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.down ℕ) p q n =
      ((-1 : ℤ) ^ p) • ((𝟙 (K.X p) ⊗ₘ L.d q (q - 1)) ≫
        ιTensorObj K L p (q - 1) n h) := by
  have hRel : (ComplexShape.down ℕ).Rel q (q - 1) := by
    change q - 1 + 1 = q
    omega
  rw [mapBifunctor.d₂_eq K L (curriedTensor C) (ComplexShape.down ℕ) p hRel n h]
  simp
  rfl

public lemma ιTensorObj_comp_d_down_nat
    (K L : ChainComplex C ℕ) [HasTensor K L]
    (p q n : ℕ) (h : p + q = n + 1) :
    ιTensorObj K L p q (n + 1) h ≫ (tensorObj K L).d (n + 1) n =
      (if hp : p = 0 then
          (0 : K.X p ⊗ L.X q ⟶ (tensorObj K L).X n)
        else
          (K.d p (p - 1) ⊗ₘ 𝟙 (L.X q)) ≫
            ιTensorObj K L (p - 1) q n (by omega)) +
      (if hq : q = 0 then
          (0 : K.X p ⊗ L.X q ⟶ (tensorObj K L).X n)
        else
          ((-1 : ℤ) ^ p) •
            ((𝟙 (K.X p) ⊗ₘ L.d q (q - 1)) ≫
              ιTensorObj K L p (q - 1) n (by omega))) := by
  have hD : (tensorObj K L).d (n + 1) n =
      mapBifunctor.D₁ K L (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
      mapBifunctor.D₂ K L (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n := by
    rw [mapBifunctor.d_eq]
  have hd₁ : mapBifunctor.d₁ K L (curriedTensor C) (ComplexShape.down ℕ) p q n =
      (if hp : p = 0 then
        (0 : K.X p ⊗ L.X q ⟶ (tensorObj K L).X n)
      else
        (K.d p (p - 1) ⊗ₘ 𝟙 (L.X q)) ≫
          ιTensorObj K L (p - 1) q n (by omega)) := by
    by_cases hp : p = 0
    · have hNotRel : ¬ (ComplexShape.down ℕ).Rel p
          ((ComplexShape.down ℕ).next p) := by
        rw [hp, ChainComplex.next_nat_zero]
        intro hCon
        change 0 + 1 = 0 at hCon
        omega
      rw [mapBifunctor.d₁_eq_zero K L (curriedTensor C)
        (ComplexShape.down ℕ) p q n hNotRel, dite_eq_left hp]
    · rw [dite_eq_right hp]
      have hRel : (ComplexShape.down ℕ).Rel p (p - 1) := by
        change p - 1 + 1 = p
        omega
      have hPi : p - 1 + q = n := by omega
      rw [mapBifunctor.d₁_eq K L (curriedTensor C)
        (ComplexShape.down ℕ) hRel q n hPi]
      simp
  have hd₂ : mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.down ℕ) p q n =
      (if hq : q = 0 then
        (0 : K.X p ⊗ L.X q ⟶ (tensorObj K L).X n)
      else
        ((-1 : ℤ) ^ p) •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q - 1)) ≫
            ιTensorObj K L p (q - 1) n (by omega))) := by
    by_cases hq : q = 0
    · have hNotRel : ¬ (ComplexShape.down ℕ).Rel q
          ((ComplexShape.down ℕ).next q) := by
        rw [hq, ChainComplex.next_nat_zero]
        intro hCon
        change 0 + 1 = 0 at hCon
        omega
      rw [mapBifunctor.d₂_eq_zero K L (curriedTensor C)
        (ComplexShape.down ℕ) p q n hNotRel, dite_eq_left hq]
    · rw [dite_eq_right hq]
      have hEq : p + (q - 1) = n := by omega
      rw [d₂_eq_down_nat K L p q n hq hEq]
  calc ιTensorObj K L p q (n + 1) h ≫ (tensorObj K L).d (n + 1) n
      _ = _ := by rw [hD]
      _ = _ := by rw [Preadditive.comp_add]
      _ = mapBifunctor.d₁ K L (curriedTensor C) (ComplexShape.down ℕ) p q n +
        mapBifunctor.d₂ K L (curriedTensor C) (ComplexShape.down ℕ) p q n := by
        rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
      _ = _ := by rw [hd₁, hd₂]

end HomologicalComplex
