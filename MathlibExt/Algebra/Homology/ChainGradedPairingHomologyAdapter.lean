/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingHomology
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]

omit [MonoidalPreadditive C] in
@[reassoc]
lemma ιTensorObj_comp_XIsoOfEq
    (K₁ K₂ : ChainComplex C ℕ) [K₁.HasTensor K₂]
    (p q n n' : ℕ) (h : p + q = n) (e : n = n') :
    ιTensorObj K₁ K₂ p q n h ≫ ((tensorObj K₁ K₂).XIsoOfEq e).hom =
      ιTensorObj K₁ K₂ p q n' (h.trans e) := by
  subst e
  simp

namespace ChainGradedPairing

variable {K₁ K₂ K₃ : ChainComplex C ℕ} [K₁.HasTensor K₂]

omit [MonoidalPreadditive C] in
lemma pair_comp_d_of_eq
    (P : ChainGradedPairing K₁ K₂ K₃) (p q n : ℕ) (h : p + q = n + 1) :
    P.pair p q ≫ K₃.d (p + q) n =
      ((if hp : p = 0 then
          (0 : K₁.X p ⊗ K₂.X q ⟶ (tensorObj K₁ K₂).X n)
        else
          (K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X q)) ≫
            ιTensorObj K₁ K₂ (p - 1) q n (by omega)) +
        (if hq : q = 0 then
          (0 : K₁.X p ⊗ K₂.X q ⟶ (tensorObj K₁ K₂).X n)
        else
          ((-1 : ℤ) ^ p) •
            ((𝟙 (K₁.X p) ⊗ₘ K₂.d q (q - 1)) ≫
              ιTensorObj K₁ K₂ p (q - 1) n (by omega)))) ≫ P.f n := by
  let e : p + q = n + 1 := h
  calc
    P.pair p q ≫ K₃.d (p + q) n =
        ιTensorObj K₁ K₂ p q (p + q) rfl ≫
          P.f (p + q) ≫ K₃.d (p + q) n := by rw [pair, Category.assoc]
    _ = ιTensorObj K₁ K₂ p q (p + q) rfl ≫
        (tensorObj K₁ K₂).d (p + q) n ≫ P.f n := by rw [P.comm]
    _ = ιTensorObj K₁ K₂ p q (p + q) rfl ≫
        ((tensorObj K₁ K₂).XIsoOfEq e).hom ≫
          (tensorObj K₁ K₂).d (n + 1) n ≫ P.f n := by
            simp only [(tensorObj K₁ K₂).XIsoOfEq_hom_comp_d_assoc]
    _ = ιTensorObj K₁ K₂ p q (n + 1) h ≫
        (tensorObj K₁ K₂).d (n + 1) n ≫ P.f n := by
          rw [← Category.assoc, ιTensorObj_comp_XIsoOfEq]
    _ = _ := by rw [← Category.assoc, ιTensorObj_comp_d_down_nat]

lemma cycles_d_of_chainMap
    (P : ChainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q] :
    ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P.pair p q) ≫
      K₃.d (p + q) ((ComplexShape.down ℕ).next (p + q)) = 0 := by
  rcases p with _ | p
  · rcases q with _ | q
    · simp [pair]
    · have hnext : (ComplexShape.down ℕ).next (0 + (q + 1)) = q := by simp
      have h₂ : (K₁.iCycles 0 ⊗ₘ K₂.iCycles (q + 1)) ≫
          (𝟙 (K₁.X 0) ⊗ₘ K₂.d (q + 1) q) = 0 := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, K₂.iCycles_d]
        simp [MonoidalCategory.tensorHom_def]
      rw [hnext, Category.assoc, pair_comp_d_of_eq P 0 (q + 1) q (by omega)]
      rw [← Category.assoc, Preadditive.comp_add]
      simp only [dite_eq_left True.intro, dite_eq_right (Nat.succ_ne_zero q),
        Nat.succ_sub_one, pow_zero, one_smul, comp_zero, zero_add,
        ← Category.assoc, h₂, zero_comp]
  · have hnext : (ComplexShape.down ℕ).next ((p + 1) + q) = p + q := by
      rw [show p + 1 + q = (p + q) + 1 by omega, ChainComplex.next_nat_succ]
    have h₁ : (K₁.iCycles (p + 1) ⊗ₘ K₂.iCycles q) ≫
        (K₁.d (p + 1) p ⊗ₘ 𝟙 (K₂.X q)) = 0 := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, K₁.iCycles_d]
      simp [MonoidalCategory.tensorHom_def]
    have h₂ : (K₁.iCycles (p + 1) ⊗ₘ K₂.iCycles q) ≫
        (𝟙 (K₁.X (p + 1)) ⊗ₘ K₂.d q (q - 1)) = 0 := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, K₂.iCycles_d]
      simp [MonoidalCategory.tensorHom_def]
    rw [hnext, Category.assoc, pair_comp_d_of_eq P (p + 1) q (p + q) (by omega)]
    rw [← Category.assoc, Preadditive.comp_add]
    simp only [dite_eq_right (Nat.succ_ne_zero p), Nat.succ_sub_one]
    by_cases hq : q = 0
    · simp only [dite_eq_left hq, comp_zero, add_zero, ← Category.assoc, h₁, zero_comp]
    · rw [dite_eq_right hq, Preadditive.comp_zsmul]
      simp only [← Category.assoc, h₁, h₂, zero_comp, smul_zero, add_zero]

lemma left_factor_of_chainMap
    (P : ChainGradedPairing K₁ K₂ K₃) (p q : ℕ) [K₂.HasHomology q] :
    ∃ (i' : ℕ) (x : K₁.X (p + 1) ⊗ K₂.cycles q ⟶ K₃.X i'),
      (K₁.d (p + 1) p ⊗ₘ K₂.iCycles q) ≫ P.pair p q =
        x ≫ K₃.d i' (p + q) := by
  refine ⟨(p + 1) + q,
    (𝟙 (K₁.X (p + 1)) ⊗ₘ K₂.iCycles q) ≫ P.pair (p + 1) q, ?_⟩
  have h₁ : (𝟙 (K₁.X (p + 1)) ⊗ₘ K₂.iCycles q) ≫
      (K₁.d (p + 1) p ⊗ₘ 𝟙 (K₂.X q)) =
      K₁.d (p + 1) p ⊗ₘ K₂.iCycles q := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have h₂ : (𝟙 (K₁.X (p + 1)) ⊗ₘ K₂.iCycles q) ≫
      (𝟙 (K₁.X (p + 1)) ⊗ₘ K₂.d q (q - 1)) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₂.iCycles_d]
    simp
  symm
  rw [Category.assoc, pair_comp_d_of_eq P (p + 1) q (p + q) (by omega)]
  rw [← Category.assoc, Preadditive.comp_add]
  simp only [dite_eq_right (Nat.succ_ne_zero p), Nat.succ_sub_one]
  by_cases hq : q = 0
  · simp only [dite_eq_left hq, comp_zero, add_zero, ← Category.assoc, h₁]
    simp [pair]
  · rw [dite_eq_right hq, Preadditive.comp_zsmul]
    simp only [← Category.assoc, h₁, h₂, zero_comp, smul_zero, add_zero]
    simp [pair]

lemma right_factor_of_chainMap
    (P : ChainGradedPairing K₁ K₂ K₃) (p q : ℕ) [K₁.HasHomology p] :
    ∃ (i' : ℕ) (x : K₁.cycles p ⊗ K₂.X (q + 1) ⟶ K₃.X i'),
      (K₁.iCycles p ⊗ₘ K₂.d (q + 1) q) ≫ P.pair p q =
        x ≫ K₃.d i' (p + q) := by
  refine ⟨p + (q + 1),
    ((-1 : ℤ) ^ p) •
      ((K₁.iCycles p ⊗ₘ 𝟙 (K₂.X (q + 1))) ≫ P.pair p (q + 1)), ?_⟩
  have h₁ : (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X (q + 1))) ≫
      (K₁.d p (p - 1) ⊗ₘ 𝟙 (K₂.X (q + 1))) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, K₁.iCycles_d]
    simp
  have h₂ : (K₁.iCycles p ⊗ₘ 𝟙 (K₂.X (q + 1))) ≫
      (𝟙 (K₁.X p) ⊗ₘ K₂.d (q + 1) q) =
      K₁.iCycles p ⊗ₘ K₂.d (q + 1) q := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  rw [Preadditive.zsmul_comp, Category.assoc,
    pair_comp_d_of_eq P p (q + 1) (p + q) (by omega)]
  rw [← Category.assoc, Preadditive.comp_add]
  simp only [dite_eq_right (Nat.succ_ne_zero q), Nat.succ_sub_one]
  by_cases hp : p = 0
  · rw [dite_eq_left hp]
    simp only [comp_zero, zero_add, Preadditive.comp_zsmul,
      ← Category.assoc, h₂]
    rw [Preadditive.zsmul_comp, smul_smul, hs, one_smul]
    simp [pair]
  · rw [dite_eq_right hp, Preadditive.comp_zsmul]
    simp only [← Category.assoc, h₁, h₂, zero_comp, zero_add]
    rw [Preadditive.zsmul_comp, smul_smul, hs, one_smul]
    simp [pair]

/-- Let C be a preadditive monoidal category whose tensor product is additive in each variable. For
any pairing P : K₁ ⊗ K₂ → K₃ of nonnegative chain complexes with tensor complex defined, the
chain-map law supplies HomologyDescentData P. Thus pairs of cycles map to cycles, while a
boundary paired with a cycle in either variable maps to a boundary in K₃. The right-variable
factor uses the Leibniz sign (−1)^p. -/
theorem homologyDescentData (P : ChainGradedPairing K₁ K₂ K₃) :
    HomologyDescentData P where
  cycles_d := cycles_d_of_chainMap P
  left_factor := left_factor_of_chainMap P
  right_factor := right_factor_of_chainMap P

end ChainGradedPairing

end HomologicalComplex

end
