/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Tactic.Abel

/-!
# The alternating face complex with the final face omitted

For an semisimplicial object, omit the final face from each alternating
sum. The original degree-zero term is retained. The same two-region finite-sum
pairing as for the full alternating differential proves square zero from the
semisimplicial face identity, in every degree. No augmentation,
degeneracy, unit or additional compatibility witness is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Category CategoryTheory.Preadditive
open scoped Simplicial

universe u v

namespace AlgebraicTopology

namespace TruncatedAlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : SemiSimplicialObject C)

/-- The original alternating face sum with its final face omitted. -/
def objD (n : ℕ) : X _⦋n + 1⦌ₛ ⟶ X _⦋n⦌ₛ :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • X.δ i.castSucc

/-- The truncated differential squares to zero, including the bottom square. -/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  dsimp only [objD]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 1) × Fin (n + 2)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · have hji : j ≤ i.castSucc := by
        exact Fin.le_iff_val_le_val.mpr (Finset.mem_filter.mp hij).right
      have hcast : i.castSucc.succ = i.succ.castSucc := by
        apply Fin.ext
        rfl
      simpa only [φ, Fin.castSucc_castLT, hcast] using
        (SemiSimplicialObject.δ_comp_δ X hji).symm

/-- The truncated chain complex on the original terms, including `X₀`. -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _⦋n⦌ₛ) (objD X) (d_squared X)

/-- Truncation changes the differential, not the original degreewise objects. -/
@[simp]
theorem obj_X (n : ℕ) : (obj X).X n = X _⦋n⦌ₛ := rfl

/-- The adjacent differential is exactly the truncated alternating sum. -/
@[simp]
theorem obj_d (n : ℕ) : (obj X).d (n + 1) n = objD X n := by
  simp only [obj, ChainComplex.of_d]

variable {X Y}

/-- The original semisimplicial morphism gives the degreewise chain map. -/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌ₛ)) fun n => by
    simp only [obj, ChainComplex.of_d, objD]
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [comp_zsmul, zsmul_comp]
    congr 1
    exact (f.naturality (SemiSimplexCategory.δ i.castSucc).op).symm

/-- The chain map retains the original component. -/
@[simp]
theorem map_f (f : X ⟶ Y) (n : ℕ) : (map f).f n = f.app (op ⦋n⦌ₛ) := rfl


section FrontInsertion

variable (X : SemiSimplicialObject C)
  (s : ∀ n : ℕ, X _⦋n⦌ₛ ⟶ X _⦋n + 1⦌ₛ)
  (hFirst : ∀ n : ℕ, s n ≫ X.δ (0 : Fin (n + 2)) = 𝟙 (X _⦋n⦌ₛ))
  (hShift : ∀ (n : ℕ) (i : Fin (n + 1)),
    s (n + 1) ≫ X.δ i.succ.castSucc = X.δ i.castSucc ≫ s n)

include hFirst in
/-- The original bottom term is contracted by the first face. -/
theorem frontInsertion_sum_zero : s 0 ≫ objD X 0 = 𝟙 (X _⦋0⦌ₛ) := by
  change s 0 ≫ (∑ i : Fin 1, (-1 : ℤ) ^ i.val • X.δ i.castSucc) = 𝟙 (X _⦋0⦌ₛ)
  rw [Fin.sum_univ_one]
  simpa only [Fin.val_zero, Fin.castSucc_zero, pow_zero, one_smul] using hFirst 0

include hFirst hShift in
/-- The shifted retained faces cancel the two truncated differentials. -/
theorem frontInsertion_sum_succ (n : ℕ) :
    objD X n ≫ s n + s (n + 1) ≫ objD X (n + 1) = 𝟙 (X _⦋n + 1⦌ₛ) := by
  have hs : s (n + 1) ≫ objD X (n + 1) =
      𝟙 (X _⦋n + 1⦌ₛ) - objD X n ≫ s n := by
    calc
      _ = (s (n + 1) ≫ X.δ (0 : Fin (n + 3))) +
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 1) •
            (s (n + 1) ≫ X.δ i.succ.castSucc) := by
        rw [objD, comp_sum, Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_smul, Fin.castSucc_zero,
          comp_zsmul, Fin.val_succ]
      _ = 𝟙 (X _⦋n + 1⦌ₛ) +
          ∑ i : Fin (n + 1), -(((-1 : ℤ) ^ i.val • X.δ i.castSucc) ≫ s n) := by
        rw [hFirst (n + 1)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hShift n i, pow_succ]
        simp only [mul_neg, mul_one, neg_smul, zsmul_comp]
      _ = _ := by
        simp only [objD, sum_comp, sub_eq_add_neg, Finset.sum_neg_distrib]
  rw [hs]
  abel

include hFirst hShift in
/-- The front insertion gives a native homotopy from the truncated identity to zero. -/
def contractingHomotopy : Homotopy (𝟙 (obj X)) 0 := by
  let H (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
      (obj X).X i ⟶ (obj X).X j := by
    change i + 1 = j at hij
    cases hij
    exact s i
  have hH (i : ℕ) : H i (i + 1) rfl = s i := rfl
  have h : Homotopy.nullHomotopicMap' H = 𝟙 (obj X) := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (k₁ := 1) (k₀ := 0) (by rfl) (by intro l; simp [ComplexShape.down_Rel]) H]
      simp only [hH, HomologicalComplex.id_f, obj_d]
      change s 0 ≫ objD X 0 = 𝟙 (X _⦋0⦌ₛ)
      exact frontInsertion_sum_zero X s hFirst
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f
        (k₂ := n + 2) (k₁ := n + 1) (k₀ := n) (by rfl) (by rfl) H]
      simp only [hH, HomologicalComplex.id_f, obj_d]
      change objD X n ≫ s n + s (n + 1) ≫ objD X (n + 1) = 𝟙 (X _⦋n + 1⦌ₛ)
      exact frontInsertion_sum_succ X s hFirst hShift n
  exact (Homotopy.ofEq h.symm).trans (Homotopy.nullHomotopy' H)

/-- The homotopy has precisely the original insertion component. -/
@[simp]
theorem contractingHomotopy_hom (n : ℕ) :
    (contractingHomotopy X s hFirst hShift).hom n (n + 1) = s n := by
  dsimp only [contractingHomotopy, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  split
  · rfl
  · rename_i hij
    exact (hij rfl).elim

end FrontInsertion

end TruncatedAlternatingFaceMapComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Last-face truncation as a functor to chain complexes. -/
def truncatedAlternatingFaceMapComplex : SemiSimplicialObject C ⥤ ChainComplex C ℕ where
  obj := TruncatedAlternatingFaceMapComplex.obj
  map f := TruncatedAlternatingFaceMapComplex.map f

/-- The functor retains all original objects. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_obj_X (X : SemiSimplicialObject C) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).obj X).X n = X _⦋n⦌ₛ := rfl

/-- Its differential is the truncated face sum. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_obj_d (X : SemiSimplicialObject C) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).obj X).d (n + 1) n =
      TruncatedAlternatingFaceMapComplex.objD X n := by
  exact TruncatedAlternatingFaceMapComplex.obj_d X n

/-- A morphism is mapped using its original component in every degree. -/
@[simp]
theorem truncatedAlternatingFaceMapComplex_map_f {X Y : SemiSimplicialObject C}
    (f : X ⟶ Y) (n : ℕ) :
    ((truncatedAlternatingFaceMapComplex C).map f).f n = f.app (op ⦋n⦌ₛ) := rfl

/-- Truncated alternating-face maps preserve addition of semisimplicial morphisms. -/
instance truncatedAlternatingFaceMapComplexAdditive :
    (truncatedAlternatingFaceMapComplex C).Additive where

end AlgebraicTopology
