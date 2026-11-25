/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney

/-!
# Bisimplicial Alexander--Whitney differential expansions

This file expands both sides of the desired Alexander--Whitney chain-map
identity.  Composing a cut summand with the signed total differential gives
its horizontal and signed vertical boundary terms.  Composing the diagonal
alternating differential with the degreewise component gives the double sum
of factored diagonal faces.

The subsequent cut-face and crossover cancellation is not asserted here.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- Differential of a bidegree inclusion in the signed total complex. -/
@[reassoc]
theorem totalιOfEq_comp_d
    (p q n : ℕ) (h : p + q = n + 1) :
    (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) p q (n + 1) h ≫
        (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).d
          (n + 1) n =
      (if hp : p = 0 then
          (0 : ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).X q ⟶
            (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n)
        else
          ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).d p (p - 1)).f q ≫
            totalιOfEq B (p - 1) q n (by omega)) +
      (if hq : q = 0 then
          (0 : ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).X q ⟶
            (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n)
        else
          ((-1 : ℤ) ^ p) •
            (((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).d q (q - 1) ≫
              totalιOfEq B p (q - 1) n (by omega))) := by
  let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
  dsimp only [totalιOfEq]
  change K.ιTotal (ComplexShape.down ℕ) p q (n + 1) h ≫
      (K.D₁ (ComplexShape.down ℕ) (n + 1) n +
        K.D₂ (ComplexShape.down ℕ) (n + 1) n) = _
  simp only [Preadditive.comp_add, K.ι_D₁, K.ι_D₂]
  have hd₁ : K.d₁ (ComplexShape.down ℕ) p q n =
      if hp : p = 0 then 0 else
        (K.d p (p - 1)).f q ≫
          K.ιTotal (ComplexShape.down ℕ) (p - 1) q n (by
            change (p - 1) + q = n
            omega) := by
    by_cases hp : p = 0
    · subst p
      rw [dite_eq_left rfl]
      exact K.d₁_eq_zero (ComplexShape.down ℕ) 0 q n (by simp)
    · rw [dite_eq_right hp,
        K.d₁_eq (ComplexShape.down ℕ)
          (ComplexShape.down_mk p (p - 1) (by omega)) q n (by
            change (p - 1) + q = n
            omega)]
      simp only [ComplexShape.ε₁_def, one_smul]
  have hd₂ : K.d₂ (ComplexShape.down ℕ) p q n =
      if hq : q = 0 then 0 else
        ((-1 : ℤ) ^ p) •
          ((K.X p).d q (q - 1) ≫
            K.ιTotal (ComplexShape.down ℕ) p (q - 1) n (by
              change p + (q - 1) = n
              omega)) := by
    by_cases hq : q = 0
    · subst q
      rw [dite_eq_left rfl]
      exact K.d₂_eq_zero (ComplexShape.down ℕ) p 0 n (by simp)
    · rw [dite_eq_right hq,
        K.d₂_eq (ComplexShape.down ℕ) p
          (ComplexShape.down_mk q (q - 1) (by omega)) n (by
            change p + (q - 1) = n
            omega)]
      simp only [Units.smul_def]
      rfl
  rw [hd₁, hd₂]
  rfl

omit [Preadditive A] [Limits.HasFiniteCoproducts A] in
/-- A diagonal face is the inner face followed by the outer face. -/
theorem diagonal_δ (n : ℕ) (i : Fin (n + 2)) :
    ((SimplicialObject.diagonalFunctor A).obj B).δ i =
      (B.obj (Opposite.op ⦋n + 1⦌)).δ i ≫
        (B.δ i).app (Opposite.op ⦋n⦌) := by
  change ((SimplicialObject.diagonalFunctor A).obj B).map
      (SimplexCategory.δ i).op = _
  exact SimplicialObject.diagonalFunctor_obj_map A B (SimplexCategory.δ i).op

/-- Expansion of the Alexander--Whitney component followed by the signed
total differential. -/
theorem component_comp_total_d_eq_bidegree_sum (n : ℕ) :
    component B (n + 1) ≫
        (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).d
          (n + 1) n =
      ∑ p : Fin (n + 2),
        (let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
         let q := cutComplement (n + 1) p
         have h : p.val + q = n + 1 := cut_add (n + 1) p
         faceToBidegreeOfEq B p.val q (n + 1) h ≫
           ((if hp : p.val = 0 then
               (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
             else
               (K.d p.val (p.val - 1)).f q ≫
                 K.ιTotal (ComplexShape.down ℕ)
                   (p.val - 1) q n (by
                     change (p.val - 1) + q = n
                     omega)) +
            (if hq : q = 0 then
               (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
             else
               ((-1 : ℤ) ^ p.val) •
                 ((K.X p.val).d q (q - 1) ≫
                   K.ιTotal (ComplexShape.down ℕ)
                     p.val (q - 1) n (by
                       change p.val + (q - 1) = n
                       omega))))) := by
  rw [component_eq_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  unfold summand
  let face := faceToBidegreeOfEq B p.val (cutComplement (n + 1) p)
    (n + 1) (cut_add (n + 1) p)
  have htot := totalιOfEq_comp_d B p.val
    (cutComplement (n + 1) p) n (cut_add (n + 1) p)
  exact (Category.assoc _ _ _).trans (face ≫= htot)

/-- Expansion of the diagonal alternating differential followed by the
Alexander--Whitney component. -/
theorem diagonal_d_comp_component_eq_double_sum (n : ℕ) :
    (diagonalAlternatingComplex B).d (n + 1) n ≫ component B n =
      ∑ i : Fin (n + 2),
        ∑ p : Fin (n + 1),
          (((-1 : ℤ) ^ i.val) •
            ((B.obj (Opposite.op ⦋n + 1⦌)).δ i ≫
              (B.δ i).app (Opposite.op ⦋n⦌))) ≫
            summand B n p := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
      (((SimplicialObject.diagonalFunctor A).obj B).δ i)) ≫
        (∑ p : Fin (n + 1),
          summand B n p) = _
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [diagonal_δ]
  rfl

end AlgebraicTopology.BisimplicialAlexanderWhitney
