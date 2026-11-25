/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.Reindexing

/-!
# The bisimplicial Alexander--Whitney chain map

The degreewise Alexander--Whitney components commute with the alternating
differentials.  The proof normalizes the two signed total-complex boundary
sums to target cuts, splits each boundary into ordinary and crossover faces,
cancels the paired crossover faces, and reindexes the ordinary faces by the
diagonal face index.  The resulting components define a natural chain map
from alternating chains on the diagonal to the total alternating complex.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

private lemma horizontalTermCongr
    (n p q q' : ℕ) (hqq : q = q')
    (h : (p + 1) + q = n + 1) (h' : (p + 1) + q' = n + 1)
    (hLow : p + q = n) (hLow' : p + q' = n) :
    faceToBidegreeOfEq B (p + 1) q (n + 1) h ≫
        ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).d
          (p + 1) p).f q ≫ totalιOfEq B p q n hLow =
      faceToBidegreeOfEq B (p + 1) q' (n + 1) h' ≫
        ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).d
          (p + 1) p).f q' ≫ totalιOfEq B p q' n hLow' := by
  subst q'
  rfl

private lemma verticalTermCongr
    (n p qh ql qh' ql' : ℕ) (hh : qh = qh') (hl : ql = ql')
    (h : p + qh = n + 1) (h' : p + qh' = n + 1)
    (hLow : p + ql = n) (hLow' : p + ql' = n) :
    ((-1 : ℤ) ^ p) •
        (faceToBidegreeOfEq B p qh (n + 1) h ≫
          ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).d
            qh ql ≫ totalιOfEq B p ql n hLow) =
      ((-1 : ℤ) ^ p) •
        (faceToBidegreeOfEq B p qh' (n + 1) h' ≫
          ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).d
            qh' ql' ≫ totalιOfEq B p ql' n hLow') := by
  subst qh'
  subst ql'
  rfl

private lemma horizontalOuterNormalize (n : ℕ) :
    (∑ p : Fin (n + 2),
      let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
      let q := cutComplement (n + 1) p
      have h : p.val + q = n + 1 := cut_add (n + 1) p
      faceToBidegreeOfEq B p.val q (n + 1) h ≫
        (if hp : p.val = 0 then
          (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
        else
          (K.d p.val (p.val - 1)).f q ≫
            K.ιTotal (ComplexShape.down ℕ) (p.val - 1) q n (by
              change (p.val - 1) + q = n
              have := cut_add (n + 1) p
              omega))) =
    ∑ p : Fin (n + 1),
      let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
      let q := cutComplement n p
      faceToBidegreeOfEq B (p.val + 1) q (n + 1) (by
          have := cut_add n p
          omega) ≫
        (K.d (p.val + 1) p.val).f q ≫
          totalιOfEq B p.val q n (cut_add n p) := by
  let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
  let f := fun p : Fin (n + 2) =>
    let q := cutComplement (n + 1) p
    have h : p.val + q = n + 1 := cut_add (n + 1) p
    faceToBidegreeOfEq B p.val q (n + 1) h ≫
      (if hp : p.val = 0 then
        (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
      else
        (K.d p.val (p.val - 1)).f q ≫
          K.ιTotal (ComplexShape.down ℕ) (p.val - 1) q n (by
            change (p.val - 1) + q = n
            have := cut_add (n + 1) p
            omega))
  change (∑ p, f p) = _
  rw [Fin.sum_univ_succ]
  have hf0 : f 0 = 0 := by
    dsimp [f]
    simp only [CategoryTheory.Limits.comp_zero]
  rw [hf0, zero_add]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [f]
  apply horizontalTermCongr B n p.val
    (cutComplement (n + 1) (Fin.succ p)) (cutComplement n p)
  simp only [Fin.val_succ, cutComplement]
  omega

private lemma verticalOuterNormalize (n : ℕ) :
    (∑ p : Fin (n + 2),
      let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
      let q := cutComplement (n + 1) p
      have h : p.val + q = n + 1 := cut_add (n + 1) p
      faceToBidegreeOfEq B p.val q (n + 1) h ≫
        (if hq : q = 0 then
          (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
        else
          ((-1 : ℤ) ^ p.val) •
            ((K.X p.val).d q (q - 1) ≫
              K.ιTotal (ComplexShape.down ℕ) p.val (q - 1) n (by
                change p.val + (q - 1) = n
                have := cut_add (n + 1) p
                omega)))) =
    ∑ p : Fin (n + 1),
      let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
      let q := cutComplement n p
      ((-1 : ℤ) ^ p.val) •
        (faceToBidegreeOfEq B p.val (q + 1) (n + 1) (by
            have := cut_add n p
            omega) ≫
          (K.X p.val).d (q + 1) q ≫
            totalιOfEq B p.val q n (cut_add n p)) := by
  let K := AlgebraicTopology.bisimplicialAlternatingBicomplex A B
  let g := fun p : Fin (n + 2) =>
    let q := cutComplement (n + 1) p
    have h : p.val + q = n + 1 := cut_add (n + 1) p
    faceToBidegreeOfEq B p.val q (n + 1) h ≫
      (if hq : q = 0 then
        (0 : (K.X p.val).X q ⟶ K.total (ComplexShape.down ℕ) |>.X n)
      else
        ((-1 : ℤ) ^ p.val) •
          ((K.X p.val).d q (q - 1) ≫
            K.ιTotal (ComplexShape.down ℕ) p.val (q - 1) n (by
              change p.val + (q - 1) = n
              have := cut_add (n + 1) p
              omega)))
  change (∑ p, g p) = _
  rw [Fin.sum_univ_castSucc]
  have hglast : g (Fin.last (n + 1)) = 0 := by
    dsimp [g]
    simp [cutComplement]
  rw [hglast, add_zero]
  apply Finset.sum_congr rfl
  intro p _
  have hq : cutComplement (n + 1) (Fin.castSucc p) ≠ 0 := by
    simp only [cutComplement, Fin.val_castSucc]
    omega
  dsimp [g]
  rw [dite_eq_right hq, Preadditive.comp_zsmul]
  apply verticalTermCongr B n p.val
    (cutComplement (n + 1) (Fin.castSucc p))
    (cutComplement (n + 1) (Fin.castSucc p) - 1)
    (cutComplement n p + 1) (cutComplement n p)
  all_goals simp only [Fin.val_castSucc, cutComplement]
  all_goals omega

/-- The degreewise bisimplicial Alexander--Whitney components commute with
the alternating differential. -/
theorem component_comm (n : ℕ) :
    component B (n + 1) ≫
        (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).d
          (n + 1) n =
      (diagonalAlternatingComplex B).d (n + 1) n ≫ component B n := by
  rw [component_comp_total_d_eq_bidegree_sum,
    diagonal_d_comp_component_eq_double_sum]
  simp_rw [Preadditive.comp_add]
  rw [Finset.sum_add_distrib]
  rw [horizontalOuterNormalize B n, verticalOuterNormalize B n]
  simp_rw [horizontal_face_split, vertical_face_split]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [Preadditive.zsmul_comp, ← diagonal_δ]
  let HC := fun p : Fin (n + 1) =>
    let q := cutComplement n p
    ((-1 : ℤ) ^ (p.val + 1)) •
      (faceToBidegreeOfEq B (p.val + 1) q (n + 1) (by
          have := cut_add n p
          omega) ≫
        (B.δ (⟨p.val + 1, by omega⟩ : Fin (p.val + 2))).app
          (Opposite.op ⦋q⦌) ≫
        totalιOfEq B p.val q n (cut_add n p))
  let VC := fun p : Fin (n + 1) =>
    let q := cutComplement n p
    ((-1 : ℤ) ^ p.val) •
      (faceToBidegreeOfEq B p.val (q + 1) (n + 1) (by
          have := cut_add n p
          omega) ≫
        (B.obj (Opposite.op ⦋p.val⦌)).δ
          (⟨0, by omega⟩ : Fin (q + 2)) ≫
        totalιOfEq B p.val q n (cut_add n p))
  let H := fun (p : Fin (n + 1)) (j : Fin (p.val + 1)) =>
    horizontalOrdinaryTerm B n p j
  let V := fun (p : Fin (n + 1)) (k : Fin (cutComplement n p + 1)) =>
    verticalOrdinaryTerm B n p k
  let R := fun (p : Fin (n + 1)) (i : Fin (n + 2)) =>
    diagonalOrdinaryTerm B n p i
  change ((∑ p, ∑ j, H p j) + ∑ p, HC p) +
      ((∑ p, VC p) + ∑ p, ∑ k, V p k) = ∑ i, ∑ p, R p i
  have hOrd : (∑ p, ∑ j, H p j) + (∑ p, ∑ k, V p k) =
      ∑ i, ∑ p, R p i := by
    dsimp only [H, V, R]
    exact ordinaryTerms_eq_diagonalDoubleSum B n
  have hCross : (∑ p, HC p) + (∑ p, VC p) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    dsimp only [HC, VC]
    exact crossover_signed_cancel B p.val (cutComplement n p) n (cut_add n p)
  calc
    _ = ((∑ p, ∑ j, H p j) + (∑ p, ∑ k, V p k)) +
        ((∑ p, HC p) + (∑ p, VC p)) := by ac_rfl
    _ = (∑ i, ∑ p, R p i) + 0 := by rw [hOrd, hCross]
    _ = _ := add_zero _

/-- The Alexander--Whitney chain map from the diagonal alternating complex
of a bisimplicial object to its signed total alternating complex. -/
noncomputable def alternatingMap :
    diagonalAlternatingComplex B ⟶
      AlgebraicTopology.bisimplicialAlternatingTotalComplex A B where
  f := component B
  comm' := fun {i j} hij => by
    subst hij
    exact component_comm B j

@[simp]
theorem alternatingMap_f (n : ℕ) :
    (alternatingMap B).f n = component B n := rfl

/-- Naturality of the bisimplicial Alexander--Whitney chain map. -/
@[reassoc]
theorem alternatingMap_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B') :
    (AlgebraicTopology.alternatingFaceMapComplex A).map
          ((SimplicialObject.diagonalFunctor A).map f) ≫
        alternatingMap B' =
      alternatingMap B ≫
        (AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f := by
  ext n
  exact component_naturality f n

end AlgebraicTopology.BisimplicialAlexanderWhitney
