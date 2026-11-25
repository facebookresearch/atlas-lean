/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryResidual
public import Mathlib.Algebra.Homology.Homotopy

/-!
# The natural bisimplicial Shih homotopy

The residual positive-face identity is assembled into the all-degree boundary
of the explicit Shih operator.  This packages a natural chain homotopy from
the Alexander--Whitney--shuffle composite to the identity on diagonal
alternating chains.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

open AlgebraicTopology.EilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- A positive-face identity computes the complete Shih boundary. -/
theorem shihBoundary_sum_eq_awShuffle_sub_id_of_positiveFaces
    (n : ℕ) (h : ShihPositiveFaceIdentity B n) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 3), shihUpperBoundaryTerm B (n + 1) i k) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 2), shihLowerBoundaryTerm B n k i =
      awShuffleDiagonalComponent B (n + 1) -
        𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
          (n + 1)) := by
  rw [shihBoundary_sum_reduction,
    sum_gapOneBaseSummand_eq_awShuffle_sub_zero]
  rw [show
    awShuffleDiagonalComponent B (n + 1) -
          awShuffleZeroComponent B (n + 1) +
        (∑ i : ShihIndex (n + 1),
          ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
        ∑ i : ShihIndex n,
          ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i =
      awShuffleDiagonalComponent B (n + 1) -
          awShuffleZeroComponent B (n + 1) +
        ((∑ i : ShihIndex (n + 1),
          ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
        ∑ i : ShihIndex n,
          ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i) by abel,
    h]
  abel

/-- Degree-raising operators on diagonal alternating chains. -/
def AlternatingShihOperator : Type _ :=
  ∀ i j : ℕ, (ComplexShape.down ℕ).Rel j i →
    ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X i ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X j)

/-- The operator represented by the explicit bisimplicial Shih formula. -/
noncomputable def explicitAlternatingShihOperator : AlternatingShihOperator B :=
  fun i j hij => by
    rw [ComplexShape.down_Rel] at hij
    subst j
    exact shihComponent B i

@[simp]
theorem explicitAlternatingShihOperator_apply
    (n : ℕ) (h : (ComplexShape.down ℕ).Rel (n + 1) n) :
    explicitAlternatingShihOperator B n (n + 1) h = shihComponent B n := by
  rfl

/-- Naturality of the explicit Shih operator. -/
theorem explicitAlternatingShihOperator_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
    explicitAlternatingShihOperator B i j hij ≫
        ((AlgebraicTopology.alternatingFaceMapComplex A).map
          ((SimplicialObject.diagonalFunctor A).map f)).f j =
      ((AlgebraicTopology.alternatingFaceMapComplex A).map
        ((SimplicialObject.diagonalFunctor A).map f)).f i ≫
        explicitAlternatingShihOperator B' i j hij := by
  rw [ComplexShape.down_Rel] at hij
  subst j
  simp only [explicitAlternatingShihOperator_apply,
    AlgebraicTopology.alternatingFaceMapComplex_map_f,
    SimplicialObject.diagonalFunctor_map_app]
  exact shihComponent_naturality f i

set_option backward.isDefEq.respectTransparency false in
/-- The positive-degree null-homotopic-map component is the two boundary sums. -/
theorem explicitNullHomotopicMap_f_succ (n : ℕ) :
    (Homotopy.nullHomotopicMap' (explicitAlternatingShihOperator B)).f (n + 1) =
      (∑ i : ShihIndex (n + 1),
          ∑ k : Fin (n + 3), shihUpperBoundaryTerm B (n + 1) i k) +
        ∑ i : ShihIndex n,
          ∑ k : Fin (n + 2), shihLowerBoundaryTerm B n k i := by
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)
    (show (ComplexShape.down ℕ).Rel (n + 1) n by simp)]
  simp only [explicitAlternatingShihOperator_apply,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  rw [shihComponent_comp_d, d_comp_shihComponent]
  simp only [Fintype.sum_prod_type]
  rw [show
    (∑ x : Fin (n + 3), ∑ y : ShihIndex (n + 1),
        shihUpperBoundaryTerm B (n + 1) y x) =
      ∑ y : ShihIndex (n + 1), ∑ x : Fin (n + 3),
        shihUpperBoundaryTerm B (n + 1) y x by
      exact Finset.sum_comm]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem explicitNullHomotopicMap_f_succ_eq_diagonal_sub_id
    (n : ℕ) (h : ShihPositiveFaceIdentity B n) :
    (Homotopy.nullHomotopicMap' (explicitAlternatingShihOperator B)).f (n + 1) =
      awShuffleDiagonalComponent B (n + 1) -
        𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
          (n + 1)) := by
  rw [explicitNullHomotopicMap_f_succ]
  exact shihBoundary_sum_eq_awShuffle_sub_id_of_positiveFaces B n h

/-- The degree-zero Shih boundary component is zero. -/
theorem explicitNullHomotopicMap_f_zero :
    (Homotopy.nullHomotopicMap' (explicitAlternatingShihOperator B)).f 0 = 0 := by
  change (Homotopy.nullHomotopicMap'
    (fun i j hij => explicitAlternatingShihOperator B i j hij)).f 0 = 0
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
    (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
  · rw [explicitAlternatingShihOperator_apply]
    rw [show shihComponent B 0 = 0 by
        unfold shihComponent
        exact Finset.sum_eq_zero fun i _ => Fin.elim0 i.p]
    change (0 :
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X 0 ⟶
        (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X 1) ≫
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).d 1 0 = 0
    simp only [CategoryTheory.Limits.zero_comp]
  · intro l hl
    simp at hl

/-- In degree zero the AW--shuffle component is the identity. -/
theorem awShuffleDiagonalComponent_zero :
    awShuffleDiagonalComponent B 0 =
      𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X 0) := by
  let _ : Unique (Shuffle 0 0) :=
    { default := Shuffle.leftUnitShuffle 0
      uniq := fun s => Shuffle.eq_leftUnitShuffle s }
  unfold awShuffleDiagonalComponent
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero]
  rw [Fintype.sum_unique]
  rw [Shuffle.eq_leftUnitShuffle (q := 0) (default : Shuffle 0 0)]
  simp [awShuffleDiagonalSummand,
    AlgebraicTopology.EilenbergZilber.awShuffleLeftHom,
    AlgebraicTopology.EilenbergZilber.awShuffleRightHom,
    AlgebraicTopology.AlexanderWhitney.frontInclusion_zero_right,
    AlgebraicTopology.AlexanderWhitney.backInclusion, SimplexCategory.δ₀Iter_zero,
    AlgebraicTopology.Bisimplicial.map]

theorem explicitNullHomotopicMap_f_zero_eq_diagonal_sub_id :
    (Homotopy.nullHomotopicMap' (explicitAlternatingShihOperator B)).f 0 =
      awShuffleDiagonalComponent B 0 -
        𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X 0) := by
  rw [explicitNullHomotopicMap_f_zero, awShuffleDiagonalComponent_zero,
    sub_self]

section Total

variable [Limits.HasCountableCoproducts A]

/-- The explicit Shih operator has boundary AW--shuffle minus identity. -/
theorem explicitAlternatingShihOperator_boundary :
    AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B ≫
          alternatingMap B -
        𝟙 (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B) =
      Homotopy.nullHomotopicMap' (explicitAlternatingShihOperator B) := by
  ext n
  cases n with
  | zero =>
      rw [HomologicalComplex.sub_f_apply,
        alternatingMap_comp_f_eq_awShuffleDiagonalComponent,
        HomologicalComplex.id_f]
      exact (explicitNullHomotopicMap_f_zero_eq_diagonal_sub_id B).symm
  | succ n =>
      rw [HomologicalComplex.sub_f_apply,
        alternatingMap_comp_f_eq_awShuffleDiagonalComponent,
        HomologicalComplex.id_f]
      exact (explicitNullHomotopicMap_f_succ_eq_diagonal_sub_id B n
        (shihPositiveFaceIdentity B n)).symm

/-- A chain homotopy from the Alexander--Whitney--shuffle composite to the
identity on diagonal alternating chains. -/
def AlternatingAlexanderWhitneyShuffleHomotopy : Type _ :=
  Homotopy
    (AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B ≫
      alternatingMap B)
    (𝟙 (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B))

/-- The natural explicit Shih homotopy on diagonal alternating chains. -/
noncomputable def homotopy :
    AlternatingAlexanderWhitneyShuffleHomotopy B :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (explicitAlternatingShihOperator_boundary B)).trans
      (Homotopy.nullHomotopy' (explicitAlternatingShihOperator B)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homotopy_hom (i j : ℕ) :
    (homotopy B).hom i j =
      if hij : (ComplexShape.down ℕ).Rel j i then
        explicitAlternatingShihOperator B i j hij else 0 := by
  simp [homotopy, Homotopy.equivSubZero, Homotopy.nullHomotopy']

/-- Naturality of every component of the Shih homotopy. -/
theorem homotopy_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (i j : ℕ) :
    (homotopy B).hom i j ≫
        ((AlgebraicTopology.alternatingFaceMapComplex A).map
          ((SimplicialObject.diagonalFunctor A).map f)).f j =
      ((AlgebraicTopology.alternatingFaceMapComplex A).map
        ((SimplicialObject.diagonalFunctor A).map f)).f i ≫
        (homotopy B').hom i j := by
  by_cases hij : (ComplexShape.down ℕ).Rel j i
  · simp only [homotopy_hom, dite_eq_left hij]
    exact explicitAlternatingShihOperator_naturality f i j hij
  · simp only [homotopy_hom, dite_eq_right hij,
      CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

end Total

end AlgebraicTopology.BisimplicialEilenbergZilber
