/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingSquareTorusAdapter










open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager StatMech.Ising

theorem anisotropicSquare_weightedSpin_norm_le_evenSubgraphSum
    (L : Nat) [Fact (2 < L)] {x y : Real} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (a b : Fin 2) :
    ‖ons_weightedSpinCharacterSum L
      (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) a b‖ ≤
      inhomogeneousEvenSubgraphSum (onsTorusGraph L)
        (fun edge => if squareTorusHorizontalEdge L edge then x else y) := by
  classical
  unfold ons_weightedSpinCharacterSum inhomogeneousEvenSubgraphSum
  calc
    ‖∑ F ∈ evenSubgraphs (onsTorusGraph L),
        (ons_spinCharacter a b (ons_evenHomology L F) : Complex) *
          ∏ edge ∈ F,
            anisotropicSquareEdgeWeight L (x : Complex) (y : Complex) edge‖ ≤
      ∑ F ∈ evenSubgraphs (onsTorusGraph L),
        ‖(ons_spinCharacter a b (ons_evenHomology L F) : Complex) *
          ∏ edge ∈ F,
            anisotropicSquareEdgeWeight L (x : Complex) (y : Complex) edge‖ :=
        norm_sum_le _ _
    _ = ∑ F ∈ evenSubgraphs (onsTorusGraph L),
        ∏ edge ∈ F,
          (if squareTorusHorizontalEdge L edge then x else y) := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [norm_mul, norm_prod]
      have hchar :
          ‖(ons_spinCharacter a b (ons_evenHomology L F) : Complex)‖ = 1 := by
        simp [ons_spinCharacter]
      rw [hchar, one_mul]
      apply Finset.prod_congr rfl
      intro edge hedge
      unfold anisotropicSquareEdgeWeight
      split <;> simp_all [abs_of_nonneg]

theorem inhomogeneousEvenSubgraphSum_anisotropic_nonneg
    (L : Nat) [Fact (2 < L)] {x y : Real} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ inhomogeneousEvenSubgraphSum (onsTorusGraph L)
      (fun edge => if squareTorusHorizontalEdge L edge then x else y) := by
  classical
  unfold inhomogeneousEvenSubgraphSum
  positivity

theorem two_mul_evenSubgraphSum_le_sum_sector_norms
    (L : Nat) [Fact (2 < L)] {x y : Real} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * inhomogeneousEvenSubgraphSum (onsTorusGraph L)
        (fun edge => if squareTorusHorizontalEdge L edge then x else y) ≤
      ‖ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 1‖ +
      ‖ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 1‖ +
      ‖ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 0‖ +
      ‖ons_weightedSpinCharacterSum L
        (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 0‖ := by
  let E := inhomogeneousEvenSubgraphSum (onsTorusGraph L)
    (fun edge => if squareTorusHorizontalEdge L edge then x else y)
  have hE : 0 ≤ E := inhomogeneousEvenSubgraphSum_anisotropic_nonneg L hx hy
  have harf := two_mul_inhomogeneousEvenSubgraphSum_eq_spin L
    (fun edge => if squareTorusHorizontalEdge L edge then x else y)
  have hsector (a b : Fin 2) :
      ons_weightedSpinCharacterSum L
          (fun edge =>
            ((if squareTorusHorizontalEdge L edge then x else y) : Complex)) a b =
        ons_weightedSpinCharacterSum L
          (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) a b := by
    rfl
  simp only [apply_ite] at harf
  rw [hsector 1 1, hsector 0 1, hsector 1 0, hsector 0 0] at harf
  change (2 : Complex) * (E : Complex) = _ at harf
  have hnorm := congrArg norm harf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hnorm
  norm_num at hnorm
  change 2 * E ≤ _
  rw [hnorm]
  let S11 := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 1
  let S01 := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 1
  let S10 := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 0
  let S00 := ons_weightedSpinCharacterSum L
    (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 0
  change ‖S11 + S01 + S10 - S00‖ ≤
    ‖S11‖ + ‖S01‖ + ‖S10‖ + ‖S00‖
  calc
    ‖S11 + S01 + S10 - S00‖ ≤ ‖S11 + S01 + S10‖ + ‖S00‖ :=
      norm_sub_le _ _
    _ ≤ (‖S11 + S01‖ + ‖S10‖) + ‖S00‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖S11‖ + ‖S01‖) + ‖S10‖) + ‖S00‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

end StatMech.FrontierA
