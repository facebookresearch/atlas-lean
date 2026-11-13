/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusFourier
import Code.FrontierA.AnisotropicSquareTorusKacWard





open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager



def triangularTorusAdj (L : Nat)
    (u v : ZMod L × ZMod L) : Prop :=
  onsTorusAdj L u v ∨
    ((u.1 = v.1 + 1 ∧ u.2 = v.2 + 1) ∨
      (u.1 = v.1 - 1 ∧ u.2 = v.2 - 1))

instance (L : Nat) : DecidableRel (triangularTorusAdj L) := by
  intro u v
  unfold triangularTorusAdj
  infer_instance


def triangularTorusGraph (L : Nat) [Fact (2 < L)] :
    SimpleGraph (ZMod L × ZMod L) where
  Adj := triangularTorusAdj L
  symm := by
    rintro u v (hsquare | hdiag)
    · apply Or.inl
      exact ((onsTorusGraph L).adj_comm u v).mp hsquare
    · rcases hdiag with hdiag | hdiag
      · exact Or.inr (Or.inr <| by
          constructor
          · linear_combination -hdiag.1
          · linear_combination -hdiag.2)
      · exact Or.inr (Or.inl <| by
          constructor
          · linear_combination -hdiag.1
          · linear_combination -hdiag.2)
  loopless := by
    have hne : (1 : ZMod L) ≠ 0 := by
      letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
      exact one_ne_zero
    refine ⟨?_⟩
    intro v hv
    rcases hv with hsquare | hdiag
    · exact (onsTorusGraph L).loopless.irrefl v hsquare
    · rcases hdiag with hdiag | hdiag
      · exact hne (by linear_combination -hdiag.1)
      · exact hne (by linear_combination hdiag.1)

instance (L : Nat) [Fact (2 < L)] :
    DecidableRel (triangularTorusGraph L).Adj :=
  inferInstanceAs (DecidableRel (triangularTorusAdj L))



def triangularTorusXSeamEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ons_xSeamEdge L edge ∨
    ∃ y : ZMod L, edge = s(((0 : ZMod L), y), (-1, y - 1))



def triangularTorusYSeamEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ons_ySeamEdge L edge ∨
    ∃ x : ZMod L, edge = s((x, (0 : ZMod L)), (x - 1, -1))

noncomputable instance triangularTorusXSeamEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusXSeamEdge L edge) := Classical.dec _

noncomputable instance triangularTorusYSeamEdge_decidable
    (L : Nat) (edge : Sym2 (ZMod L × ZMod L)) :
    Decidable (triangularTorusYSeamEdge L edge) := Classical.dec _

@[simp] theorem triangularTorusXSeamEdge_diagonal
    (L : Nat) (y : ZMod L) :
    triangularTorusXSeamEdge L
      s(((0 : ZMod L), y), (-1, y - 1)) :=
  Or.inr ⟨y, rfl⟩

@[simp] theorem triangularTorusYSeamEdge_diagonal
    (L : Nat) (x : ZMod L) :
    triangularTorusYSeamEdge L
      s((x, (0 : ZMod L)), (x - 1, -1)) :=
  Or.inr ⟨x, rfl⟩



noncomputable def triangularTorusEvenHomology (L : Nat)
    (F : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 × Fin 2 :=
  by
    classical
    exact
      (⟨(F.filter (triangularTorusXSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩,
       ⟨(F.filter (triangularTorusYSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩)



noncomputable def triangularTorusWeightedSpinCharacterSum
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) : Complex :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    (ons_spinCharacter a b (triangularTorusEvenHomology L F) : Complex) *
      ∏ edge ∈ F, weight edge

private theorem triangularTorus_spinCharacter_arf_sum
    (h : Fin 2 × Fin 2) :
    (2 : Complex) =
      ons_spinCharacter 1 1 h + ons_spinCharacter 0 1 h +
        ons_spinCharacter 1 0 h - ons_spinCharacter 0 0 h := by
  rcases h with ⟨h1, h2⟩
  fin_cases h1 <;> fin_cases h2 <;> norm_num [ons_spinCharacter]



theorem two_mul_triangularTorusEvenSubgraphSum_eq_spin
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real) :
    (2 : Complex) *
        inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight =
      triangularTorusWeightedSpinCharacterSum L
          (fun edge => (weight edge : Complex)) 1 1 +
        triangularTorusWeightedSpinCharacterSum L
          (fun edge => (weight edge : Complex)) 0 1 +
        triangularTorusWeightedSpinCharacterSum L
          (fun edge => (weight edge : Complex)) 1 0 -
        triangularTorusWeightedSpinCharacterSum L
          (fun edge => (weight edge : Complex)) 0 0 := by
  classical
  unfold inhomogeneousEvenSubgraphSum
    triangularTorusWeightedSpinCharacterSum
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  rw [triangularTorus_spinCharacter_arf_sum
    (triangularTorusEvenHomology L F)]
  ring



theorem triangularTorusIsingPartition_highTemperature
    (L : Nat) [Fact (2 < L)]
    (coupling : Sym2 (ZMod L × ZMod L) → Real) :
    StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset coupling
        (fun _ => 0) =
      (2 : Real) ^ Fintype.card (ZMod L × ZMod L) *
        (∏ edge ∈ (triangularTorusGraph L).edgeFinset,
          Real.cosh (coupling edge)) *
        inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
          (fun edge => Real.tanh (coupling edge)) :=
  inhomogeneousIsingPartition_highTemperature
    (triangularTorusGraph L) coupling



theorem triangularTorusWeightedSpin_norm_le_evenSubgraphSum
    (L : Nat) [Fact (2 < L)]
    {weight : Sym2 (ZMod L × ZMod L) → Real}
    (hweight : ∀ edge, 0 ≤ weight edge) (a b : Fin 2) :
    ‖triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b‖ ≤
      inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight := by
  classical
  unfold triangularTorusWeightedSpinCharacterSum
    inhomogeneousEvenSubgraphSum
  calc
    ‖∑ F ∈ evenSubgraphs (triangularTorusGraph L),
        (ons_spinCharacter a b (triangularTorusEvenHomology L F) : Complex) *
          ∏ edge ∈ F, (weight edge : Complex)‖ ≤
      ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
        ‖(ons_spinCharacter a b (triangularTorusEvenHomology L F) : Complex) *
          ∏ edge ∈ F, (weight edge : Complex)‖ := norm_sum_le _ _
    _ = ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
        ∏ edge ∈ F, weight edge := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [norm_mul, norm_prod]
      have hchar :
          ‖(ons_spinCharacter a b
            (triangularTorusEvenHomology L F) : Complex)‖ = 1 := by
        simp [ons_spinCharacter]
      rw [hchar, one_mul]
      apply Finset.prod_congr rfl
      intro edge hedge
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight edge)]

theorem triangularTorusEvenSubgraphSum_nonneg
    (L : Nat) [Fact (2 < L)]
    {weight : Sym2 (ZMod L × ZMod L) → Real}
    (hweight : ∀ edge, 0 ≤ weight edge) :
    0 ≤ inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight := by
  classical
  unfold inhomogeneousEvenSubgraphSum
  apply Finset.sum_nonneg
  intro F hF
  apply Finset.prod_nonneg
  intro edge hedge
  exact hweight edge



theorem two_mul_triangularTorusEvenSubgraphSum_le_sum_sector_norms
    (L : Nat) [Fact (2 < L)]
    {weight : Sym2 (ZMod L × ZMod L) → Real}
    (hweight : ∀ edge, 0 ≤ weight edge) :
    2 * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight ≤
      ‖triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) 1 1‖ +
      ‖triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) 0 1‖ +
      ‖triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) 1 0‖ +
      ‖triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) 0 0‖ := by
  let E := inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight
  have hE : 0 ≤ E := triangularTorusEvenSubgraphSum_nonneg L hweight
  have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight
  change (2 : Complex) * (E : Complex) = _ at harf
  have hnorm := congrArg norm harf
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hnorm
  norm_num at hnorm
  change 2 * E ≤ _
  rw [hnorm]
  let S11 := triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight edge : Complex)) 1 1
  let S01 := triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight edge : Complex)) 0 1
  let S10 := triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight edge : Complex)) 1 0
  let S00 := triangularTorusWeightedSpinCharacterSum L
    (fun edge => (weight edge : Complex)) 0 0
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
