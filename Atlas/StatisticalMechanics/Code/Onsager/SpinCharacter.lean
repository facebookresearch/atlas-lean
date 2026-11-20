/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWPhaseLoops
import Code.Onsager.TorusSpinSectors









namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_spinCharacter (a b : Fin 2) (h : Fin 2 × Fin 2) : ℝ :=
  (-1 : ℝ) ^ ((1 + a.val) * h.1.val + (1 + b.val) * h.2.val +
    h.1.val * h.2.val)

def ons_homologyIntersection (h k : Fin 2 × Fin 2) : Fin 2 :=
  h.1 * k.2 + h.2 * k.1

theorem ons_homologyIntersection_add_right
    (h k l : Fin 2 × Fin 2) :
    ons_homologyIntersection h (k + l) =
      ons_homologyIntersection h k + ons_homologyIntersection h l := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  rcases l with ⟨l1, l2⟩
  fin_cases h1 <;> fin_cases h2 <;> fin_cases k1 <;> fin_cases k2 <;>
    fin_cases l1 <;> fin_cases l2 <;> decide

theorem ons_homologyIntersection_sum_right
    {iota : Type*} (h : Fin 2 × Fin 2) (S : Finset iota)
    (f : iota → Fin 2 × Fin 2) :
    ons_homologyIntersection h (∑ i ∈ S, f i) =
      ∑ i ∈ S, ons_homologyIntersection h (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_homologyIntersection]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ons_homologyIntersection_add_right, ih]

theorem ons_spinCharacter_add (a b : Fin 2) (h k : Fin 2 × Fin 2) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k *
        (-1 : ℝ) ^ (ons_homologyIntersection h k).val := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    fin_cases k1 <;> fin_cases k2 <;>
    norm_num [ons_spinCharacter, ons_homologyIntersection, Fin.val_add]

theorem ons_spinCharacter_add_of_intersection_zero
    (a b : Fin 2) (h k : Fin 2 × Fin 2)
    (hzero : ons_homologyIntersection h k = 0) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k := by
  rw [ons_spinCharacter_add, hzero]
  norm_num

theorem ons_spinCharacter_sum_of_pairwise_intersection_zero
    {iota : Type*} (a b : Fin 2) (S : Finset iota)
    (f : iota → Fin 2 × Fin 2)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ons_homologyIntersection (f i) (f j) = 0) :
    ons_spinCharacter a b (∑ i ∈ S, f i) =
      ∏ i ∈ S, ons_spinCharacter a b (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [ons_spinCharacter]
  | @insert i S hi ih =>
      have hpairS : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
          ons_homologyIntersection (f j) (f k) = 0 := by
        intro j hj k hk hjk
        exact hpair j (by simp [hj]) k (by simp [hk]) hjk
      have hinter : ons_homologyIntersection (f i) (∑ j ∈ S, f j) = 0 := by
        rw [ons_homologyIntersection_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact hpair i (by simp) j (by simp [hj]) (by
          intro hij
          subst j
          exact hi hj)
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        ons_spinCharacter_add_of_intersection_zero a b _ _ hinter,
        ih hpairS]

noncomputable def ons_spinCharacterSum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

theorem ons_spinCharacterSum_eq_sector_sum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) :
    ons_spinCharacterSum L x a b =
      ∑ h : Fin 2 × Fin 2,
        ons_spinCharacter a b h * ons_sectorWeight L x h := by
  unfold ons_spinCharacterSum ons_sectorWeight
  calc
    (∑ F ∈ evenSubgraphs (onsTorusGraph L),
        ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card) =
        ∑ h : Fin 2 × Fin 2,
          ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h,
            ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card :=
      (Finset.sum_fiberwise
        (evenSubgraphs (onsTorusGraph L)) (ons_evenHomology L)
        (fun F => ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2]

theorem ons_spinCharacterSum_zero_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 0 = ons_spin11 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin11, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_one_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 0 = ons_spin01 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin01, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_zero_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 1 = ons_spin10 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin10, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_one_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 1 = ons_spin00 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin00, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

end StatMech.Onsager
