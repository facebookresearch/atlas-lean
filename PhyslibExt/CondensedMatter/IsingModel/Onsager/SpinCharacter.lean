/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusSpinSectors

/-!

# Spin-structure characters of homology classes

The quadratic characters `(-1)^{q_{a,b}(h)}` on `H₁(T², ℤ/2)` and the even-subgraph sums they
weight.

## i. Overview

For boundary phases `a, b ∈ {0, 1}` the character
`ons_spinCharacter a b h = (-1)^{(1 + a) h₁ + (1 + b) h₂ + h₁ h₂}` is a quadratic form on `(ℤ/2)²`
refining the intersection form `h · k = h₁ k₂ + h₂ k₁`: it is multiplicative up to the sign
`(-1)^{h · k}`. These are the four spin structures of the torus. Weighting even subgraphs by the
character of their homology class gives the four signed sector sums `ons_spin11`, `ons_spin01`,
`ons_spin10`, `ons_spin00`.

## ii. Key results

- `ons_spinCharacter` : the spin-structure character
- `ons_homologyIntersection` : the intersection form mod 2
- `ons_spinCharacter_add` : the character is quadratic with respect to the intersection form
- `ons_spinCharacterSum` : the character-weighted even-subgraph sum
- `ons_spinCharacterSum_zero_zero` : the four character sums are the signed sector sums

## iii. Table of contents

- A. Characters and the intersection form
- B. Character-weighted even-subgraph sums

## iv. References

- N. P. Dolbilin, Yu. M. Zinov'ev, A. S. Mishchenko, M. A. Shtan'ko and M. I. Shtogrin, *Homological
  properties of two-dimensional coverings of lattices on surfaces*, Funct. Anal. Appl. 30 (1996)
  163-173
- D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators StatMech.Ising

/-! ## A. Characters and the intersection form -/

/-- The spin-structure character `(-1)^{(1 + a) h₁ + (1 + b) h₂ + h₁ h₂}` of a homology class `h`
mod 2, for boundary phases `a, b`. -/
def ons_spinCharacter (a b : Fin 2) (h : Fin 2 × Fin 2) : ℝ :=
  (-1 : ℝ) ^ ((1 + a.val) * h.1.val + (1 + b.val) * h.2.val +
    h.1.val * h.2.val)

/-- The intersection form `h₁ k₂ + h₂ k₁` on `H₁(T², ℤ/2) = (ℤ/2)²`. -/
def ons_homologyIntersection (h k : Fin 2 × Fin 2) : Fin 2 :=
  h.1 * k.2 + h.2 * k.1

lemma ons_homologyIntersection_add_right
    (h k l : Fin 2 × Fin 2) :
    ons_homologyIntersection h (k + l) =
      ons_homologyIntersection h k + ons_homologyIntersection h l := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  rcases l with ⟨l1, l2⟩
  fin_cases h1 <;> fin_cases h2 <;> fin_cases k1 <;> fin_cases k2 <;>
    fin_cases l1 <;> fin_cases l2 <;> decide

lemma ons_homologyIntersection_sum_right
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

lemma ons_spinCharacter_add (a b : Fin 2) (h k : Fin 2 × Fin 2) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k *
        (-1 : ℝ) ^ (ons_homologyIntersection h k).val := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    fin_cases k1 <;> fin_cases k2 <;>
    norm_num [ons_spinCharacter, ons_homologyIntersection, Fin.val_add]

lemma ons_spinCharacter_add_of_intersection_zero
    (a b : Fin 2) (h k : Fin 2 × Fin 2)
    (hzero : ons_homologyIntersection h k = 0) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k := by
  rw [ons_spinCharacter_add, hzero]
  norm_num

lemma ons_spinCharacter_sum_of_pairwise_intersection_zero
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

/-! ## B. Character-weighted even-subgraph sums -/

/-- The even-subgraph sum of the torus with each subgraph weighted by the spin character of its
homology class. -/
noncomputable def ons_spinCharacterSum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

lemma ons_spinCharacterSum_eq_sector_sum (L : ℕ) [Fact (2 < L)]
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

lemma ons_spinCharacterSum_zero_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 0 = ons_spin11 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin11, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

lemma ons_spinCharacterSum_one_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 0 = ons_spin01 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin01, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

lemma ons_spinCharacterSum_zero_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 1 = ons_spin10 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin10, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

lemma ons_spinCharacterSum_one_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 1 = ons_spin00 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin00, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

end StatMech.Onsager
