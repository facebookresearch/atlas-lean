/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWDetLimit
import Code.Onsager.SpinAssembly
import Code.Onsager.TorusSpinSectors

namespace StatMech.Onsager

open StatMech.Ising Polynomial

noncomputable def ons_sectorPoly (L : ℕ) [Fact (2 < L)]
    (h : Fin 2 × Fin 2) : Polynomial ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h,
    X ^ F.card

noncomputable def ons_spinPoly00 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) + ons_sectorPoly L (1, 0) +
    ons_sectorPoly L (0, 1) - ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly10 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) - ons_sectorPoly L (1, 0) +
    ons_sectorPoly L (0, 1) + ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly01 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) + ons_sectorPoly L (1, 0) -
    ons_sectorPoly L (0, 1) + ons_sectorPoly L (1, 1)

noncomputable def ons_spinPoly11 (L : ℕ) [Fact (2 < L)] : Polynomial ℝ :=
  ons_sectorPoly L (0, 0) - ons_sectorPoly L (1, 0) -
    ons_sectorPoly L (0, 1) - ons_sectorPoly L (1, 1)

theorem eval_ons_sectorPoly (L : ℕ) [Fact (2 < L)] (x : ℝ) (h : Fin 2 × Fin 2) :
    eval x (ons_sectorPoly L h) = ons_sectorWeight L x h := by
  unfold ons_sectorPoly ons_sectorWeight
  simp_rw [Polynomial.eval_finset_sum, eval_pow, eval_X]

theorem eval_ons_spinPoly00 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly00 L) = ons_spin00 L x := by
  simp [ons_spinPoly00, ons_spin00, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly10 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly10 L) = ons_spin10 L x := by
  simp [ons_spinPoly10, ons_spin10, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly01 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly01 L) = ons_spin01 L x := by
  simp [ons_spinPoly01, ons_spin01, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]

theorem eval_ons_spinPoly11 (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    eval x (ons_spinPoly11 L) = ons_spin11 L x := by
  simp [ons_spinPoly11, ons_spin11, ons_sector00, ons_sector10, ons_sector01,
    ons_sector11, eval_ons_sectorPoly]


noncomputable def ons_spinDetX (L : ℕ) (x : ℝ) (a b : Fin 2) : ℝ :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    ((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
      (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)))

theorem ons_spinDet_eq_spinDetX (L : ℕ) (beta : ℝ) (a b : Fin 2) :
    ons_spinDet L beta a b = ons_spinDetX L (Real.tanh beta) a b := by
  unfold ons_spinDet ons_spinDetX ons_symbolDispersion
  rfl

noncomputable def ons_spinDetPoly (L : ℕ) (a b : Fin 2) : Polynomial ℝ :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    ((1 + X ^ 2) ^ 2 -
      C (2 * (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L))) * X * (1 - X ^ 2))

theorem eval_ons_spinDetPoly (L : ℕ) (x : ℝ) (a b : Fin 2) :
    eval x (ons_spinDetPoly L a b) = ons_spinDetX L x a b := by
  unfold ons_spinDetPoly ons_spinDetX
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp
  ring

def ons_spinKacWardAt (L : ℕ) [Fact (2 < L)] (x : ℝ) : Prop :=
  ons_spin11 L x ^ 2 = ons_spinDetX L x 0 0 ∧
  ons_spin01 L x ^ 2 = ons_spinDetX L x 1 0 ∧
  ons_spin10 L x ^ 2 = ons_spinDetX L x 0 1 ∧
  ons_spin00 L x ^ 2 = ons_spinDetX L x 1 1




theorem ons_spinKacWardAt_all_of_small (L : ℕ) [Fact (2 < L)]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : ∀ x ∈ Set.Ioo (0 : ℝ) epsilon, ons_spinKacWardAt L x) :
    ∀ x : ℝ, ons_spinKacWardAt L x := by
  have hinter : (Set.Ioo (0 : ℝ) epsilon).Infinite :=
    Set.Ioo_infinite hepsilon
  have h11poly : ons_spinPoly11 L ^ 2 = ons_spinDetPoly L 0 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly11,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).1
  have h01poly : ons_spinPoly01 L ^ 2 = ons_spinDetPoly L 1 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly01,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.1
  have h10poly : ons_spinPoly10 L ^ 2 = ons_spinDetPoly L 0 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly10,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.2.1
  have h00poly : ons_spinPoly00 L ^ 2 = ons_spinDetPoly L 1 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly00,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.2.2
  intro x
  unfold ons_spinKacWardAt
  constructor
  · simpa [← eval_ons_spinPoly11, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h11poly
  constructor
  · simpa [← eval_ons_spinPoly01, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h01poly
  constructor
  · simpa [← eval_ons_spinPoly10, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h10poly
  · simpa [← eval_ons_spinPoly00, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h00poly

theorem ons_spinKacWardIdentities_of_small
    (epsilon : ℕ → ℝ) (hepsilon : ∀ L, 0 < epsilon L)
    (hsmall : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ∀ x ∈ Set.Ioo (0 : ℝ) (epsilon L), ons_spinKacWardAt L x)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  have hall := ons_spinKacWardAt_all_of_small L (hepsilon L)
    (hsmall L hL) (Real.tanh beta)
  unfold ons_spinKacWardAt at hall
  simpa [ons_spinDet_eq_spinDetX] using hall

end StatMech.Onsager
