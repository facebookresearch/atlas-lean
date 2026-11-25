/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30

open MathlibExt.GroupTheory.KourovkaNotebookShared
open MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

-- Level `1` imposes no condition.
example : congruenceSubgroup (Fin 3) 1 = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_congruenceSubgroup_iff.mpr fun _ _ => one_dvd _

-- Level `0` gives the trivial subgroup.
example : congruenceSubgroup (Fin 2) 0 = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  rw [mem_congruenceSubgroup_iff] at hg
  exact Units.ext (Matrix.ext fun i j =>
    sub_eq_zero.mp (zero_dvd_iff.mp (by exact_mod_cast hg i j)))

-- The scalar `-1` has order 2 and lies in the level-2 congruence subgroup but not in level 3, so
-- the level 6 of the witness excludes it.
example : (-1 : GL (Fin 2) ℤ) ∈ congruenceSubgroup (Fin 2) 2 ∧
    (-1 : GL (Fin 2) ℤ) ∉ congruenceSubgroup (Fin 2) 3 := by
  simp only [mem_congruenceSubgroup_iff, Units.val_neg, Units.val_one, Matrix.neg_apply]
  refine ⟨fun i j => ?_, fun h => absurd (h 0 0) (by decide)⟩
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

-- Residual `p`-ness for a prime dividing the level, in another dimension.
example : IsResiduallyFiniteP 5 (congruenceSubgroup (Fin 2) 10) :=
  isResiduallyFiniteP_congruenceSubgroup Nat.prime_five (by norm_num)

-- `GL₃(ℤ)` itself, the level-`1` congruence subgroup, is not right-orderable.
example : ¬ IsRightOrderable (congruenceSubgroup (Fin 3) 1) :=
  not_isRightOrderable_congruenceSubgroup one_ne_zero

-- Level `6` is residually a finite `2`-group and a finite `3`-group, but not right-orderable.
example : IsResiduallyFiniteP 2 (congruenceSubgroup (Fin 3) 6) ∧
    IsResiduallyFiniteP 3 (congruenceSubgroup (Fin 3) 6) ∧
    ¬ IsRightOrderable (congruenceSubgroup (Fin 3) 6) :=
  ⟨isResiduallyFiniteP_congruenceSubgroup Nat.prime_two (by norm_num),
    isResiduallyFiniteP_congruenceSubgroup Nat.prime_three (by norm_num),
    not_isRightOrderable_congruenceSubgroup (by norm_num)⟩

-- Medvedev's question has a positive answer: being residually a finite `p`-group for two distinct
-- primes does not force right-orderability.
example : ¬ ∀ (G : Type) [Group G] (p q : ℕ), p.Prime → q.Prime → p ≠ q →
    IsResiduallyFiniteP p G → IsResiduallyFiniteP q G → IsRightOrderable G := by
  intro h
  obtain ⟨G, _, p, q, hp, hq, hpq, hpG, hqG, hG⟩ := residuallyTwoPrimesNotRightOrderable_holds
  exact hG (h G p q hp hq hpq hpG hqG)
