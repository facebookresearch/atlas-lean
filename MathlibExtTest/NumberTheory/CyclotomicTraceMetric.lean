/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicTraceMetric
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the cyclotomic trace metric -/

open IsCyclotomicExtension MetaMathlibExt

variable {K : Type*} [Field K] [CharZero K]

-- The defining sum is empty at conductor one.
example [IsCyclotomicExtension {1} ℚ K] (x : K) : cyclotomicTraceNormSq 1 x = 0 := by
  simp [cyclotomicTraceNormSq]

-- At the smallest prime the lower bound is an equality for every rational coordinate.
example [IsCyclotomicExtension {2} ℚ K] (q : ℚ) :
    cyclotomicTraceNormSq 2 ((q : K) * zeta 2 ℚ K) = q ^ 2 := by
  have h := (cyclotomicTraceNormSq_eq_and_ge (K := K) Nat.prime_two (fun _ => q)).1
  have hζ := (zeta_spec 2 ℚ K).eq_neg_one_of_two_right
  have htrace : Algebra.trace ℚ K (q : K) = q := by
    change Algebra.trace ℚ K (algebraMap ℚ K q) = q
    rw [Algebra.trace_algebraMap, IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 2))]
    norm_num
  simp [hζ, htrace] at h ⊢
  rw [h]
  ring

-- Opposite coordinates at conductor three give a lower bound of two.
example [IsCyclotomicExtension {3} ℚ K] :
    2 ≤ cyclotomicTraceNormSq 3 (zeta 3 ℚ K - zeta 3 ℚ K ^ 2) := by
  have h := (cyclotomicTraceNormSq_eq_and_ge (K := K) Nat.prime_three ![1, -1]).2
  simpa [Fin.sum_univ_two, sub_eq_add_neg, show (1 : ℚ) + 1 = 2 by norm_num] using h

-- The radius-zero box has one lattice point, at distance zero from itself.
example {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} ℚ K] :
    cyclotomicDistMoment p K 0 2 = 0 := by
  simp [cyclotomicDistMoment, cyclotomicBox_zero]

-- At conductor three the nonidentity automorphism exchanges the two primitive roots.
example [IsCyclotomicExtension {3} ℚ K] :
    cyclotomicTraceDist 3 (zeta 3 ℚ K ^ 2) 1 = cyclotomicTraceDist 3 (zeta 3 ℚ K) 1 := by
  have h := (zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide)
  have hirr := Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 3)
  simpa only [fromZetaAut_spec, map_one] using
    cyclotomicTraceDist_algEquiv Nat.prime_three (fromZetaAut h hirr) (zeta 3 ℚ K) 1

-- Even at conductor two the trace distance separates distinct field elements.
example [IsCyclotomicExtension {2} ℚ K] (x y : K) : cyclotomicTraceDist 2 x y = 0 ↔ x = y :=
  ((cyclotomicTraceNorm_isNorm Nat.prime_two).1 (x - y)).trans sub_eq_zero

-- A negative rational scalar of absolute value one half halves the norm.
example [IsCyclotomicExtension {3} ℚ K] (x : K) :
    cyclotomicTraceNorm 3 ((-1 / 2 : ℚ) • x) = cyclotomicTraceNorm 3 x / 2 := by
  rw [(cyclotomicTraceNorm_isNorm Nat.prime_three).2.2]
  norm_num
  ring
