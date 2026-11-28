/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.Algebra.Polynomial.KasselReutenauerLaurentCoefficients

/-! # Tests for Kassel–Reutenauer Laurent coefficients and Chebyshev partial sums -/

open LaurentPolynomial Polynomial

namespace MetaMathlibExt

-- The boundary case is equality of the two constant polynomials, independently of the iff.
example : kasselReutenauerPoly 1 = chebyshevCPartialSum 0 := rfl

-- At the smallest positive index, the two negative monomials have exponent zero.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 1)).coeff.sum (fun _ c => |c|) = 4 := by
  rw [show kasselReutenauerPoly 1 = chebyshevCPartialSum 0 from rfl,
    chebyshevCPartialSum_zero, map_one, mul_one]
  have hs : ((T 1 - 2 + T (-1)) : LaurentPolynomial ℤ).coeff.support ⊆ ({1, 0, -1} : Finset ℤ) := by
    intro i hi
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact Finsupp.mem_support_iff.mp hi (by
      simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_ofNat,
        Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2])
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  norm_num [Finset.sum_insert, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_ofNat, Finsupp.single_apply]

-- The second partial sum contributes four in absolute value, but the third polynomial gives eight.
example : kasselReutenauerPoly 3 ≠ chebyshevCPartialSum 2 := by
  intro h
  have hcount := kasselReutenauer_C_abs_coeff_sum 3 (by decide)
  have hcard : ((Nat.divisors 3).filter Odd).card = 2 := by decide
  rw [h, hcard] at hcount
  have hinv : (T (-1) * T 1 : LaurentPolynomial ℤ) = 1 := by rw [← T_add]; simp
  have hfactor : (T (-1) * (T 1 - 1) ^ 2 : LaurentPolynomial ℤ) = T 1 - 2 + T (-1) := by
    linear_combination (T 1 - 2) * hinv
  rw [← hfactor, ← chebyshevCPartialSum_laurent_identity] at hcount
  have hs : ((T 3 + T (-3) - T 2 - T (-2)) : LaurentPolynomial ℤ).coeff.support ⊆
      ({3, -3, 2, -2} : Finset ℤ) := by
    intro i hi
    by_contra hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    exact Finsupp.mem_support_iff.mp hi (by
      simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, Ne.symm hmem.1,
        Ne.symm hmem.2.1, Ne.symm hmem.2.2.1, Ne.symm hmem.2.2.2])
  norm_num at hcount
  change ((T 3 + T (-3) - T 2 - T (-2)) : LaurentPolynomial ℤ).coeff.sum
    (fun _ c => |c|) = 8 at hcount
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)] at hcount
  norm_num [Finset.sum_insert, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub] at hcount

-- Client: the nontrivial power `2 = 2^1` gives equality at the first partial sum.
example : kasselReutenauerPoly 2 = chebyshevCPartialSum 1 :=
  (kasselReutenauerPoly_eq_chebyshevCPartialSum_iff 2 (by decide)).2 ⟨1, by decide⟩

-- A power of two has only the trivial odd divisor despite its even divisors.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 8)).coeff.sum (fun _ c => |c|) = 4 := by
  rw [kasselReutenauer_C_abs_coeff_sum 8 (by decide)]
  decide

-- With several odd divisors, both signs of the Chebyshev endpoints occur.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 15)).coeff.sum (fun _ c => |c|) = 16 := by
  rw [kasselReutenauer_C_abs_coeff_sum 15 (by decide)]
  decide

end MetaMathlibExt
