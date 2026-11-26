/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConstantTermLinearRepresentationStep

namespace MetaMathlibExt

-- At degree one the box can consist of just the origin, even for the largest digit.
example {r : ℕ} (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (hP : laurentDeg P ≤ 1) (n : ℕ) :
    (P ^ (3 * n + 2)).coeff 0 ≡ (P ^ 2).coeff 0 * (P ^ n).coeff 0 [ZMOD 3] := by
  have hbox : Fintype.piFinset (fun _ : Fin r => Finset.Icc (0 : ℤ) 0) = {0} := by
    simpa only [Finset.Icc_self, Pi.zero_apply] using Fintype.piFinset_singleton (0 : Fin r → ℤ)
  simpa only [Nat.cast_zero, neg_zero, hbox, Finset.sum_singleton, smul_zero, sub_zero,
    Nat.cast_ofNat] using coeff_pow_modEq_sum_gamma_mul_V Nat.prime_three P 0 hP 2 (by decide)
      n 0 (Fintype.mem_piFinset.mpr fun _ => by simp)

-- At the nonzero endpoint i = 1, the zero binary digit kills the coefficient at -1.
example (P : AddMonoidAlgebra ℤ (Fin 1 → ℤ)) (hP : laurentDeg P ≤ 2) (n : ℕ) :
    (P ^ (2 * n)).coeff (fun _ => -1) ≡ 0 [ZMOD 2] := by
  have h := coeff_pow_modEq_sum_gamma_mul_V Nat.prime_two P 1 hP 0 (by decide) n
    (fun _ => 1) (by decide)
  have hodd (j : Fin 1 → ℤ) : (0 : Fin 1 → ℤ) ≠ 2 • j - (fun _ => 1) := by
    intro he
    have he₀ := congrFun he 0
    change (0 : ℤ) = (2 : ℕ) • j 0 - 1 at he₀
    rw [two_nsmul] at he₀
    omega
  simpa only [Nat.add_zero, Pi.neg_def, pow_zero, AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hodd, ite_false, zero_mul,
    Finset.sum_const_zero, Nat.cast_ofNat] using h

end MetaMathlibExt
