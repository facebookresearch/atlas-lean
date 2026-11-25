/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFruitDiophantine
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # Tests for the generalized fruit equation -/

namespace MetaMathlibExt.generalizedFruit_no_solution_two_dvd

open NumberField

private theorem rational_two_prime : (twoUnramifiedDegreeOnePrimes ℚ).Nonempty := by
  classical
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hp : p.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  let : p.IsPrime := hp.isPrime
  obtain ⟨P⟩ : Nonempty (p.primesOver (𝓞 ℚ)) := inferInstance
  let : Fintype (p.primesOver (𝓞 ℚ)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 ℚ)
  rw [RingOfIntegers.rank, Module.finrank_self] at hsum
  have hle : P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun Q ↦ Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ P)
  have hepos := P.1.ramificationIdx_pos ℤ
  have hfpos := P.1.inertiaDeg_pos ℤ
  have he : P.1.ramificationIdx ℤ = 1 :=
    Nat.le_antisymm ((Nat.le_mul_of_pos_right _ hfpos).trans hle) hepos
  have hf : P.1.inertiaDeg ℤ = 1 :=
    Nat.le_antisymm ((Nat.le_mul_of_pos_left _ hepos).trans hle) hfpos
  have htwo : (2 : 𝓞 ℚ) ∈ P.1 := by
    simpa using (P.1.mem_of_liesOver p (2 : ℤ)).mp (Ideal.mem_span_singleton_self _)
  exact ⟨P.1, (mem_twoUnramifiedDegreeOnePrimes _).mpr ⟨inferInstance, htwo, he, hf⟩⟩

-- The smallest allowed odd exponents and the even nonzero coordinate x = 2.
example (y z : 𝓞 ℚ) :
    1 * (2 : 𝓞 ℚ) ^ 3 - y ^ 2 - z ^ 2 + 2 * y * z - (2 ^ 3 * 1 - 3 ^ 3) ≠ 0 :=
  generalizedFruit_no_solution_two_dvd ℚ rational_two_prime 1 1 one_ne_zero one_ne_zero
    3 3 (by decide) (by decide) (by decide) (by decide) 2 y z (dvd_refl _)

-- With the even exponent r = 2 the documented counterexample does solve the equation.
example :
    1 * (2 : 𝓞 ℚ) ^ 3 - 3 ^ 2 - 0 ^ 2 + 2 * 3 * 0 - (2 ^ 3 * 1 - 3 ^ 2) = 0 := by
  norm_num

end MetaMathlibExt.generalizedFruit_no_solution_two_dvd
