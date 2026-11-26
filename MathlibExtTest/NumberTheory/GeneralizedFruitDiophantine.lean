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

namespace MetaMathlibExt.ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow

open NumberField

-- The first quotient is the residue field, while 4 survives in the quotient by the cube.
example : ∃ P ∈ twoUnramifiedDegreeOnePrimes ℚ,
    Nonempty ((𝓞 ℚ ⧸ P) ≃+* ZMod 2) ∧ (4 : 𝓞 ℚ ⧸ P ^ 3) ≠ 0 := by
  obtain ⟨P, hP⟩ := generalizedFruit_no_solution_two_dvd.rational_two_prime
  refine ⟨P, hP, ?_, ?_⟩
  · obtain ⟨e⟩ := ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow ℚ P hP 1 (by decide)
    exact ⟨(Ideal.quotEquivOfEq (pow_one P).symm).trans e⟩
  · obtain ⟨e⟩ := ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow ℚ P hP 3 (by decide)
    intro h
    have : (4 : ZMod 8) = 0 := by simpa only [map_ofNat, map_zero] using congrArg e h
    exact (by decide : (4 : ZMod 8) ≠ 0) this

end MetaMathlibExt.ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow

namespace MetaMathlibExt

-- An even parameter and a nonintegral x-coordinate with even numerator.
example (y : ℚ) : ¬ (fruitWeierstrassCurve (0 : ℚ)).toAffine.Equation (2 / 3) y :=
  fruitWeierstrassCurve_rat_not_equation_of_two_dvd_num 0 (2 / 3) y (by decide +kernel)

-- An odd parameter and a negative even numerator in lowest terms.
example (y : ℚ) : ¬ (fruitWeierstrassCurve (-1 : ℚ)).toAffine.Equation (-4 / 5) y :=
  fruitWeierstrassCurve_rat_not_equation_of_two_dvd_num (-1) (-4 / 5) y (by decide +kernel)

-- The same curve family does have rational points with odd numerator.
example : (fruitWeierstrassCurve (1 : ℚ)).toAffine.Nonsingular (101 / 16) (1225 / 64) ∧
    ¬ 2 ∣ (101 / 16 : ℚ).num := by
  constructor
  · rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
    norm_num [fruitWeierstrassCurve, WeierstrassCurve.toAffine]
  · decide +kernel

end MetaMathlibExt
