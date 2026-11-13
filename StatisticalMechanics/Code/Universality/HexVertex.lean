/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib

namespace StatMech.Universality

open Complex








theorem hexExpI_mul (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring


theorem hexExpI_zpow (a : ℝ) (k : ℤ) :
    (Complex.exp ((a : ℂ) * Complex.I)) ^ k
      = Complex.exp ((((k : ℝ) * a : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_int_mul]; congr 1; push_cast; ring


theorem hexExpI_add_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.cos θ : ℂ) := by
  rw [show ((-θ : ℝ) : ℂ) = -(θ : ℂ) by push_cast; ring,
      ← Complex.two_cos, Complex.ofReal_cos]












noncomputable def hexOmega : ℂ := Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)


theorem hexOmega_sq :
    hexOmega ^ 2 = Complex.exp (((2 * (2 * Real.pi / 3) : ℝ) : ℂ) * Complex.I) := by
  unfold hexOmega
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring



noncomputable def hexLambda : ℂ := Complex.exp ((-(5 * Real.pi / 24) : ℝ) * Complex.I)


noncomputable def hexChi : ℝ := 1 / (2 * Real.cos (Real.pi / 8))


theorem hexCos_pi8_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos, Real.pi_le_four]


theorem hexChi_pos : 0 < hexChi := by
  unfold hexChi
  have := hexCos_pi8_pos
  positivity




theorem hexChi_eq_sqrt : hexChi = 1 / Real.sqrt (2 + Real.sqrt 2) := by
  unfold hexChi
  congr 1
  
  have hcospos := hexCos_pi8_pos
  have hpos : (0 : ℝ) ≤ 2 * Real.cos (Real.pi / 8) := by
    positivity
  rw [show (2 + Real.sqrt 2 : ℝ) = (2 * Real.cos (Real.pi / 8)) ^ 2 by
        have hcos2 : Real.cos (Real.pi / 8) ^ 2 = (1 + Real.cos (Real.pi / 4)) / 2 := by
          have := Real.cos_sq (Real.pi / 8)
          rw [this]; ring_nf
        have hcosq : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        rw [mul_pow, hcos2, hcosq]; ring]
  rw [Real.sqrt_sq hpos]
















theorem hexPair_zero :
    hexOmega * hexLambda ^ (-4 : ℤ) + hexOmega ^ 2 * hexLambda ^ (4 : ℤ) = 0 := by
  rw [hexOmega_sq]
  unfold hexOmega hexLambda
  rw [hexExpI_zpow, hexExpI_zpow, hexExpI_mul, hexExpI_mul]
  
  have h1 : (2 * Real.pi / 3) + (((-4 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
      = 3 * Real.pi / 2 := by push_cast; ring
  
  
  have h2 : (2 * (2 * Real.pi / 3)) + (((4 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
      = -(3 * Real.pi / 2) + 2 * Real.pi := by push_cast; ring
  rw [h1, h2]
  
  rw [show (((-(3 * Real.pi / 2) + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = ((-(3 * Real.pi / 2) : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [hexExpI_add_neg]
  
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add]
    simp
  rw [hcos]; simp









theorem hexTriplet_zero :
    (1 : ℂ) + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
      + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ)) = 0 := by
  
  have hsum : hexOmega * hexLambda ^ (-1 : ℤ) + hexOmega ^ 2 * hexLambda ^ (1 : ℤ)
      = 2 * (Real.cos (7 * Real.pi / 8) : ℂ) := by
    rw [hexOmega_sq]
    unfold hexOmega hexLambda
    rw [hexExpI_zpow, hexExpI_zpow, hexExpI_mul, hexExpI_mul]
    have h1 : (2 * Real.pi / 3) + (((-1 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
        = 7 * Real.pi / 8 := by push_cast; ring
    have h2 : (2 * (2 * Real.pi / 3)) + (((1 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
        = -(7 * Real.pi / 8) + 2 * Real.pi := by push_cast; ring
    rw [h1, h2]
    rw [show (((-(7 * Real.pi / 8) + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
          = ((-(7 * Real.pi / 8) : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by
          push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexExpI_add_neg]
  
  rw [show (1 : ℂ) + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
          + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ))
        = 1 + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ)
              + hexOmega ^ 2 * hexLambda ^ (1 : ℤ)) by ring,
      hsum]
  have hcos7 : Real.cos (7 * Real.pi / 8) = - Real.cos (Real.pi / 8) := by
    rw [show (7 * Real.pi / 8 : ℝ) = Real.pi - Real.pi / 8 by ring, Real.cos_pi_sub]
  unfold hexChi
  have hcos_ne : (Real.cos (Real.pi / 8) : ℂ) ≠ 0 := by
    exact_mod_cast hexCos_pi8_pos.ne'
  rw [hcos7,
      show ((-Real.cos (Real.pi / 8) : ℝ) : ℂ) = -(Real.cos (Real.pi / 8) : ℂ) by push_cast; ring,
      show ((1 / (2 * Real.cos (Real.pi / 8)) : ℝ) : ℂ)
        = 1 / (2 * (Real.cos (Real.pi / 8) : ℂ)) by push_cast; ring]
  field_simp
  ring






























noncomputable def hexContribution (dir : ℂ) (k : ℤ) (n : ℕ) : ℂ :=
  dir * hexLambda ^ k * (hexChi : ℂ) ^ n






theorem hexPairContribution_zero (du : ℂ) (k : ℤ) (n : ℕ) :
    hexContribution (hexOmega * du) (k - 4) n
      + hexContribution (hexOmega ^ 2 * du) (k + 4) n = 0 := by
  unfold hexContribution
  have hlne : hexLambda ≠ 0 := by
    unfold hexLambda; exact Complex.exp_ne_zero _
  
  rw [show hexLambda ^ (k - 4) = hexLambda ^ k * hexLambda ^ (-4 : ℤ) by
        rw [sub_eq_add_neg, zpow_add₀ hlne],
      show hexLambda ^ (k + 4) = hexLambda ^ k * hexLambda ^ (4 : ℤ) by
        rw [zpow_add₀ hlne]]
  have key := hexPair_zero
  
  
  calc
    hexOmega * du * (hexLambda ^ k * hexLambda ^ (-4 : ℤ)) * (hexChi : ℂ) ^ n
        + hexOmega ^ 2 * du * (hexLambda ^ k * hexLambda ^ (4 : ℤ)) * (hexChi : ℂ) ^ n
      = (du * hexLambda ^ k * (hexChi : ℂ) ^ n)
          * (hexOmega * hexLambda ^ (-4 : ℤ) + hexOmega ^ 2 * hexLambda ^ (4 : ℤ)) := by ring
    _ = (du * hexLambda ^ k * (hexChi : ℂ) ^ n) * 0 := by rw [key]
    _ = 0 := by ring






theorem hexTripletContribution_zero (du : ℂ) (k : ℤ) (n : ℕ) :
    hexContribution du k n
      + hexContribution (hexOmega * du) (k - 1) (n + 1)
      + hexContribution (hexOmega ^ 2 * du) (k + 1) (n + 1) = 0 := by
  unfold hexContribution
  have hlne : hexLambda ≠ 0 := by
    unfold hexLambda; exact Complex.exp_ne_zero _
  rw [show hexLambda ^ (k - 1) = hexLambda ^ k * hexLambda ^ (-1 : ℤ) by
        rw [sub_eq_add_neg, zpow_add₀ hlne],
      show hexLambda ^ (k + 1) = hexLambda ^ k * hexLambda ^ (1 : ℤ) by
        rw [zpow_add₀ hlne],
      pow_succ]
  have key := hexTriplet_zero
  calc
    du * hexLambda ^ k * (hexChi : ℂ) ^ n
        + hexOmega * du * (hexLambda ^ k * hexLambda ^ (-1 : ℤ)) * ((hexChi : ℂ) ^ n * (hexChi : ℂ))
        + hexOmega ^ 2 * du * (hexLambda ^ k * hexLambda ^ (1 : ℤ)) * ((hexChi : ℂ) ^ n * (hexChi : ℂ))
      = (du * hexLambda ^ k * (hexChi : ℂ) ^ n)
          * (1 + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
              + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ))) := by ring
    _ = (du * hexLambda ^ k * (hexChi : ℂ) ^ n) * 0 := by rw [key]
    _ = 0 := by ring

















structure VertexWalkData where
  
  du : ℂ
  
  pairs : Finset ℕ
  
  pairWind : ℕ → ℤ
  
  pairLen : ℕ → ℕ
  
  triplets : Finset ℕ
  
  tripWind : ℕ → ℤ
  
  tripLen : ℕ → ℕ

namespace VertexWalkData

variable (D : VertexWalkData)





noncomputable def vertexSum : ℂ :=
  (∑ P ∈ D.pairs,
      (hexContribution (hexOmega * D.du) (D.pairWind P - 4) (D.pairLen P)
        + hexContribution (hexOmega ^ 2 * D.du) (D.pairWind P + 4) (D.pairLen P)))
  + (∑ T ∈ D.triplets,
      (hexContribution D.du (D.tripWind T) (D.tripLen T)
        + hexContribution (hexOmega * D.du) (D.tripWind T - 1) (D.tripLen T + 1)
        + hexContribution (hexOmega ^ 2 * D.du) (D.tripWind T + 1) (D.tripLen T + 1)))








theorem relation : D.vertexSum = 0 := by
  unfold vertexSum
  rw [Finset.sum_eq_zero (fun P _ => hexPairContribution_zero D.du (D.pairWind P) (D.pairLen P)),
      Finset.sum_eq_zero (fun T _ => hexTripletContribution_zero D.du (D.tripWind T) (D.tripLen T)),
      add_zero]

end VertexWalkData

end StatMech.Universality
