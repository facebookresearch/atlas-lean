/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.LocallyIntegerPolynomialCircuitCoeffDen
import Mathlib.Tactic.NormNum

/-!
# Tests for the denominator of the top coefficient on a circuit

The circuit on `{0, 2}` with values `0, 1` has top coefficient denominator `2`.
-/

open MetaMathlibExt Polynomial

namespace MathlibExtTest.Algebra.LocallyIntegerPolynomialCircuitCoeffDen

example : ((interpolationPoly {0, 2} (fun z : ℤ => if z = 2 then 1 else 0)).coeff 1).den = 2 := by
  let f : ℤ → ℤ := fun z => if z = 2 then 1 else 0
  have hX : interpolationPoly {0, 2} f ∉ Polynomial.lifts (Int.castRingHom ℚ) := by
    intro h
    obtain ⟨p, hp⟩ := (mem_lifts _).mp h
    have h0 := eval_interpolationPoly (X := {0, 2}) f (x := 0) (by simp)
    have h2 := eval_interpolationPoly (X := {0, 2}) f (x := 2) (by simp)
    rw [← hp, eval_intCast_map] at h0 h2
    have hp0 : p.eval 0 = 0 := by simpa [f] using h0
    have hp2 : p.eval 2 = 1 := by exact_mod_cast (by simpa [f] using h2)
    have hdiv := Polynomial.sub_dvd_eval_sub (2 : ℤ) 0 p
    rw [hp0, hp2] at hdiv
    norm_num at hdiv
  have hmin : ∀ a ∈ ({0, 2} : Finset ℤ),
      interpolationPoly (({0, 2} : Finset ℤ).erase a) f ∈
        Polynomial.lifts (Int.castRingHom ℚ) := by
    have hs (a : ℤ) : interpolationPoly {a} f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
      rw [interpolationPoly, Lagrange.interpolate_singleton]
      exact C_mem_lifts _ _
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simpa using hs 2
    · have he : ({0, 2} : Finset ℤ).erase 2 = {0} := by decide
      rw [he]
      exact hs 0
  have h := circuit_coeff_den f {0, 2} hX hmin
  have hdiv := h.2 2 (by simp) 0 (by simp)
  have hnat : ((interpolationPoly {0, 2} f).coeff 1).den ∣ 2 := by
    simpa using (Int.natCast_dvd_natCast.mp (by simpa using hdiv))
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hnat with h1 | h2
  · have hne : ((interpolationPoly {0, 2} f).coeff 1).den ≠ 1 := by simpa using h.1
    exact (hne h1).elim
  · exact h2

end MathlibExtTest.Algebra.LocallyIntegerPolynomialCircuitCoeffDen
