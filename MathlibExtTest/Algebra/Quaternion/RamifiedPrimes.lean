/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.RamifiedPrimes
public import MathlibExt.Algebra.Quaternion.BaseChange
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TwoFormula

/-!
# Tests for the ramified primes $\Delta_{a,b}$ of $H_{a,b}$
-/

set_option autoImplicit false

@[expose] public section

open scoped Quaternion TensorProduct

namespace QuaternionRamifiedPrimesTest

/-- $(ij)^2 = -ab$; for Hamilton's quaternions $a = b = -1$ this is $k^2 = -1$. -/
example : ((⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]) * ⟨0, 0, 1, 0⟩) ^ 2 = algebraMap ℚ _ (-1) := by
  rw [QuaternionAlgebra.i_mul_j_sq]
  norm_num

/-- $H_{a,b} \otimes \mathbb{Q}_p$ is `ℍ[ℚ_[p], a, b]` (`QuaternionAlgebra.baseChange`), the algebra
in the definition of $\Delta_{a,b}$. -/
noncomputable example (p : ℕ) [Fact p.Prime] (a b : ℚ) :
    ℚ_[p] ⊗[ℚ] ℍ[ℚ,a,b] ≃ₐ[ℚ_[p]] ℍ[ℚ_[p],(a : ℚ_[p]),0,(b : ℚ_[p])] :=
  QuaternionAlgebra.baseChange (by simp) (by simp) (by simp)

/-- $(-1, -1)_2 = -1$. -/
theorem padicHilbertSymbol_two_neg_one_neg_one :
    padicHilbertSymbol 2 (Units.map (Rat.castHom ℚ_[2]).toMonoidHom (-1))
      (Units.map (Rat.castHom ℚ_[2]).toMonoidHom (-1)) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 0 0 (-1) (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- Hamilton's quaternions ramify at $2$: $2 \in \Delta_{-1,-1}$. -/
example : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ Rat.quaternionRamifiedPrimes (-1) (-1) := by
  have h := (Rat.mem_quaternionRamifiedPrimes_iff (-1) (-1) ⟨2, Nat.prime_two⟩).2
    padicHilbertSymbol_two_neg_one_neg_one
  simp only [Units.val_neg, Units.val_one] at h
  exact h

/-- $H_{1,b}$ is split everywhere: no prime is in $\Delta_{1,b}$, as $1^2 - 1 \cdot 1^2 = 0$. -/
theorem not_mem_quaternionRamifiedPrimes_one {b : ℚ} (hb : b ≠ 0) (p : Nat.Primes) :
    p ∉ Rat.quaternionRamifiedPrimes 1 b := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  intro hp
  obtain ⟨φ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero ℚ_[p] two_ne_zero
    ((1 : ℚ) : ℚ_[p]) (b : ℚ_[p]) (by simp) (by exact_mod_cast hb) 1 1 0 0 (by simp) (by simp)
  exact hp.false φ

#check @QuaternionAlgebra.i_mul_j_sq
#check @QuaternionAlgebra.nonempty_algEquiv_matrix_iff_hilbertSymbol_eq_one
#check @Rat.quaternionRamifiedPrimes
#check @Rat.mem_quaternionRamifiedPrimes_iff

end QuaternionRamifiedPrimesTest
