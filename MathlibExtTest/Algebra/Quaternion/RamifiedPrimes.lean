/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.RamifiedPrimes
public import MathlibExt.Algebra.Quaternion.BaseChange
public import MathlibExtTest.NumberTheory.Padics.HilbertSymbol.Bilinear

/-!
# Tests for the ramified primes $\Delta_{a,b}$ of $H_{a,b}$
-/

set_option autoImplicit false

@[expose] public section

open scoped Quaternion TensorProduct

namespace QuaternionRamifiedPrimesTest

/-- $(ij)^2 = -ab$ in `ℍ[R,a,b]`, from Mathlib's quaternion basis
(`QuaternionAlgebra.Basis.i_mul_j`, `QuaternionAlgebra.Basis.k_mul_k`). The coefficient $ab$ of
$x_4^2$ in the reduced norm comes from it: $\overline{ij} = -ij$, so
$\operatorname{nrd}(ij) = -(ij)^2 = ab$. -/
example {R : Type*} [CommRing R] (a b : R) :
    ((⟨0, 1, 0, 0⟩ : ℍ[R,a,b]) * ⟨0, 0, 1, 0⟩) ^ 2 = algebraMap R ℍ[R,a,b] (-(a * b)) := by
  let q := QuaternionAlgebra.Basis.self R (c₁ := a) (c₂ := 0) (c₃ := b)
  change (q.i * q.j) ^ 2 = _
  rw [q.i_mul_j, pow_two, q.k_mul_k, map_neg, Algebra.algebraMap_eq_smul_one]

/-- $H_{a,b} \otimes \mathbb{Q}_p$ is `ℍ[ℚ_[p], a, b]` (`QuaternionAlgebra.baseChange`), the algebra
in the definition of $\Delta_{a,b}$. -/
noncomputable example (p : ℕ) [Fact p.Prime] (a b : ℚ) :
    ℚ_[p] ⊗[ℚ] ℍ[ℚ,a,b] ≃ₐ[ℚ_[p]] ℍ[ℚ_[p],(a : ℚ_[p]),0,(b : ℚ_[p])] :=
  QuaternionAlgebra.baseChange (by simp) (by simp) (by simp)

/-- Hamilton's quaternions ramify at $2$: $2 \in \Delta_{-1,-1}$, as $(-1, -1)_2 = -1$
(`HilbertSymbolBilinearTest.neg_one_neg_one_two`). -/
example : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ Rat.quaternionRamifiedPrimes (-1) (-1) := by
  have hu : Units.map (Rat.castHom ℚ_[2]).toMonoidHom (-1 : ℚˣ) = -1 := Units.ext (by simp)
  have h := (Rat.mem_quaternionRamifiedPrimes_iff (-1) (-1) ⟨2, Nat.prime_two⟩).2
    (by rw [hu]; exact HilbertSymbolBilinearTest.neg_one_neg_one_two)
  simp only [Units.val_neg, Units.val_one] at h
  exact h

/-- For $b \ne 0$, $H_{1,b}$ is split everywhere: no prime is in $\Delta_{1,b}$, as
$1^2 - 1 \cdot 1^2 = 0$. -/
theorem not_mem_quaternionRamifiedPrimes_one {b : ℚ} (hb : b ≠ 0) (p : Nat.Primes) :
    p ∉ Rat.quaternionRamifiedPrimes 1 b := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  intro hp
  obtain ⟨φ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero ℚ_[p] two_ne_zero
    ((1 : ℚ) : ℚ_[p]) (b : ℚ_[p]) (by simp) (by exact_mod_cast hb) 1 1 0 0 (by simp) (by simp)
  exact hp.false φ

#check @QuaternionAlgebra.nonempty_algEquiv_matrix_iff_hilbertSymbol_eq_one
#check @Rat.quaternionRamifiedPrimes
#check @Rat.mem_quaternionRamifiedPrimes_iff

end QuaternionRamifiedPrimesTest
