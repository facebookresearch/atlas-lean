/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConstantTermZeroDensity

namespace MetaMathlibExt

open AddMonoidAlgebra

-- With P = x and Q = x⁻¹ the unique nonzero residue occurs at n = 1.
example :
    let e : Fin 1 → ℤ := fun _ => 1
    let P : AddMonoidAlgebra ℤ (Fin 1 → ℤ) := single e 1
    let Q : AddMonoidAlgebra ℤ (Fin 1 → ℤ) := single (-e) 1
    ({n : ℕ | (2 : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1 ∧
      ¬ IsUniformlyRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod 2) := by
  intro e P Q
  have he : e ≠ 0 := fun h => by simpa [e] using congrFun h 0
  have hw : (2 : ℤ) ∣ (P ^ 1).coeff 0 := by simp [P, he, eq_comm]
  obtain ⟨hdensity, _, hall | hrec⟩ :=
    constantTerm_zero_density_mod_prime Nat.prime_two P ⟨1, hw⟩ Q
  · have h := hall 1
    norm_num [P, Q, single_mul_single] at h
  · exact ⟨hdensity, hrec⟩

-- The all-zero sequence is uniformly recurrent even with no variables.
example {p : ℕ} (hp : p.Prime) (P : AddMonoidAlgebra ℤ (Fin 0 → ℤ))
    (hP : ∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) :
    ∀ n, (p : ℤ) ∣ (P ^ n * 0).coeff 0 := by
  apply (constantTerm_zero_density_mod_prime hp P hP 0).2.2.resolve_right
  apply not_not.mpr
  intro i ℓ
  exact ⟨1, fun j _ => ⟨1, by decide, le_rfl, fun t _ => by simp⟩⟩

end MetaMathlibExt
