/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors

/-! Exact pairing of complete physical factor packets, without tensor-coordinate enumeration. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The actual spin-coordinate sum equals the finite source-label sum by their proved bijection. -/
theorem generatedAxisGlobal_spin_sum_labels (f : SpinIndex → ℝ) :
    (∑ t, f t) = ∑ k : Fin 4096, f (golayLabelCoefficients k) := by
  let e : Fin 4096 ≃ SpinIndex :=
    Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective
  exact (Equiv.sum_comp e f).symm

/-- Pairing two complete integer tensor factors requires only two exact finite scalar sums. -/
theorem generatedAxisGlobalTensorFactor_pairing
    (u U : Fin 4096 → ℤ) (v V : Fin 24 → ℤ) (D E : ℕ) (hD : 0 < D) (hE : 0 < E) :
    conwayTensorForm
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D)
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V) E) =
      ((∑ k, u k * U k : ℤ) : ℝ) * ((∑ i, v i * V i : ℤ) : ℝ) /
        (2 * (D : ℝ) * (E : ℝ)) := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have he : (E : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  change (∑ t : SpinIndex, ∑ i : Fin 24,
    generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D t i *
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V) E t i) = _
  rw [generatedAxisGlobal_spin_sum_labels]
  simp only [generatedAxisGlobalTensorIntegerPacket_coefficient,
    generatedAxisGlobalOddTensorFactor, Int.cast_mul]
  simp_rw [show ∀ k i,
    ((u k : ℝ) * v i / ((D : ℝ) * Real.sqrt 2)) *
      ((U k : ℝ) * V i / ((E : ℝ) * Real.sqrt 2)) =
        ((u k : ℝ) * U k) * ((v i : ℝ) * V i) / (2 * (D : ℝ) * (E : ℝ)) by
    intro k i
    field_simp
    rw [hsq]
    ring]
  simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul,
    Int.cast_sum, Int.cast_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
