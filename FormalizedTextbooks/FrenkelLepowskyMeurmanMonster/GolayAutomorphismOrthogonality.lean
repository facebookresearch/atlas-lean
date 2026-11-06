/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphism

/-! Self orthogonality of the actual published Golay code.
This is needed to prove that codeword coordinate sign changes preserve the
sum congruence defining the Leech lattice (Seysen §9.2). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxHeartbeats 4000000 in
-- Kernel reduction checks the 144 finite generator dot products.
/-- Kernel-checked dot products of all 144 pairs of published generator rows. -/
theorem golayGenerators_self_orthogonal : ∀ j k : Fin 12,
    (∑ i : Fin 24, (golayGeneratorBit j i : ZMod 2) *
      (golayGeneratorBit k i : ZMod 2)) = 0 := by
  decide +kernel

/-- Bilinearity transports the finite generator calculation to all codewords. -/
theorem golayCode_self_orthogonal (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode) : ∑ i, c i * d i = 0 := by
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  change (∑ i, (∑ j, a j * (golayGeneratorBit j i : ZMod 2)) *
    (∑ k, b k * (golayGeneratorBit k i : ZMod 2))) = 0
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  have h : ∀ i : Fin 24,
      a j * (golayGeneratorBit j i : ZMod 2) * (b k * (golayGeneratorBit k i : ZMod 2)) =
      (a j * b k) * ((golayGeneratorBit j i : ZMod 2) * (golayGeneratorBit k i : ZMod 2)) := by
    intro i
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, golayGenerators_self_orthogonal, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
