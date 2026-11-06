/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadCoordinates

/-! The original octad sign convention is linear in its six free binary sign coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine code encoder and cocode syndrome are adjoint for the binary coordinate dot. -/
theorem generatedSixth_golay_syndrome_dot (u : SpinIndex) (c : Fin 24 → ZMod 2) :
    spinDot u (golaySyndrome c) = ∑ i : Fin 24, golayEncoder u i * c i := by
  simp only [spinDot, golaySyndrome, golayEncoder, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

set_option maxHeartbeats 4000000 in
-- Check the 64 original even sign masks; coefficients remain arbitrary binary variables.
/-- Every binary sign character is an ordinary six-coordinate dot product. -/
theorem generatedSixth_octad_sign_character (b : Fin 8 → ZMod 2) (e : Fin 64) :
    (∑ a : Fin 8, b a * (if (trialityEvenMask e).testBit a.val then 1 else 0)) =
      ∑ a : Fin 6, (b (Fin.castAdd 2 a) + b 6) *
        (if e.val.testBit a.val then 1 else 0) := by
  have hbit : ∀ e : Fin 64, ∀ a : Fin 8,
      (if (trialityEvenMask e).testBit a.val then (1 : ZMod 2) else 0) =
        ∑ j : Fin 6,
          ((if a = Fin.castAdd 2 j then 1 else 0) + (if a = 6 then 1 else 0)) *
            (if e.val.testBit j.val then 1 else 0) := by
    decide +kernel
  simp_rw [hbit, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_add, mul_ite, mul_one, mul_zero]
  split_ifs with he
  · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp only [Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
