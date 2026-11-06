/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The source y82 local candidate has its verified order-two relation before source-word binding. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Compatibility

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal source affine change of spin labels. -/
def monsterSourceY82Affine (t : SpinIndex) : SpinIndex :=
  t + (1 + t 11) • monsterSourceY82Code

/-- Its last coordinate remains fixed because e82 has no all-one component. -/
theorem monsterSourceY82Affine_last (t : SpinIndex) : monsterSourceY82Affine t 11 = t 11 := by
  change t 11 + (1 + t 11) * monsterSourceY82Code 11 = t 11
  rw [monsterSourceY82Code_last, mul_zero, add_zero]

/-- The explicit affine source relabeling is an involution. -/
theorem monsterSourceY82Affine_double (t : SpinIndex) :
    monsterSourceY82Affine (monsterSourceY82Affine t) = t := by
  ext i
  change (t i + (1 + t 11) * monsterSourceY82Code i) +
    (1 + monsterSourceY82Affine t 11) * monsterSourceY82Code i = t i
  rw [monsterSourceY82Affine_last, add_assoc, CharTwo.add_self_eq_zero, add_zero]

set_option maxHeartbeats 4000000 in
-- Check the thirteen finite values determining the phase along the code translation.
/-- The actual code vector belongs to the radical of the exact quadratic source phase. -/
theorem monsterSourceY82Phase_radical :
    monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code)
      monsterSourceY82Code = 0 ∧
    monsterMonomialGradient (monsterSourceYPhaseMatrix monsterSourceY82Code)
      monsterSourceY82Code = 0 := by
  decide +kernel

/-- The full exact phase is unchanged by the source affine relabeling. -/
theorem monsterSourceY82Phase_affine (t : SpinIndex) :
    monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code)
      (monsterSourceY82Affine t) =
        monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code) t := by
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  obtain h | h := hc (1 + t 11)
  · simp only [monsterSourceY82Affine, h, zero_smul, add_zero]
  · rw [monsterSourceY82Affine, h, one_smul]
    have ha := monsterMonomialQuadratic_add (monsterSourceYPhaseMatrix monsterSourceY82Code)
      monsterSourceY82Code t
    rw [monsterSourceY82Phase_radical.1, monsterSourceY82Phase_radical.2] at ha
    simpa only [add_comm monsterSourceY82Code t, zero_add, spinDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero] using ha

/-- The actual plus/minus operator evaluates with this exact quadratic sign and affine map. -/
theorem monsterSourceY82PlusMinus_quadratic (f : SpinSpace) (t : SpinIndex) :
    monsterSourceY82PlusMinus.val f t =
      qSign (monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code) t) *
        f (monsterSourceY82Affine t) := by
  rw [monsterSourceY82PlusMinus_apply, ← monsterSourceYPhaseMatrix_apply]
  rfl

/-- The actual signed plus/minus spin operator has square one. -/
theorem monsterSourceY82PlusMinus_square : monsterSourceY82PlusMinus ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  ext t
  change monsterSourceY82PlusMinus.val (monsterSourceY82PlusMinus.val f) t = f t
  rw [monsterSourceY82PlusMinus_quadratic, monsterSourceY82PlusMinus_quadratic,
    monsterSourceY82Affine_double, monsterSourceY82Phase_affine, ← mul_assoc, qSign_sq, one_mul]

/-- The full source spin candidate has square one in the actual orthogonal normalizer. -/
theorem monsterSourceY82Spin_square : monsterSourceY82Spin ^ 2 = 1 := by
  have hH : monsterSpinHadamardHolomorph * monsterSpinHadamardHolomorph = 1 := by
    apply Subtype.ext
    exact monsterSpinHadamardEquiv_square
  have hP : monsterSourceY82PlusMinus * monsterSourceY82PlusMinus = 1 := by
    rw [← pow_two, monsterSourceY82PlusMinus_square]
  rw [pow_two, monsterSourceY82Spin]
  calc
    _ = monsterSpinHadamardHolomorph * monsterSourceY82PlusMinus *
        (monsterSpinHadamardHolomorph * monsterSpinHadamardHolomorph) *
          monsterSourceY82PlusMinus * monsterSpinHadamardHolomorph := by simp only [mul_assoc]
    _ = monsterSpinHadamardHolomorph *
        (monsterSourceY82PlusMinus * monsterSourceY82PlusMinus) *
          monsterSpinHadamardHolomorph := by rw [hH]; simp only [mul_one, mul_assoc]
    _ = 1 := by rw [hP, mul_one, hH]

/-- The genuine physical code sign has square one on the actual Leech space. -/
theorem monsterSourceY82Isometry_square : monsterSourceY82Isometry ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  ext i
  change qSign (monsterSourceY82SignCode.val i) *
    (qSign (monsterSourceY82SignCode.val i) * f i) = f i
  rw [← mul_assoc, qSign_sq, one_mul]

/-- The exact compatible spin/lattice pair has square one before quotienting. -/
theorem monsterSourceY82Fiber_square : monsterSourceY82Fiber ^ 2 = 1 := by
  apply Subtype.ext
  exact Prod.ext monsterSourceY82Spin_square monsterSourceY82Isometry_square

/-- The explicit local source-coordinate candidate obeys its order-two relation in H. -/
theorem monsterSourceY82Local_square : monsterSourceY82Local ^ 2 = 1 := by
  have h := congrArg (QuotientGroup.mk' localDiagonalSubgroup) monsterSourceY82Fiber_square
  rw [map_pow, map_one] at h
  exact h

/-- The candidate is an actual involution in G, before identifying its source word. -/
theorem monsterSourceY82Generated_square : monsterSourceY82Generated ^ 2 = 1 := by
  rw [monsterSourceY82Generated, ← map_pow, monsterSourceY82Local_square, map_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
