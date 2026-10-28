/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Concrete normal-generation prerequisites for the actual Conway quotient.
The published Golay word 0x400 has mask 0x11111e. Its sign operation
reflects the source order-three ξ operation into its inverse.
No assertion that these operations generate all lattice isometries is made.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationSignsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual code sign isometry belonging to the published reflection word. -/
noncomputable def co1ReflectionIsometry : leechIsomSubgroup := golaySignIsometry co1ReflectionCode

/-- The same reflection matrix over the real coordinate space. -/
noncomputable def co1ReflectionMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  co1ReflectionMatrixQ.map (Rat.castHom ℝ)

theorem co1ReflectionIsometry_apply (x : Fin 24 → ℝ) :
    co1ReflectionIsometry.val x = co1ReflectionMatrix *ᵥ x := by
  funext i
  have he := co1ReflectionCode_bits i
  change qSign (co1ReflectionCode.val i) * x i = _
  rw [he]
  have hm : co1ReflectionMatrix = Matrix.diagonal (fun j => (co1ReflectionScalarQ j : ℝ)) := by
    ext j k
    simp only [co1ReflectionMatrix, co1ReflectionMatrixQ, Matrix.map_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hm]
  rw [Matrix.mulVec_diagonal]
  unfold co1ReflectionScalarQ
  split_ifs <;> simp [qSign_zero, qSign_one]

/-- Real transport of the kernel-checked rational reflection identity. -/
theorem co1Reflection_xi_real :
    co1ReflectionMatrix * co1XiMatrix * co1ReflectionMatrix = co1XiMatrix * co1XiMatrix := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix co1Reflection_xi_certificate
  rw [map_mul, map_mul, map_mul] at h
  exact h

/-- Reflection in the actual lattice isometry group gives the square of ξ. -/
theorem co1ReflectionIsometry_xi_square :
    co1ReflectionIsometry * co1XiIsometry * co1ReflectionIsometry = co1XiIsometry ^ 2 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change co1ReflectionIsometry.val (co1XiIsometry.val (co1ReflectionIsometry.val x)) =
    co1XiIsometry.val (co1XiIsometry.val x)
  rw [co1ReflectionIsometry_apply, co1ReflectionIsometry_apply]
  change co1ReflectionMatrix *ᵥ (co1XiMatrix *ᵥ (co1ReflectionMatrix *ᵥ x)) =
    co1XiMatrix *ᵥ (co1XiMatrix *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    co1Reflection_xi_real, Matrix.mulVec_mulVec]

/-- The actual source code reflection is involutive. -/
theorem co1ReflectionIsometry_square : co1ReflectionIsometry * co1ReflectionIsometry = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  change qSign (co1ReflectionCode.val i) * (qSign (co1ReflectionCode.val i) * x i) = x i
  rw [← mul_assoc, qSign_sq, one_mul]

/-- The ξ square is its inverse in the genuine lattice isometry group. -/
theorem co1XiIsometry_square_eq_inverse : co1XiIsometry ^ 2 = co1XiIsometry⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using co1XiIsometry_cube

/-- The actual published Golay code sign inverts the actual published ξ isometry. -/
theorem co1ReflectionIsometry_conjugates_xi_inverse :
    co1ReflectionIsometry * co1XiIsometry * co1ReflectionIsometry⁻¹ = co1XiIsometry⁻¹ := by
  rw [inv_eq_of_mul_eq_one_left co1ReflectionIsometry_square,
    co1ReflectionIsometry_xi_square, co1XiIsometry_square_eq_inverse]

/-- Any normal subgroup of the actual lattice isometry group containing the
source code sign also contains the source three-bases operation. -/
theorem co1XiIsometry_mem_of_reflection_mem (K : Subgroup ↥leechIsomSubgroup)
    [hK : K.Normal] (hd : co1ReflectionIsometry ∈ K) : co1XiIsometry ∈ K := by
  have hinv : co1XiIsometry⁻¹ * co1XiIsometry⁻¹ = co1XiIsometry := by
    apply mul_right_cancel (b := co1XiIsometry * co1XiIsometry)
    calc
      _ = 1 := by group
      _ = co1XiIsometry * (co1XiIsometry * co1XiIsometry) := by
        simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
          using co1XiIsometry_cube.symm
  have hm : co1XiIsometry⁻¹ * co1ReflectionIsometry * co1XiIsometry *
      co1ReflectionIsometry⁻¹ = co1XiIsometry := by
    calc
      _ = co1XiIsometry⁻¹ * (co1ReflectionIsometry * co1XiIsometry *
          co1ReflectionIsometry⁻¹) := by group
      _ = co1XiIsometry⁻¹ * co1XiIsometry⁻¹ := by
        rw [co1ReflectionIsometry_conjugates_xi_inverse]
      _ = co1XiIsometry := hinv
  rw [← hm]
  exact K.mul_mem (hK.conj_mem _ hd co1XiIsometry⁻¹) (K.inv_mem hd)

/-- The actual source reflection class in the Conway quotient. -/
noncomputable def co1ReflectionClass : Co1 := QuotientGroup.mk co1ReflectionIsometry

/-- The actual source three-bases class in the Conway quotient. -/
noncomputable def co1XiClass : Co1 := QuotientGroup.mk co1XiIsometry

/-- A normal subgroup of the actual Conway quotient containing the published
code sign contains the published three-bases class. -/
theorem co1XiClass_mem_of_reflectionClass_mem (K : Subgroup Co1) [K.Normal]
    (hd : co1ReflectionClass ∈ K) : co1XiClass ∈ K := by
  exact co1XiIsometry_mem_of_reflection_mem
    (K.comap (QuotientGroup.mk' signsSubgroup)) hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
