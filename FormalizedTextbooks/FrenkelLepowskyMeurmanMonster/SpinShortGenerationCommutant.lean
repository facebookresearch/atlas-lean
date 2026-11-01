/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinShortGeneration

/-! Commuting with every actual preferred short spin operator implies
commuting with all of the actual Q representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem spinShort_operator_inverse (q : Q) (x : SpinSpace) :
    spinOperator q (spinOperator q⁻¹ x) = x := by
  change spinRepresentation q (spinRepresentation q⁻¹ x) = x
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The Q elements whose actual spin operators commute with a given endomorphism. -/
def spinShortCommutingSubgroup (S : Module.End ℝ SpinSpace) : Subgroup Q where
  carrier := {q | ∀ x : SpinSpace, S (spinOperator q x) = spinOperator q (S x)}
  one_mem' x := by simp only [spinOperator_one, LinearMap.id_apply]
  mul_mem' := by
    intro p q hp hq x
    rw [spinOperator_mul]
    simp only [LinearMap.comp_apply]
    rw [hp, hq]
  inv_mem' := by
    intro q hq x
    apply (spinRepresentation q).injective
    change spinOperator q (S (spinOperator q⁻¹ x)) =
      spinOperator q (spinOperator q⁻¹ (S x))
    rw [spinShort_operator_inverse]
    have h := hq (spinOperator q⁻¹ x)
    rw [spinShort_operator_inverse] at h
    exact h.symm

/-- The central sign commutes with every real spin endomorphism. -/
theorem spinShort_central_mem_commuting (S : Module.End ℝ SpinSpace) :
    qCentralInvolution ∈ spinShortCommutingSubgroup S := by
  intro x
  change S (spinRepresentation (qCentral 1) x) = spinRepresentation (qCentral 1) (S x)
  rw [spinRepresentation_central, spinRepresentation_central, map_smul]

/-- Commutation with the actual short spin operators extends to every actual Q operator.
No separate central-commutation, invertibility, or orthogonality premise is needed. -/
theorem spinShort_commutes_all (S : Module.End ℝ SpinSpace)
    (hshort : ∀ r : GriessShortIndex,
      S.comp (spinOperator (griessShortQ r)) = (spinOperator (griessShortQ r)).comp S) :
    ∀ q : Q, S.comp (spinOperator q) = (spinOperator q).comp S := by
  have hK : spinShortCommutingSubgroup S = ⊤ := by
    apply spinShort_subgroup_eq_top
    · intro r x
      exact congrArg (fun T : Module.End ℝ SpinSpace => T x) (hshort r)
    · exact spinShort_central_mem_commuting S
  intro q
  have hq : q ∈ spinShortCommutingSubgroup S := by rw [hK]; exact Subgroup.mem_top q
  exact LinearMap.ext hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
