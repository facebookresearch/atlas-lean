/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQEvenLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSignGeneration

/-! The full middle Pauli products give every genuine code sign in the Eighth projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every rank-eleven Pauli product fixes the complete middle axis. -/
theorem generatedEighth_pauli_product_full_fixed (a : Fin 11 → ZMod 2) :
    rhoLocal (inclQ (generatedEighthSpinPauliProduct a)) generatedEighthMiddleAxis =
      generatedEighthMiddleAxis := by
  change generatedEighthSpinPauliProduct a ∈ generatedEighthMiddleAxisQStabilizer
  apply generatedEighthMiddleAxisQStabilizer.list_prod_mem
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  apply generatedEighthMiddleAxisQStabilizer.pow_mem
  exact generatedEighth_pauli_final_full_fixed (generatedEighthSpinPauliIndependent j)

/-- Coefficient vectors whose actual sign quotient lies in the full-axis projection range. -/
def generatedEighthProjectedSignCoefficients : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
  (generatedFourthMonomialSignPreimage
    (generatedEighthProjectedAxisStabilizer.comap (QuotientGroup.mk' signsSubgroup))).comap
      golayEncoder.rangeRestrict

/-- Each actual rank-eleven translation gives a genuine projected complete-axis fixer. -/
theorem generatedEighth_projected_sign_translation (a : Fin 11 → ZMod 2) :
    generatedEighthSpinPauliTranslationMatrix *ᵥ a ∈ generatedEighthProjectedSignCoefficients := by
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.surjective
    (spinTranslation (generatedEighthSpinPauliProduct a))
  have hp := generatedEighth_pauli_local_lift_projection (generatedEighthSpinPauliProduct a)
    d hd.symm
  have hf := generatedEighth_pauli_local_lift_full_fixed (generatedEighthSpinPauliProduct a)
    (generatedEighth_pauli_product_full_fixed a)
  have hm : projH (generatedEighthPauliLocalLift (generatedEighthSpinPauliProduct a)) ∈
      generatedEighthProjectedAxisStabilizer :=
    ⟨⟨generatedEighthPauliLocalLift (generatedEighthSpinPauliProduct a), hf⟩, rfl⟩
  rw [hp] at hm
  change (QuotientGroup.mk' signsSubgroup
    (golaySignIsometry (golayEncoder.rangeRestrict
      (generatedEighthSpinPauliTranslationMatrix *ᵥ a)))) ∈
      generatedEighthProjectedAxisStabilizer
  have ht := generatedEighth_spin_pauli_product_translation a
  rw [← ht, ← hd]
  exact hm

/-- Omega gives the negative physical identity, hence the identity actual Conway quotient. -/
theorem generatedEighth_projected_sign_omega :
    Pi.single (11 : Fin 12) 1 ∈ generatedEighthProjectedSignCoefficients := by
  let c : golayCode := golayEncoder.rangeRestrict (Pi.single (11 : Fin 12) 1)
  change (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈
    generatedEighthProjectedAxisStabilizer
  have hs : golaySignIsometry c ∈ signsSubgroup := by
    right
    intro x
    funext i
    change qSign (golayEncoder (Pi.single (11 : Fin 12) 1) i) * x i = -x i
    rw [golay_all_one]
    simp only [qSign_one, neg_one_mul]
  have hz : (QuotientGroup.mk (golaySignIsometry c) : Co1) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hs
  rw [hz]
  exact generatedEighthProjectedAxisStabilizer.one_mem

/-- The actual rank-eleven translation space and omega cover every original sign coefficient. -/
theorem generatedEighth_projected_sign_coefficients_all (v : Fin 12 → ZMod 2) :
    v ∈ generatedEighthProjectedSignCoefficients := by
  have he := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M *ᵥ v)
    generatedEighth_spin_support_projection_certificate
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec] at he
  rw [← he]
  apply generatedEighthProjectedSignCoefficients.add_mem
  · exact generatedEighth_projected_sign_translation _
  · have hc : generatedEighthSpinSupportComplement *ᵥ
        (generatedEighthSpinSupportMatrix *ᵥ v) =
        (generatedEighthSpinSupportMatrix *ᵥ v) 0 • Pi.single (11 : Fin 12) 1 := by
      funext i
      simp [Matrix.mulVec, dotProduct, generatedEighthSpinSupportComplement,
        Pi.single_apply, mul_comm]
    rw [hc]
    exact generatedEighthProjectedSignCoefficients.smul_mem _ generatedEighth_projected_sign_omega

/-- Every genuine Golay code sign belongs to the full actual Eighth-axis projection. -/
theorem generatedEighth_projected_source_sign_mem (d : Fin 4096) :
    (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∈
      generatedEighthProjectedAxisStabilizer :=
  generatedEighth_projected_sign_coefficients_all (golayLabelCoefficients d)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
