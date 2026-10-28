/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction

/-! The genuine binary lifts and central involution determine every Q homomorphism. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A subgroup containing the genuine coordinate lifts has full actual binary quotient. -/
theorem generatedFourth_lift_basis_binaryImage (K : Subgroup Q)
    (hb : ∀ j, xiSpinBinaryBasisLift j ∈ K) : qSubgroupBinaryImage K = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 24)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  simp only [Pi.basisFun_apply]
  change ofAdd (Pi.single j 1) ∈ K.map qQuotHom
  exact ⟨xiSpinBinaryBasisLift j, hb j, rfl⟩

/-- Actual coordinate lifts together with the central involution generate Q. -/
theorem generatedFourth_lift_basis_subgroup_eq_top (K : Subgroup Q)
    (hb : ∀ j, xiSpinBinaryBasisLift j ∈ K) (hz : qCentralInvolution ∈ K) : K = ⊤ :=
  qSubgroup_eq_top_of_binaryImage_eq_top K (centerQ_le_of_central_mem K hz)
    (generatedFourth_lift_basis_binaryImage K hb)

/-- Full Q homomorphism equality follows from twenty-four lift images and the central image. -/
theorem generatedFourth_lift_q_hom_ext {D : Type*} [Group D] (f g : Q →* D)
    (hb : ∀ j, f (xiSpinBinaryBasisLift j) = g (xiSpinBinaryBasisLift j))
    (hz : f qCentralInvolution = g qCentralInvolution) : f = g := by
  have he : f.eqLocus g = ⊤ := generatedFourth_lift_basis_subgroup_eq_top _ hb hz
  ext q
  have hq : q ∈ f.eqLocus g := by rw [he]; exact Subgroup.mem_top q
  exact hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
