/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactQCertificatesAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

/-! Ungated genuine compact source binding; full central signs are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine chosen spin component of the complete original Root02 source word. -/
def generatedTenthAxisLowerRecoveryOriginalSourceSpin : SpinHolomorph :=
  (generatedAxisGlobalFifthShortWordFiber 2).val.1

/-- Split full-Q certificates bind the entire genuine original conjugation, retaining its center. -/
theorem generatedTenth_axis_lower_recovery_source_compact_Q_eq (q : Q) :
    spinConjugation generatedTenthAxisLowerRecoveryOriginalSourceSpin q =
      spinConjugation (generatedTenthAxisLowerRecoverySourceCompactSpin 0) q :=
  generatedTenth_source_q_certificates_original_Q_eq q

private theorem source_scalar_of_conjugation_eq (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace, a.val x = c • b.val x := by
  let s : SpinHolomorph := a * b⁻¹
  have hk : s ∈ spinConjugation.ker := by
    change spinConjugation s = 1
    dsimp only [s]
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc, hs⟩ := spinHolomorph_conjugation_kernel_scalar ⟨s, hk⟩
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hs (b.val x)
  change a.val (b.val.symm (b.val x)) = c • b.val x at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- The actual chosen source spin and the explicit compact source differ by a genuine central sign.
This does not choose the source fiber orientation. -/
theorem generatedTenth_axis_lower_recovery_source_compact_scalar :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace,
      generatedTenthAxisLowerRecoveryOriginalSourceSpin.val x =
        c • (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val x :=
  source_scalar_of_conjugation_eq _ _
    (MulEquiv.ext generatedTenth_axis_lower_recovery_source_compact_Q_eq)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
