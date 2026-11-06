/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignConjugation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignOmega

/-! Genuine high-code source conjugation with its complete all-one extraspecial correction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact high-code image, including the full central and all-one source factor. -/
def generatedAxisGlobalSignHighImage (a : Fin 2048) (q : Q) : Q :=
  (qCentralInvolution * sourceOmegaQ) * generatedAxisGlobalSignSpinImage a q *
    (qCentralInvolution * sourceOmegaQ)⁻¹

/-- Every high source word has its complete explicit extraspecial image in actual G. -/
theorem generatedAxisGlobalSignHigh_generated_conjugation (a : Fin 2048) (q : Q) :
    sourceGeneratedY (generatedAxisGlobalCodeHighLabel a) 0 * qIntoGenerated q *
        (sourceGeneratedY (generatedAxisGlobalCodeHighLabel a) 0)⁻¹ =
      qIntoGenerated (generatedAxisGlobalSignHighImage a q) := by
  rw [generatedAxisGlobalSourceY_high_factor]
  have h := generatedAxisGlobalSignLow_generated_conjugation a q
  change sourceGeneratedY (generatedAxisGlobalCodeLowLabel a) 0 * qIntoGenerated q *
    (sourceGeneratedY (generatedAxisGlobalCodeLowLabel a) 0)⁻¹ = _ at h
  calc
    _ = qIntoGenerated (qCentralInvolution * sourceOmegaQ) *
        (sourceGeneratedY (generatedAxisGlobalCodeLowLabel a) 0 * qIntoGenerated q *
          (sourceGeneratedY (generatedAxisGlobalCodeLowLabel a) 0)⁻¹) *
        (qIntoGenerated (qCentralInvolution * sourceOmegaQ))⁻¹ := by group
    _ = _ := by
      rw [h]
      simp only [generatedAxisGlobalSignHighImage, map_mul, map_inv]

/-- The actual high sign fiber has exactly this explicit full Q image. -/
theorem generatedAxisGlobalSignHigh_QImage (a : Fin 2048) (q : Q) :
    spinConjugation (generatedFifthSignFiber (generatedAxisGlobalCodeHighLabel a) 0).val.1 q =
      generatedAxisGlobalSignHighImage a q := by
  apply inclQ_injective
  apply localIntoGenerated_injective
  have h := inclQ_spinConjugation
    (generatedFifthSignFiber (generatedAxisGlobalCodeHighLabel a) 0) q
  rw [generatedFifth_sign_fiber_local] at h
  have hg := congrArg localIntoGenerated h
  rw [map_mul, map_mul, map_inv, generatedFifth_sign_local_generated] at hg
  exact hg.trans (generatedAxisGlobalSignHigh_generated_conjugation a q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
