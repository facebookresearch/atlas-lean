/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactDeltaPhase

/-! Ungated full128 source-Pauli image bindings; a whole Q certificate retains every central bit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All128 fixed images must equal the genuine original complete source Q evaluator. -/
def GeneratedTenthSourceSparseFastQCertificate : Prop :=
  ∀ (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2),
    generatedTenthSourceSparseFastQ p b =
      generatedAxisGlobalFifthQFast 2 (generatedTenthSourceCompactTranslationQ
        (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Scope the bounded prospective full128 image computation; this theorem remains uncompiled.
/-- Prospective full finite image certificate, including all translation/modulation/central bits. -/
theorem generatedTenth_source_sparse_fast_q_certificate :
    GeneratedTenthSourceSparseFastQCertificate := by
  have hb : ∀ (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2)
      (k : Fin 24),
      Multiplicative.toAdd (generatedTenthSourceSparseFastQ p b).base k =
        Multiplicative.toAdd (generatedAxisGlobalFifthQFast 2
          (generatedTenthSourceCompactTranslationQ
            (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b)))).base k := by
    decide +kernel
  have hc : ∀ (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2),
      Multiplicative.toAdd (generatedTenthSourceSparseFastQ p b).coeff =
        Multiplicative.toAdd (generatedAxisGlobalFifthQFast 2
          (generatedTenthSourceCompactTranslationQ
            (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b)))).coeff := by
    decide +kernel
  intro p b
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    funext k
    exact hb p b k
  · apply Multiplicative.toAdd.injective
    exact hc p b

/-- The cached full image is genuinely bound to compact source conjugation. -/
theorem generatedTenth_source_sparse_fast_q_actual
    (hQ : GeneratedTenthSourceSparseFastQCertificate)
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (b : Fin 2) :
    generatedTenthSourceSparseFastQ p b =
      generatedTenthAxisLowerRecoverySourceCompactQImage 0
        (generatedTenthSourceCompactTranslationQ
          (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b))) := by
  calc
    _ = generatedAxisGlobalFifthQFast 2 (generatedTenthSourceCompactTranslationQ
        (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b))) := hQ p b
    _ = spinConjugation (generatedTenthAxisLowerRecoverySourceCompactSpin 0)
        (generatedTenthSourceCompactTranslationQ
          (golayLabelCoefficients (generatedTenthSourceSparseFastLabel p b))) :=
      (generatedTenth_source_q_certificates_fast _).symm
    _ = _ := generatedTenth_axis_lower_recovery_source_compact_conjugation 0 _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

