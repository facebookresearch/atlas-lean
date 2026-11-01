/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceOctadSparseCertificatesAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortActual

/-! Whole incoming source and original final integer bindings from exact sparse certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- All 759 by 64 packed incoming coefficients equal the complete bounded sparse source. -/
theorem generatedTenth_final_source_octad_sparse_source (o : Fin 759) (f : Fin 64) :
    generatedTenthFinalSourceCertificateIncomingC (Sum.inr (Sum.inl (o, f))) =
      generatedTenthFinalSourceOctadSparseCoefficient o f := by
  let a : Fin 48576 := ⟨64 * o.val + f.val, by omega⟩
  have ho : generatedTenthFinalSourceOctadSparseOctad a = o := by
    apply Fin.ext
    dsimp [generatedTenthFinalSourceOctadSparseOctad, a]
    omega
  have hf : generatedTenthFinalSourceOctadSparseCoordinate a = f := by
    apply Fin.ext
    dsimp [generatedTenthFinalSourceOctadSparseCoordinate, a]
    omega
  simpa only [GeneratedTenthFinalSourceOctadSparseCertificate, ho, hf] using
    generatedTenth_final_source_octad_sparse_certificates_all a

/-- The original Root02 dictionary retains every signed coefficient and outside-support zero. -/
theorem generatedTenth_final_source_octad_sparse_original_source (o : Fin 759) (f : Fin 64) :
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
      (Sum.inr (Sum.inl (o, f))) = generatedTenthFinalSourceOctadSparseCoefficient o f := by
  rw [← generatedTenth_final_source_certificate_incoming_actual]
  exact generatedTenth_final_source_octad_sparse_source o f

/-- The genuine actual incoming short field has exactly the certified denominator-sixteen source. -/
theorem generatedTenth_final_source_octad_sparse_incoming_actual (o : Fin 759) (f : Fin 64) :
    generatedAxisGlobalFifthRoot02Packet.2.1 (Sum.inr (Sum.inl (o, f))) =
      (generatedTenthFinalSourceOctadSparseCoefficient o f : ℝ) / 16 := by
  rw [generatedTenth_final_short_source_incoming_C generatedTenth_root_two_certificates_all,
    generatedTenth_final_source_octad_sparse_original_source]

/-- The full original triality sum equals at most fifteen certified signed source terms. -/
theorem generatedTenth_final_source_octad_sparse_sum (o : Fin 759) (e : Fin 64) :
    (∑ f : Fin 64, trialityIntegerMatrix e f *
      generatedTenthFinalSourceCertificateIncomingC (Sum.inr (Sum.inl (o, f)))) =
        generatedTenthFinalSourceOctadSparseSum o e := by
  simp_rw [generatedTenth_final_source_octad_sparse_source]
  unfold generatedTenthFinalSourceOctadSparseCoefficient generatedTenthFinalSourceOctadSparseSum
  rw [generatedTenth_final_source_octad_sparse_short_word_eq]
  exact generatedTenth_final_source_octad_sparse_word_sum _ e

/-- The original final C integer predicate uses the exact certified bounded octad sum. -/
theorem generatedTenth_final_source_octad_sparse_integer (o : Fin 759) (e : Fin 64) :
    generatedTenthFinalSourceCertificateCInteger (Sum.inr (Sum.inl (o, e))) =
      generatedTenthFinalSourceOctadSparseSum o e := by
  exact generatedTenth_final_source_octad_sparse_sum o e

/-- Only the octad branch uses the sparse source; all original non-octad formulas are retained. -/
def generatedTenthFinalSourceOctadSparseCInteger : GriessShortIndex → ℤ
  | Sum.inr (Sum.inl (o, e)) => generatedTenthFinalSourceOctadSparseSum o e
  | r => generatedTenthFinalSourceCertificateCInteger r

/-- A whole function equality permits proof-body rewriting without changing any old predicate. -/
theorem generatedTenth_final_source_octad_sparse_C_function :
    generatedTenthFinalSourceCertificateCInteger = generatedTenthFinalSourceOctadSparseCInteger :=
  by
  funext r
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · exact generatedTenth_final_source_octad_sparse_integer o e
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
