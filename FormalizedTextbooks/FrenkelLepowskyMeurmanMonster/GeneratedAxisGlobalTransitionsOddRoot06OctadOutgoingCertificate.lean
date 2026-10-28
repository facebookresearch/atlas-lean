/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOutside
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadPairCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOddCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier00Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier01Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier02Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier03Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier04Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier05Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier06Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier07Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier08Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier09Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier10Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier11Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier12Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier13Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFourier14Certificate

/-! Every original outgoing short coordinate equals the complete sparse packet, including every omitted octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem active_fourier (k : Fin 15) (e : Fin 64) :
    generatedAxisGlobalOddRoot06PositiveShortQ (Sum.inr (Sum.inl (generatedAxisGlobalOddRoot06ActiveOctad k, e))) =
      generatedAxisGlobalOddRoot06OctadSparseShortQ (Sum.inr (Sum.inl (generatedAxisGlobalOddRoot06ActiveOctad k, e))) := by
  fin_cases k
  · exact generatedAxisGlobalOddRoot06OctadFourier00_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier01_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier02_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier03_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier04_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier05_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier06_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier07_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier08_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier09_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier10_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier11_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier12_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier13_certificate e
  · exact generatedAxisGlobalOddRoot06OctadFourier14_certificate e

/-- The full original positive short packet has exactly the stated sparse coefficients. -/
theorem generatedAxisGlobalOddRoot06PositiveShort_sparse (r : GriessShortIndex) :
    generatedAxisGlobalOddRoot06PositiveShortQ r = generatedAxisGlobalOddRoot06OctadSparseShortQ r := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · exact generatedAxisGlobalOddRoot06OctadPair_certificate s p
  · by_cases ho : ∃ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k = o
    · obtain ⟨k, rfl⟩ := ho
      exact active_fourier k e
    · have h : ∀ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k ≠ o := by
        intro k hk
        exact ho ⟨k, hk⟩
      rw [generatedAxisGlobalOddRoot06Positive_octad_zero o e h,
        generatedAxisGlobalOddRoot06Sparse_octad_zero o e h]
  · exact generatedAxisGlobalOddRoot06OctadOdd_certificate d j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
