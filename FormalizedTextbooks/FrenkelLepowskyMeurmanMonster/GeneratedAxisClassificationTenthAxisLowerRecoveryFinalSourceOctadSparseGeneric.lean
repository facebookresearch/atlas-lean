/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceOctadSparseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateIncomingGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Bounded signed source-slot lookup and symbolic triality sum transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Balanced lookup retains a zero default at every missing candidate octad address. -/
def generatedTenthFinalSourceOctadSparseWord (o : Fin 759) : ℕ :=
  (generatedTenthFinalSourceOctadSparseTree.lookup generatedTenthFinalSourceOctadSparseKey
    o.val).getD 0

/-- Four bits encode the number of active original source slots. -/
def generatedTenthFinalSourceOctadSparseCount (word : ℕ) : ℕ := (word >>> 10) % 16

/-- Every source slot retains its complete original six-bit coordinate. -/
def generatedTenthFinalSourceOctadSparseSlot (word : ℕ) (s : Fin 15) : Fin 64 :=
  ⟨(word >>> (14 + 14 * s.val)) % 64, Nat.mod_lt _ (by decide)⟩

/-- Original signed eight-bit coefficients are zero outside the retained active slots. -/
def generatedTenthFinalSourceOctadSparseValue (word : ℕ) (s : Fin 15) : ℤ :=
  if s.val < generatedTenthFinalSourceOctadSparseCount word then
    (((word >>> (20 + 14 * s.val)) % 256 : ℕ) : ℤ) - 128
  else 0

/-- Every original coordinate is reconstructed from all fifteen bounded signed slots. -/
def generatedTenthFinalSourceOctadSparseCoefficientWord (word : ℕ) (f : Fin 64) : ℤ :=
  ∑ s : Fin 15, if generatedTenthFinalSourceOctadSparseSlot word s = f then
    generatedTenthFinalSourceOctadSparseValue word s else 0

/-- The balanced record determines the full source vector, including every zero coordinate. -/
def generatedTenthFinalSourceOctadSparseCoefficient (o : Fin 759) (f : Fin 64) : ℤ :=
  generatedTenthFinalSourceOctadSparseCoefficientWord
    (generatedTenthFinalSourceOctadSparseWord o) f

/-- Triality uses at most fifteen signed original source terms from one fixed record. -/
def generatedTenthFinalSourceOctadSparseSumWord (word : ℕ) (e : Fin 64) : ℤ :=
  ∑ s : Fin 15, trialityIntegerMatrix e (generatedTenthFinalSourceOctadSparseSlot word s) *
    generatedTenthFinalSourceOctadSparseValue word s

/-- Zero source slots are skipped before any triality matrix entry is evaluated. -/
def generatedTenthFinalSourceOctadSparseShortSumWord (word : ℕ) (e : Fin 64) : ℤ :=
  ∑ s : Fin 15, if generatedTenthFinalSourceOctadSparseValue word s = 0 then 0 else
    generatedTenthFinalSourceOctadSparseValue word s *
      trialityIntegerMatrix e (generatedTenthFinalSourceOctadSparseSlot word s)

/-- The exact bounded sum retains original row orientation and skips zero source slots. -/
def generatedTenthFinalSourceOctadSparseSum (o : Fin 759) (e : Fin 64) : ℤ :=
  generatedTenthFinalSourceOctadSparseShortSumWord (generatedTenthFinalSourceOctadSparseWord o) e

/-- Skipping zero slots preserves the complete ordinary signed fifteen-slot sum. -/
theorem generatedTenth_final_source_octad_sparse_short_word_eq (word : ℕ) (e : Fin 64) :
    generatedTenthFinalSourceOctadSparseShortSumWord word e =
      generatedTenthFinalSourceOctadSparseSumWord word e := by
  unfold generatedTenthFinalSourceOctadSparseShortSumWord
    generatedTenthFinalSourceOctadSparseSumWord
  apply Finset.sum_congr rfl
  intro s _
  by_cases hz : generatedTenthFinalSourceOctadSparseValue word s = 0
  · simp only [hz, ite_true, mul_zero]
  · simp only [hz, ite_false, mul_comm]

/-- The literal count field always retains at most fifteen active source terms. -/
theorem generatedTenth_final_source_octad_sparse_count_le (word : ℕ) :
    generatedTenthFinalSourceOctadSparseCount word ≤ 15 := by
  unfold generatedTenthFinalSourceOctadSparseCount
  omega

/-- Function-valued finite sums avoid reducing the concrete matrix carrier during algebra. -/
private theorem sparse_slot_sum (a : Fin 64 → ℤ) (slot : Fin 15 → Fin 64)
    (value : Fin 15 → ℤ) :
    (∑ f : Fin 64, a f * (∑ s : Fin 15, if slot s = f then value s else 0)) =
      ∑ s : Fin 15, a (slot s) * value s := by
  classical
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Finite-sum interchange collapses the complete original triality source coordinate sum. -/
theorem generatedTenth_final_source_octad_sparse_word_sum (word : ℕ) (e : Fin 64) :
    (∑ f : Fin 64, trialityIntegerMatrix e f *
      generatedTenthFinalSourceOctadSparseCoefficientWord word f) =
        generatedTenthFinalSourceOctadSparseSumWord word e := by
  exact sparse_slot_sum (fun f => trialityIntegerMatrix e f)
    (generatedTenthFinalSourceOctadSparseSlot word)
    (generatedTenthFinalSourceOctadSparseValue word)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
