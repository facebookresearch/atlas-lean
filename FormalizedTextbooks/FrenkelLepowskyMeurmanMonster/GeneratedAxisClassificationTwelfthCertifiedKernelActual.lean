/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedKernelCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixLifts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Original kernel enumeration is represented by complete products of the nine genuine candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- A genuine physical candidate for one original monomial letter. -/
def generatedTwelfthCertifiedKernelLetter (g : Fin 9) : leechIsomSubgroup :=
  generatedTwelfthCertifiedSpatial (generatedTwelfthCertifiedKernelIndex g)

/-- The entire actual product of a complete original monomial candidate word. -/
def generatedTwelfthCertifiedKernelWord (w : List (Fin 9)) : leechIsomSubgroup :=
  (w.map generatedTwelfthCertifiedKernelLetter).prod

/-- Each complete candidate physical letter acts by its exact signed original pullback. -/
theorem generatedTwelfth_certified_kernel_letter_apply (g : Fin 9)
    (v : Fin 24 → ℝ) (i : Fin 24) :
    (generatedTwelfthCertifiedKernelLetter g).val v i =
      qSign (generatedTwelfthCertifiedKernelLetterSign g i) *
        v (generatedTwelfthCertifiedKernelLetterBackward g i) := by
  have hm : leechIsomMatrix (generatedTwelfthCertifiedKernelLetter g) =
      fun i j => qSign (generatedTwelfthCertifiedKernelLetterSign g i) *
        if generatedTwelfthCertifiedKernelLetterBackward g i = j then 1 else 0 := by
    change leechIsomMatrix (generatedTwelfthCertifiedSpatial
      (generatedTwelfthCertifiedKernelIndex g)) = _
    rw [generatedTwelfth_certified_spatial_matrix]
    ext j k
    change (generatedTwelfthCertifiedDenominator
      (generatedTwelfthCertifiedKernelIndex g) : ℝ)⁻¹ *
        (generatedTwelfthCertifiedNumerator (generatedTwelfthCertifiedKernelIndex g) j k : ℝ) = _
    rw [generatedTwelfth_certified_kernel_denominators,
      generatedTwelfth_certified_kernel_matrix_entries]
    simp only [Nat.cast_one, inv_one, one_mul, Int.cast_mul,
      Int.cast_ite, Int.cast_one, Int.cast_zero, nortonUIntegerSign_real]
  rw [← leechIsomMatrix_mulVec, hm]
  simp [Matrix.mulVec, dotProduct]

/-- Every entire actual monomial word acts by its complete original signed pullback. -/
theorem generatedTwelfth_certified_kernel_word_apply (w : List (Fin 9))
    (v : Fin 24 → ℝ) (i : Fin 24) :
    (generatedTwelfthCertifiedKernelWord w).val v i =
      qSign (generatedTwelfthCertifiedKernelWordData w i).1 *
        v (generatedTwelfthCertifiedKernelWordData w i).2 := by
  induction w generalizing v i with
  | nil => simp [generatedTwelfthCertifiedKernelWord, generatedTwelfthCertifiedKernelWordData]
  | cons g w ih =>
    change (generatedTwelfthCertifiedKernelLetter g).val
      ((generatedTwelfthCertifiedKernelWord w).val v) i = _
    rw [generatedTwelfth_certified_kernel_letter_apply, ih]
    simp only [generatedTwelfthCertifiedKernelWordData, qSign_add]
    ring

/-- All original positive root-kernel words are exactly products of genuine compact candidates. -/
theorem generatedTwelfth_certified_kernel_monomial (a : Fin 32) (p : Fin 16) :
    generatedTwelfthCertifiedKernelWord (generatedTwelfthCertifiedKernelSignWord a) *
      generatedTwelfthCertifiedKernelWord (generatedTwelfthCertifiedKernelPermutationWord p) =
        generatedTwelfthRootKernelMonomial false a p := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  funext i
  change (generatedTwelfthCertifiedKernelWord (generatedTwelfthCertifiedKernelSignWord a)).val
    ((generatedTwelfthCertifiedKernelWord
      (generatedTwelfthCertifiedKernelPermutationWord p)).val v) i = _
  rw [generatedTwelfth_certified_kernel_word_apply, generatedTwelfth_certified_kernel_sign_words]
  simp only [Prod.fst, Prod.snd]
  rw [generatedTwelfth_certified_kernel_word_apply,
    generatedTwelfth_certified_kernel_permutation_words]
  simp only [Prod.fst, Prod.snd, qSign_zero, one_mul]
  exact (generatedTwelfth_root_kernel_monomial_apply false a p v i).symm

/-- The original all-ones sign changes each entire positive monomial by the genuine scalar minus sign. -/
theorem generatedTwelfth_certified_kernel_monomial_negative (a : Fin 32) (p : Fin 16)
    (v : Fin 24 → ℝ) :
    (generatedTwelfthRootKernelMonomial true a p).val v =
      -((generatedTwelfthRootKernelMonomial false a p).val v) := by
  funext i
  change (generatedTwelfthRootKernelMonomial true a p).val v i =
    -((generatedTwelfthRootKernelMonomial false a p).val v i)
  rw [generatedTwelfth_root_kernel_monomial_apply,
    generatedTwelfth_root_kernel_monomial_apply, generatedTwelfth_certified_kernel_total_sign,
    qSign_add]
  simp only [qSign_one, Pi.neg_apply]
  ring

/-- Both original common orientations of the complete monomial word have the same genuine Conway class. -/
theorem generatedTwelfth_certified_kernel_monomial_projection_sign (a : Fin 32) (p : Fin 16) :
    (QuotientGroup.mk (generatedTwelfthRootKernelMonomial true a p) : Co1) =
      QuotientGroup.mk (generatedTwelfthRootKernelMonomial false a p) := by
  have hsign : generatedTwelfthRootKernelMonomial true a p *
      (generatedTwelfthRootKernelMonomial false a p)⁻¹ ∈ signsSubgroup := by
    right
    intro v
    change (generatedTwelfthRootKernelMonomial true a p).val
      ((generatedTwelfthRootKernelMonomial false a p).val.symm v) = -v
    rw [generatedTwelfth_certified_kernel_monomial_negative, LinearEquiv.apply_symm_apply]
  have h := (QuotientGroup.eq_one_iff _).mpr hsign
  change (QuotientGroup.mk' signsSubgroup)
    (generatedTwelfthRootKernelMonomial true a p *
      (generatedTwelfthRootKernelMonomial false a p)⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- Attaining the twelve genuine candidate Conway values attains all 1024 original kernel orientations. -/
theorem generatedTwelfth_certified_kernel_projection_mem (P : Subgroup Co1)
    (hcandidate : ∀ g : Fin 12,
      (QuotientGroup.mk (generatedTwelfthCertifiedSpatial g) : Co1) ∈ P)
    (b : Bool) (a : Fin 32) (p : Fin 16) :
    (QuotientGroup.mk (generatedTwelfthRootKernelMonomial b a p) : Co1) ∈ P := by
  have hw (w : List (Fin 9)) :
      (QuotientGroup.mk (generatedTwelfthCertifiedKernelWord w) : Co1) ∈ P := by
    induction w with
    | nil => simpa only [generatedTwelfthCertifiedKernelWord, List.map_nil,
        List.prod_nil, QuotientGroup.mk_one] using P.one_mem
    | cons g w ih =>
      change (QuotientGroup.mk' signsSubgroup)
        (generatedTwelfthCertifiedKernelLetter g * generatedTwelfthCertifiedKernelWord w) ∈ P
      rw [map_mul]
      exact P.mul_mem (hcandidate (generatedTwelfthCertifiedKernelIndex g)) ih
  have hpositive : (QuotientGroup.mk (generatedTwelfthRootKernelMonomial false a p) : Co1) ∈ P := by
    rw [← generatedTwelfth_certified_kernel_monomial]
    change (QuotientGroup.mk' signsSubgroup)
      (generatedTwelfthCertifiedKernelWord (generatedTwelfthCertifiedKernelSignWord a) *
        generatedTwelfthCertifiedKernelWord (generatedTwelfthCertifiedKernelPermutationWord p)) ∈ P
    rw [map_mul]
    exact P.mul_mem (hw _) (hw _)
  cases b
  · exact hpositive
  · rw [generatedTwelfth_certified_kernel_monomial_projection_sign]
    exact hpositive

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
