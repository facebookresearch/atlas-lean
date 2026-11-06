/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelMonomialMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Distinct genuine original signed words give 1024 actual section root-action kernel elements. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original pointwise-octad words lie in the full genuine selected-octad permutation group. -/
theorem generatedTwelfth_root_kernel_permutation_selected (p : Fin 16) :
    generatedTwelfthRootKernelPermutation p ∈ generatedFifthSelectedOctadSubgroup := by
  have hl (l : Fin 5 × Bool) :
      generatedTwelfthRootKernelPermutationLetter l ∈ generatedFifthSelectedOctadSubgroup := by
    rcases l with ⟨g, b⟩
    cases b
    · exact generatedFifthSelectedOctad_generator_mem g
    · exact generatedFifthSelectedOctadSubgroup.inv_mem
        (generatedFifthSelectedOctad_generator_mem g)
  have hw (w : List (Fin 5 × Bool)) :
      (w.map generatedTwelfthRootKernelPermutationLetter).prod ∈
        generatedFifthSelectedOctadSubgroup := by
    induction w with
    | nil => exact generatedFifthSelectedOctadSubgroup.one_mem
    | cons l w ih => exact generatedFifthSelectedOctadSubgroup.mul_mem (hl l) ih
  exact hw (generatedTwelfthRootKernelPermutationWord p)

/-- Every actual signed kernel word preserves the entire original integral E8 section. -/
theorem generatedTwelfth_root_kernel_monomial_section (b : Bool) (a : Fin 32) (p : Fin 16) :
    generatedTwelfthRootKernelMonomial b a p ∈ leechSeventhE8SectionGroup := by
  apply generatedAxisE8FrameSystemSectionGroup.mul_mem
  · rw [generatedAxisE8SectionStabilizer_mem]
    exact generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ _)
  · rw [generatedAxisE8SectionStabilizer_mem, generatedAxisE8_permutation_image]
    exact congrArg generatedAxisE8CoordinateSection
      ((generatedFifthSelectedOctadSubgroup_mem _).mp
        (generatedTwelfth_root_kernel_permutation_selected p))

/-- Every full original root vector has exactly the one common actual signed-word orientation. -/
theorem generatedTwelfth_root_kernel_monomial_root_real (b : Bool) (a : Fin 32) (p : Fin 16)
    (r : Fin 120) :
    (generatedTwelfthRootKernelMonomial b a p).val (leechSeventhE8RealRoot r) =
      qSign (if b then 1 else 0) • leechSeventhE8RealRoot r := by
  have h := generatedTwelfth_root_kernel_monomial_insertion b a p
    (fun i => (leechSeventhE8RootLocal r i : ℝ))
  rw [generatedTwelfthSection_root_insert, map_smul, smul_comm] at h
  exact (smul_right_injective _ (by positivity : Real.sqrt (8 : ℝ) ≠ 0)) h

/-- All complete original signed monomial words have genuine integral root orientations. -/
theorem generatedTwelfth_root_kernel_monomial_root_integral (b : Bool) (a : Fin 32) (p : Fin 16)
    (r : Fin 120) :
    leechIntegralAction (generatedTwelfthRootKernelMonomial b a p) (leechSeventhE8Root r) =
        leechSeventhE8Root r ∨
      leechIntegralAction (generatedTwelfthRootKernelMonomial b a p) (leechSeventhE8Root r) =
        -leechSeventhE8Root r := by
  have h := generatedTwelfth_root_kernel_monomial_root_real b a p r
  cases b
  · left
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    simpa [qSign, leechSeventhE8RealRoot] using h
  · right
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [Submodule.coe_neg, map_neg, leechIntegralAction_embedding]
    simpa [qSign, leechSeventhE8RealRoot] using h

/-- The full actual original word belongs to the genuine 120-root-line action kernel. -/
theorem generatedTwelfth_root_kernel_monomial_root_action (b : Bool) (a : Fin 32) (p : Fin 16) :
    generatedTwelfthRootAction
        ⟨generatedTwelfthRootKernelMonomial b a p,
          generatedTwelfth_root_kernel_monomial_section b a p⟩ = 1 := by
  apply Equiv.ext
  intro r
  change leechSeventhE8SectionRootIndex _ r = r
  apply leechSeventhE8RootLabel_injective
  rw [leechSeventhE8SectionRootIndex_label]
  apply griessShortClass_injective
  rw [griessShortPermutation_class, leechSeventhE8Root_label_class]
  change leechReduction
    (leechIntegralAction (generatedTwelfthRootKernelMonomial b a p) (leechSeventhE8Root r)) = _
  rcases generatedTwelfth_root_kernel_monomial_root_integral b a p r with h | h
  · rw [h]
  · rw [h, leechReduction_neg]

/-- The complete original physical sign-code parametrization retains every true source label. -/
theorem generatedTwelfth_root_kernel_source_sign_injective :
    Function.Injective sourceGeneratedSignCode := by
  intro d e h
  apply golayLabelCoefficients_injective
  apply golayEncoder_injective
  exact congrArg Subtype.val h

/-- Distinct original signed-word parameters are distinct actual full lattice isometries. -/
theorem generatedTwelfth_root_kernel_monomial_injective :
    Function.Injective (fun x : Bool × Fin 32 × Fin 16 =>
      generatedTwelfthRootKernelMonomial x.1 x.2.1 x.2.2) := by
  rintro ⟨b, a, p⟩ ⟨c, d, q⟩ h
  have hp := @golayMonomialPair_injective
    (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel b a),
      generatedTwelfthRootKernelPermutation p)
    (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel c d),
      generatedTwelfthRootKernelPermutation q) h
  have hc := congrArg Prod.fst hp
  have hperm := congrArg Prod.snd hp
  have hlabel := generatedTwelfth_root_kernel_source_sign_injective hc
  have hba := generatedTwelfth_root_kernel_total_label_injective b c a d hlabel
  have hpq : p = q := by
    apply generatedTwelfth_root_kernel_permutation_distinct p q
    intro i
    have he := congrArg (fun v : golayAutomorphismSubgroup => v.val i) hperm
    rw [generatedTwelfth_root_kernel_permutation_actual,
      generatedTwelfth_root_kernel_permutation_actual] at he
    exact he
  exact Prod.ext hba.1 (Prod.ext hba.2 hpq)

/-- All 1024 actual original signed monomial words are elements of the full root-action kernel. -/
def generatedTwelfthRootKernelEnumeration (x : Bool × Fin 32 × Fin 16) :
    generatedTwelfthRootAction.ker :=
  ⟨⟨generatedTwelfthRootKernelMonomial x.1 x.2.1 x.2.2,
    generatedTwelfth_root_kernel_monomial_section _ _ _⟩,
      generatedTwelfth_root_kernel_monomial_root_action _ _ _⟩

/-- The actual kernel enumeration is injective as a complete original lattice-word construction. -/
theorem generatedTwelfth_root_kernel_enumeration_injective :
    Function.Injective generatedTwelfthRootKernelEnumeration := by
  intro x y h
  apply generatedTwelfth_root_kernel_monomial_injective
  exact congrArg (fun g : generatedTwelfthRootAction.ker => g.val.val) h

/-- The genuine full section root-action kernel has at least 1024 actual elements. -/
theorem generatedTwelfth_root_action_kernel_lower :
    1024 ≤ Nat.card generatedTwelfthRootAction.ker := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Nat.card_le_card_of_injective generatedTwelfthRootKernelEnumeration
    generatedTwelfth_root_kernel_enumeration_injective
  have hsize : Nat.card (Bool × Fin 32 × Fin 16) = 1024 := by
    norm_num [Nat.card_eq_fintype_card]
  rw [hsize] at h
  exact h

/-- Genuine kernel words bound the full original section root-line action image. -/
theorem generatedTwelfth_root_action_image_upper :
    Nat.card generatedTwelfthRootAction.range ≤ 174182400 := by
  have h := generatedTwelfthRootAction.ker.card_mul_index
  rw [Subgroup.index_ker, generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at h
  have hl := Nat.mul_le_mul_right (Nat.card generatedTwelfthRootAction.range)
    generatedTwelfth_root_action_kernel_lower
  rw [h] at hl
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
