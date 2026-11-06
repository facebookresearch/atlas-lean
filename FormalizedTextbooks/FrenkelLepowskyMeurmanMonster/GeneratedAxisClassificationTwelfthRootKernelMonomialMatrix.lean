/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelMonomialWord

/-! Genuine signed original monomial words act by one sign on the entire physical E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every vanishing sign label has its original all-ones bit zero. -/
theorem generatedTwelfth_root_kernel_sign_label_low : ∀ a : Fin 32,
    (generatedTwelfthRootKernelSignLabel a).val < 2048 := by
  decide +kernel

/-- The original all-ones code bit supplies the common actual root orientation. -/
def generatedTwelfthRootKernelTotalLabel (b : Bool) (a : Fin 32) : Fin 4096 :=
  ⟨(generatedTwelfthRootKernelSignLabel a).val + if b then 2048 else 0, by
    have ha := generatedTwelfth_root_kernel_sign_label_low a
    split_ifs <;> omega⟩

/-- All sixty-four original full sign codes are distinct genuine code labels. -/
theorem generatedTwelfth_root_kernel_total_label_injective : ∀ b c : Bool, ∀ a d : Fin 32,
    generatedTwelfthRootKernelTotalLabel b a = generatedTwelfthRootKernelTotalLabel c d →
      b = c ∧ a = d := by
  decide +kernel

/-- Every actual physical octad sign is exactly the one original all-ones bit. -/
theorem generatedTwelfth_root_kernel_total_code_octad : ∀ b : Bool, ∀ a : Fin 32, ∀ i : Fin 8,
    (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel b a)).val
      (generatedTwelfthRootKernelOctadCoordinate i) = if b then 1 else 0 := by
  decide +kernel

/-- The entire actual signed permutation is a product of original genuine lattice isometries. -/
def generatedTwelfthRootKernelMonomial (b : Bool) (a : Fin 32) (p : Fin 16) :
    leechIsomSubgroup :=
  golaySignIsometry (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel b a)) *
    golayPermutationIsometry (generatedTwelfthRootKernelPermutation p)

/-- Every physical coordinate retains the original full word pullback and actual Golay sign. -/
theorem generatedTwelfth_root_kernel_monomial_apply (b : Bool) (a : Fin 32) (p : Fin 16)
    (v : Fin 24 → ℝ) (i : Fin 24) :
    (generatedTwelfthRootKernelMonomial b a p).val v i =
      qSign ((sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel b a)).val i) *
        v (generatedTwelfthRootKernelPermutationBackward p i) := by
  change golayRealSign _ (golayRealPermute _ v) i = _
  rw [golayRealSign_apply, golayRealPermute_apply,
    generatedTwelfth_root_kernel_permutation_backward]

/-- The true original permutation word fixes every physical inserted section vector. -/
theorem generatedTwelfth_root_kernel_permute_insertion (p : Fin 16) (v : Fin 8 → ℝ) :
    golayRealPermute (generatedTwelfthRootKernelPermutation p).val
      (generatedTwelfthSectionInsertReal v) = generatedTwelfthSectionInsertReal v := by
  funext i
  rw [golayRealPermute_apply, generatedTwelfth_root_kernel_permutation_backward]
  fin_cases p <;> fin_cases i <;> rfl

/-- Outside the original eight octad coordinates the entire actual insertion is zero. -/
theorem generatedTwelfth_root_kernel_insertion_outside (v : Fin 8 → ℝ) (i : Fin 24)
    (hi : ∀ j : Fin 8, generatedTwelfthRootKernelOctadCoordinate j ≠ i) :
    generatedTwelfthSectionInsertReal v i = 0 := by
  fin_cases i <;> try rfl
  all_goals exfalso
  all_goals
    first
    | exact hi 0 rfl
    | exact hi 1 rfl
    | exact hi 2 rfl
    | exact hi 3 rfl
    | exact hi 4 rfl
    | exact hi 5 rfl
    | exact hi 6 rfl
    | exact hi 7 rfl

/-- Every genuine original full sign code has one scalar sign on all physical section vectors. -/
theorem generatedTwelfth_root_kernel_sign_insertion (b : Bool) (a : Fin 32) (v : Fin 8 → ℝ) :
    golayRealSign (sourceGeneratedSignCode (generatedTwelfthRootKernelTotalLabel b a)).val
      (generatedTwelfthSectionInsertReal v) =
        qSign (if b then 1 else 0) • generatedTwelfthSectionInsertReal v := by
  funext i
  by_cases hi : ∃ j : Fin 8, generatedTwelfthRootKernelOctadCoordinate j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [golayRealSign_apply, generatedTwelfth_root_kernel_total_code_octad]
    rfl
  · have hz := generatedTwelfth_root_kernel_insertion_outside v i
      (by simpa only [not_exists] using hi)
    rw [golayRealSign_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hz, mul_zero]

/-- All original signed monomial words act by the same scalar on the whole actual E8 section. -/
theorem generatedTwelfth_root_kernel_monomial_insertion (b : Bool) (a : Fin 32) (p : Fin 16)
    (v : Fin 8 → ℝ) :
    (generatedTwelfthRootKernelMonomial b a p).val (generatedTwelfthSectionInsertReal v) =
      qSign (if b then 1 else 0) • generatedTwelfthSectionInsertReal v := by
  change golayRealSign _ (golayRealPermute _ (generatedTwelfthSectionInsertReal v)) = _
  rw [generatedTwelfth_root_kernel_permute_insertion,
    generatedTwelfth_root_kernel_sign_insertion]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
