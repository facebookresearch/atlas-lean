/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadStabilizerKernel

/-! The exact original extraspecial kernel and order of the orthogonal odd A stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000


/-- A whole odd fixer in the original projection kernel fixes the actual orthogonal first axis. -/
theorem generatedFeasibleOddDestination_kernel_first_fixed (h : H)
    (hfix : rhoLocal h (generatedOddAxis) = generatedOddAxis)
    (hproj : projH h = 1) : h ∈ localAxisStabilizer generatedFeasibleOddDestinationPair := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleOddDestinationPair)) =
      Sum.inl (0, generatedFeasibleOddDestinationPair) := by
    have he : co1ShortPermutation (projH h) = griessShortPermutation f.val.2 := by
      rw [← hf]
      exact co1ShortPermutation_mk f.val.2
    rw [hproj, map_one] at he
    rw [← he]
    rfl
  have hh := generatedFeasibleOddDestination_first_fixed f (by rw [hf]; exact hfix) hp
  rwa [hf] at hh


/-- The two actual restricted kernels are equivalent through the original subgroup inclusion. -/
def generatedFeasibleOddDestinationKernelEquiv :
    generatedFeasibleOddDestinationProjection.ker ≃
      (generatedOddLocalAxisProjection).ker := by
  unfold generatedFeasibleOddDestinationProjection generatedOddLocalAxisProjection
  rw [MonoidHom.ker_codRestrict, MonoidHom.ker_codRestrict]
  change (projH.comp
    ((localAxisStabilizer generatedFeasibleOddDestinationPair).subtype.comp
      ((generatedOddLocalAxisStabilizer).comap
        (localAxisStabilizer generatedFeasibleOddDestinationPair).subtype).subtype)).ker ≃
      (projH.comp (generatedOddLocalAxisStabilizer).subtype).ker
  exact generatedFeasibleContainingKernelRestrictionEquiv _ _ projH
    (fun h hh => generatedFeasibleOddDestination_kernel_first_fixed h.val h.property hh)

/-- The entire actual orthogonal restricted Q kernel has exactly 2^12 elements. -/
theorem generatedFeasibleOddDestinationProjection_kernel_card :
    Nat.card generatedFeasibleOddDestinationProjection.ker = 2 ^ 12 := by
  rw [Nat.card_congr generatedFeasibleOddDestinationKernelEquiv]
  exact generatedOddLocalAxisProjection_kernel_card

/-- The actual projected flag group has its separately proved genuine frame-root Co1 order. -/
theorem generatedFeasibleOddDestinationFlag_card :
    Nat.card generatedFeasibleOddDestinationFlag = 41287680 :=
  generatedFeasibleOddFrame_co1_flag_card

/-- The genuine orthogonal odd A stabilizer has exact order 169,114,337,280. -/
theorem generatedFeasibleOddDestinationStabilizer_card :
    Nat.card generatedFeasibleOddDestinationStabilizer = 169114337280 := by
  have h := generatedFeasibleOddDestinationProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    generatedFeasibleOddDestinationProjection_surjective, Subgroup.card_top,
    generatedFeasibleOddDestinationProjection_kernel_card,
    generatedFeasibleOddDestinationFlag_card] at h
  exact h.symm.trans (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
