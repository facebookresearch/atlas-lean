/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadStabilizerProjection

/-! The exact original extraspecial kernel and order of the incident octad A stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000


/-- A whole octad fixer in the original projection kernel fixes the actual incident first axis. -/
theorem generatedFeasibleContainingIncident_kernel_first_fixed (h : H)
    (hfix : rhoLocal h (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0)
    (hproj : projH h = 1) : h ∈ localAxisStabilizer generatedFeasibleContainingIncidentPair := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair) := by
    have he : co1ShortPermutation (projH h) = griessShortPermutation f.val.2 := by
      rw [← hf]
      exact co1ShortPermutation_mk f.val.2
    rw [hproj, map_one] at he
    rw [← he]
    rfl
  have hh := generatedFeasibleContainingIncident_first_fixed f (by rw [hf]; exact hfix) hp
  rwa [hf] at hh


/-- Restricting a projection to a subgroup preserves its kernel when every old kernel element
already belongs to that subgroup. This is applied below to the original whole-octad fixers. -/
def generatedFeasibleContainingKernelRestrictionEquiv
    {Γ Δ : Type*} [Group Γ] [Group Δ] (A B : Subgroup Γ) (f : Γ →* Δ)
    (hkernel : ∀ b : B, f b.val = 1 → b.val ∈ A) :
    (f.comp (A.subtype.comp (B.comap A.subtype).subtype)).ker ≃
      (f.comp B.subtype).ker where
  toFun x := ⟨⟨x.val.val.val, x.val.property⟩, x.property⟩
  invFun x := ⟨⟨⟨x.val.val, hkernel x.val x.property⟩, x.val.property⟩, x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The two actual restricted kernels are equivalent through the original subgroup inclusion. -/
def generatedFeasibleContainingIncidentKernelEquiv :
    generatedFeasibleContainingIncidentProjection.ker ≃
      (generatedOctadLocalAxisProjection 0 0).ker := by
  unfold generatedFeasibleContainingIncidentProjection generatedOctadLocalAxisProjection
  rw [MonoidHom.ker_codRestrict, MonoidHom.ker_codRestrict]
  change (projH.comp
    ((localAxisStabilizer generatedFeasibleContainingIncidentPair).subtype.comp
      ((generatedOctadLocalAxisStabilizer 0 0).comap
        (localAxisStabilizer generatedFeasibleContainingIncidentPair).subtype).subtype)).ker ≃
      (projH.comp (generatedOctadLocalAxisStabilizer 0 0).subtype).ker
  exact generatedFeasibleContainingKernelRestrictionEquiv _ _ projH
    (fun h hh => generatedFeasibleContainingIncident_kernel_first_fixed h.val h.property hh)

/-- The entire actual incident restricted Q kernel has exactly 2^17 elements. -/
theorem generatedFeasibleContainingIncidentProjection_kernel_card :
    Nat.card generatedFeasibleContainingIncidentProjection.ker = 2 ^ 17 := by
  rw [Nat.card_congr generatedFeasibleContainingIncidentKernelEquiv]
  exact generatedOctadLocalAxisProjection_kernel_card 0 0

/-- The actual fixed incident short line belongs to the original coordinate E8 section. -/
theorem generatedFeasibleContainingIncident_short_mem :
    Sum.inl (0, generatedFeasibleContainingIncidentPair) ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
  rw [generatedAxisE8ShortLines_coordinate_mem]
  apply (generatedAxis_triality_octad_support_iff generatedOctadBasisOctad 0 0 _).mp
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
    (Sum.inl (0, generatedFeasibleContainingIncidentPair)) ≠ 0
  rw [generatedFeasibleContainingIncident_first_coordinate]
  norm_num

/-- The actual projected incident flag group has its previously proved original Co1 order. -/
theorem generatedFeasibleContainingIncidentFlag_card :
    Nat.card generatedFeasibleContainingIncidentFlag = 743178240 :=
  generatedAxisE8Co1ShortFlagStabilizer_card _ _ generatedFeasibleContainingIncident_short_mem

/-- The genuine incident octad A stabilizer has exact order 97,409,858,273,280. -/
theorem generatedFeasibleContainingIncidentStabilizer_card :
    Nat.card generatedFeasibleContainingIncidentStabilizer = 97409858273280 := by
  have h := generatedFeasibleContainingIncidentProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    generatedFeasibleContainingIncidentProjection_surjective, Subgroup.card_top,
    generatedFeasibleContainingIncidentProjection_kernel_card,
    generatedFeasibleContainingIncidentFlag_card] at h
  exact h.symm.trans (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
