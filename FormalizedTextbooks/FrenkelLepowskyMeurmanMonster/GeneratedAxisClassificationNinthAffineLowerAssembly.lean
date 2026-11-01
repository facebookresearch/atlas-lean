/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineAlternatingImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineKernelOrbit
public import Mathlib.GroupTheory.Index

/-! A finite group with the exact nine kernel images and two alternating images has
at least92897280 elements. Actual full-axis fixing lifts remain explicit prerequisites. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine group product corresponding to a finite original kernel-image word. -/
def generatedNinthAffineKernelGroupWord {G : Type*} [Group G]
    (u : Fin 9 → G) (w : List (Fin 9)) : G := (w.map u).prod

/-- Entire group-word actions retain the exact full binary-column source evaluation. -/
theorem generatedNinth_affine_kernel_word_action {G : Type*} [Group G]
    [MulAction G (Fin 24 → ZMod 2)] (u : Fin 9 → G)
    (hu : ∀ (j : Fin 9) (v : ℕ),
      u j • monsterCo1GeometryBinaryMaskDecode (n := 24) v =
        monsterCo1GeometryBinaryMaskDecode
          (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j) v))
    (w : List (Fin 9)) (v : ℕ) :
    generatedNinthAffineKernelGroupWord u w • monsterCo1GeometryBinaryMaskDecode (n := 24) v =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineKernelMaskWord w v) := by
  induction w with
  | nil => exact one_smul G _
  | cons j w ih =>
    change (u j * generatedNinthAffineKernelGroupWord u w) •
        monsterCo1GeometryBinaryMaskDecode (n := 24) v =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j)
          (generatedNinthAffineKernelMaskWord w v))
    rw [mul_smul, ih, hu]

/-- Every genuine source word in kernel elements belongs to the whole homomorphism kernel. -/
theorem generatedNinth_affine_kernel_group_word_mem {G : Type*} [Group G]
    (μ : G →* Equiv.Perm (Fin 9)) (u : Fin 9 → G) (hu : ∀ j, μ (u j) = 1)
    (w : List (Fin 9)) : generatedNinthAffineKernelGroupWord u w ∈ μ.ker := by
  change μ (generatedNinthAffineKernelGroupWord u w) = 1
  induction w with
  | nil => exact μ.map_one
  | cons j w ih =>
    change μ (u j * generatedNinthAffineKernelGroupWord u w) = 1
    rw [map_mul, hu, ih, one_mul]

/-- The512 source products in the genuine homomorphism kernel are distinct whole elements. -/
theorem generatedNinth_affine_kernel_card_lower {G : Type*} [Group G] [Finite G]
    [MulAction G (Fin 24 → ZMod 2)] (μ : G →* Equiv.Perm (Fin 9)) (u : Fin 9 → G)
    (hμ : ∀ j, μ (u j) = 1)
    (hu : ∀ (j : Fin 9) (v : ℕ),
      u j • monsterCo1GeometryBinaryMaskDecode (n := 24) v =
        monsterCo1GeometryBinaryMaskDecode
          (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j) v)) :
    512 ≤ Nat.card μ.ker := by
  let f : Fin 512 → μ.ker := fun k =>
    ⟨generatedNinthAffineKernelGroupWord u (generatedNinthAffineKernelSourceWord k),
      generatedNinth_affine_kernel_group_word_mem μ u hμ _⟩
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg (fun g : μ.ker =>
      g.val • monsterCo1GeometryBinaryMaskDecode (n := 24) 16) h
    change generatedNinthAffineKernelGroupWord u (generatedNinthAffineKernelSourceWord a) •
        monsterCo1GeometryBinaryMaskDecode (n := 24) 16 =
      generatedNinthAffineKernelGroupWord u (generatedNinthAffineKernelSourceWord b) •
        monsterCo1GeometryBinaryMaskDecode (n := 24) 16 at he
    rw [generatedNinth_affine_kernel_word_action u hu,
      generatedNinth_affine_kernel_word_action u hu,
      generatedNinth_affine_kernel_orbit_source, generatedNinth_affine_kernel_orbit_source] at he
    apply generatedNinth_affine_kernel_orbit_image_injective
    exact sixthFrameOrbitMaskDecode_injective _ _
      (generatedNinth_affine_kernel_orbit_lookup a).2
      (generatedNinth_affine_kernel_orbit_lookup b).2 he
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The two complete original permutation images force an image of size at least181440. -/
theorem generatedNinth_affine_permutation_image_card_lower {G : Type*} [Group G]
    (μ : G →* Equiv.Perm (Fin 9)) (v : Fin 2 → G)
    (hv : ∀ j, μ (v j) = generatedNinthAffineAlternatingPermutation j) :
    181440 ≤ Nat.card μ.range := by
  have hl : Subgroup.closure (Set.range generatedNinthAffineAlternatingPermutation) ≤
      μ.range := by
    apply (Subgroup.closure_le _).mpr
    rintro p ⟨j, rfl⟩
    exact ⟨v j, hv j⟩
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hl)
    (Subgroup.inclusion_injective hl)
  rwa [generatedNinth_affine_alternating_image_card] at hc

/-- Actual lifts of the eleven stated complete images force the required full subgroup size. -/
theorem generatedNinth_affine_full_group_card_lower {G : Type*} [Group G] [Finite G]
    [MulAction G (Fin 24 → ZMod 2)] (μ : G →* Equiv.Perm (Fin 9))
    (u : Fin 9 → G) (v : Fin 2 → G)
    (hμ : ∀ j, μ (u j) = 1)
    (hu : ∀ (j : Fin 9) (w : ℕ),
      u j • monsterCo1GeometryBinaryMaskDecode (n := 24) w =
        monsterCo1GeometryBinaryMaskDecode
          (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j) w))
    (hv : ∀ j, μ (v j) = generatedNinthAffineAlternatingPermutation j) :
    92897280 ≤ Nat.card G := by
  have hk := generatedNinth_affine_kernel_card_lower μ u hμ hu
  have hi := generatedNinth_affine_permutation_image_card_lower μ v hv
  have hc := μ.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  calc
    92897280 = 512 * 181440 := by decide
    _ ≤ Nat.card μ.ker * Nat.card μ.range := Nat.mul_le_mul hk hi
    _ = Nat.card G := hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
