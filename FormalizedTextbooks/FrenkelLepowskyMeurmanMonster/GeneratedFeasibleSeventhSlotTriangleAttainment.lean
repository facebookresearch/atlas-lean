/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSeventhSlotTriangleCatalogue
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhExact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2CoordinateTransport
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ShortAction

/-! Attainment half of the first-axis catalogue for source slot 8 (label 6C1) of Höhn–Seysen,
arXiv:2508.01037, Table 3. An explicit original Golay permutation cycles the seventh
triangle and preserves the seventh section octad, hence fixes the entire seventh matrix.
The proved equality of the seventh projected stabilizer with its spatial stabilizer supplies
a genuine whole-axis fixer with this projection. Together with coverage, the entire orbit of
the first positive triangle root axis under the actual seventh H stabilizer is exactly the
three positive triangle root axes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Forward coordinate array of an original Golay permutation cycling the triangle
16 → 17 → 19 → 16 and fixing coordinates 12, 13, 14, 15 and 18. -/
def generatedFeasibleSeventhSlotTriangleForward : Fin 24 → Fin 24 :=
  ![0, 3, 1, 2, 10, 8, 9, 11, 23, 20, 22, 21, 12, 13, 14, 15, 17, 19, 18, 16, 6, 7, 4, 5]

/-- The explicit inverse coordinate array. -/
def generatedFeasibleSeventhSlotTriangleInverse : Fin 24 → Fin 24 :=
  ![0, 2, 3, 1, 22, 23, 20, 21, 5, 6, 4, 7, 12, 13, 14, 15, 19, 16, 18, 17, 9, 11, 10, 8]

/-- The explicit finite arrays define a genuine coordinate permutation. -/
def generatedFeasibleSeventhSlotTrianglePermutation : Equiv.Perm (Fin 24) where
  toFun := generatedFeasibleSeventhSlotTriangleForward
  invFun := generatedFeasibleSeventhSlotTriangleInverse
  left_inv := by
    have h : ∀ i, generatedFeasibleSeventhSlotTriangleInverse
        (generatedFeasibleSeventhSlotTriangleForward i) = i := by
      decide +kernel
    exact h
  right_inv := by
    have h : ∀ i, generatedFeasibleSeventhSlotTriangleForward
        (generatedFeasibleSeventhSlotTriangleInverse i) = i := by
      decide +kernel
    exact h

/-- Generator image labels under the forward permutation, then under its inverse. -/
def generatedFeasibleSeventhSlotTriangleCodeImages : Fin 2 → Fin 12 → Fin 4096 :=
  ![![8, 2, 4, 15, 75, 140, 235, 126, 896, 459, 1186, 2048],
    ![15, 2, 4, 1, 238, 117, 28, 37, 565, 784, 1106, 2048]]

set_option maxHeartbeats 2000000 in
-- The 24 generator-image vectors are checked against the actual encoder.
/-- Both the permutation and its inverse send the twelve original generators into the code. -/
theorem generatedFeasibleSeventhSlotTriangle_code_certificate : ∀ j : Fin 12,
    golayPermute generatedFeasibleSeventhSlotTrianglePermutation (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients
        (generatedFeasibleSeventhSlotTriangleCodeImages 0 j)) ∧
    golayPermute generatedFeasibleSeventhSlotTrianglePermutation⁻¹
        (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients
        (generatedFeasibleSeventhSlotTriangleCodeImages 1 j)) := by
  decide +kernel

private def triangleGolayPermuteLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem triangle_golayPermute_mem (p : Equiv.Perm (Fin 24))
    (hp : ∀ j, golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (triangleGolayPermuteLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  exact golayCode.smul_mem _ (hp j)

/-- The explicit triangle permutation preserves the actual Golay code. -/
def generatedFeasibleSeventhSlotTriangleGolay : golayAutomorphismSubgroup :=
  ⟨generatedFeasibleSeventhSlotTrianglePermutation, by
    have hp : ∀ j, golayPermute generatedFeasibleSeventhSlotTrianglePermutation
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(generatedFeasibleSeventhSlotTriangle_code_certificate j).1]
      exact ⟨_, rfl⟩
    have hq : ∀ j, golayPermute generatedFeasibleSeventhSlotTrianglePermutation⁻¹
        (golayEncoder (Pi.single j 1)) ∈ golayCode := by
      intro j
      rw [(generatedFeasibleSeventhSlotTriangle_code_certificate j).2]
      exact ⟨_, rfl⟩
    intro c
    constructor
    · exact triangle_golayPermute_mem _ hp c
    · intro hc
      have h := triangle_golayPermute_mem _ hq _ hc
      rw [golayPermute_inv] at h
      exact h⟩

/-- The corresponding original Leech isometry. -/
def generatedFeasibleSeventhSlotTriangleIsometry : leechIsomSubgroup :=
  golayPermutationIsometry generatedFeasibleSeventhSlotTriangleGolay

/-- The permutation preserves the genuine seventh section octad on coordinates 12 to 19. -/
theorem generatedFeasibleSeventhSlotTriangle_octad :
    golayPermute generatedFeasibleSeventhSlotTriangleGolay.val
        (golayOctadWord generatedSeventhSectionOctad) =
      golayOctadWord generatedSeventhSectionOctad := by
  have hz : ∀ x y : ZMod 2, (x ≠ 0 ↔ y ≠ 0) → x = y := by decide
  have hr : ∀ i : Fin 24, (12 ≤ (generatedFeasibleSeventhSlotTriangleInverse i).val ∧
      (generatedFeasibleSeventhSlotTriangleInverse i).val < 20 ↔ 12 ≤ i.val ∧ i.val < 20) := by
    decide +kernel
  funext i
  change golayOctadWord generatedSeventhSectionOctad
    (generatedFeasibleSeventhSlotTriangleInverse i) = _
  apply hz
  rw [generatedSeventh_section_octad_support, generatedSeventh_section_octad_support]
  exact hr i

/-- The permutation preserves the literal seventh triangle. -/
theorem generatedFeasibleSeventhSlotTriangle_triangle :
    generatedFeasibleSeventhSlotTriangleGolay • generatedSeventhTriangleCoordinates =
      generatedSeventhTriangleCoordinates := by
  rw [generatedSeventhTriangleCoordinates, Finset.smul_finset_def,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  change ({generatedFeasibleSeventhSlotTriangleForward 16,
    generatedFeasibleSeventhSlotTriangleForward 17,
    generatedFeasibleSeventhSlotTriangleForward 19} : Finset (Fin 24)) = {16, 17, 19}
  decide +kernel

/-- The corresponding original Leech isometry fixes the entire seventh matrix. -/
theorem generatedFeasibleSeventhSlotTriangle_spatial :
    generatedFeasibleSeventhSlotTriangleIsometry ∈ generatedSeventhSpatialStabilizer := by
  change conwayMatrixAction _ (griessConwayEncode generatedSeventhAxis).1 = _
  rw [generatedSeventh_axis_matrix_section_plane_fixed_iff]
  refine ⟨?_, generatedSeventh_permutation_plane_fixed _
    generatedFeasibleSeventhSlotTriangle_triangle⟩
  rw [generatedAxisE8SectionStabilizer_mem]
  exact leechSeventh_coordinate_section_permutation _ _ _
    generatedFeasibleSeventhSlotTriangle_octad

/-- The explicit isometry class lies in the actual projection of the seventh H stabilizer. -/
theorem generatedFeasibleSeventhSlotTriangle_projected :
    QuotientGroup.mk' signsSubgroup generatedFeasibleSeventhSlotTriangleIsometry ∈
      generatedSeventhProjectedAxisStabilizer := by
  rw [generatedSeventh_projected_stabilizer_eq]
  exact ⟨_, generatedFeasibleSeventhSlotTriangle_spatial, rfl⟩

/-- A genuine whole-axis fixer of the counted seventh prototype acts on short labels exactly
as the explicit triangle permutation. -/
theorem generatedFeasibleSeventhSlotTriangle_fixer_exists : ∃ f : localFiberSubgroup,
    localGriessRepresentation f generatedSeventhAxis = generatedSeventhAxis ∧
      ∀ r, griessShortPermutation f.val.2 r =
        griessShortPermutation generatedFeasibleSeventhSlotTriangleIsometry r := by
  obtain ⟨g, hg⟩ := generatedFeasibleSeventhSlotTriangle_projected
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup g.val
  change localFiberIntoH f = g.val at hf
  refine ⟨f, ?_, ?_⟩
  · have h := g.property
    rw [← hf] at h
    exact h
  · intro r
    rw [← localAxis_projection_short_mk, hf]
    change projH g.val = _ at hg
    rw [hg]
    change co1ShortPermutation (QuotientGroup.mk _) r = _
    rw [co1ShortPermutation_mk]

/-- Coordinates of the three positive triangle root vectors at physical coordinate 16. -/
theorem generatedFeasibleSeventhSlot_root_vector_16 (k : Fin 3) :
    griessShortVector (Sum.inl (0, generatedSeventhTargetPair k)) 16 =
      4 / Real.sqrt 8 * (![(1 : ℝ), 1, 0] k) := by
  rw [generatedFeasibleSeventhSlot_pair_vector, (generatedSeventh_pair_coordinate_certificate k).2]
  fin_cases k <;> simp

/-- Coordinates of the three positive triangle root vectors at physical coordinate 17. -/
theorem generatedFeasibleSeventhSlot_root_vector_17 (k : Fin 3) :
    griessShortVector (Sum.inl (0, generatedSeventhTargetPair k)) 17 =
      4 / Real.sqrt 8 * (![(-1 : ℝ), 0, 1] k) := by
  rw [generatedFeasibleSeventhSlot_pair_vector, (generatedSeventh_pair_coordinate_certificate k).2]
  fin_cases k <;> simp

/-- Coordinates of the three positive triangle root vectors at physical coordinate 19. -/
theorem generatedFeasibleSeventhSlot_root_vector_19 (k : Fin 3) :
    griessShortVector (Sum.inl (0, generatedSeventhTargetPair k)) 19 =
      4 / Real.sqrt 8 * (![(0 : ℝ), -1, -1] k) := by
  rw [generatedFeasibleSeventhSlot_pair_vector, (generatedSeventh_pair_coordinate_certificate k).2]
  fin_cases k <;> simp

/-- The explicit permutation sends the first triangle root label to the third. -/
theorem generatedFeasibleSeventhSlotTriangle_label_zero :
    griessShortPermutation (generatedFeasibleSeventhSlotTriangleIsometry)
      (Sum.inl (0, generatedSeventhTargetPair 0)) = Sum.inl (0, generatedSeventhTargetPair 2) := by
  obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_spatial_label _
    generatedFeasibleSeventhSlotTriangle_spatial 0
  rw [hk]
  have hv := griessShortPermutation_vector
    (generatedFeasibleSeventhSlotTriangleIsometry)
    (Sum.inl (0, generatedSeventhTargetPair 0))
  rw [hk] at hv
  have hs17 : (generatedFeasibleSeventhSlotTriangleIsometry).val
      (griessShortVector (Sum.inl (0, generatedSeventhTargetPair 0))) 17 =
      griessShortVector (Sum.inl (0, generatedSeventhTargetPair 0)) 16 := rfl
  have hs19 : (generatedFeasibleSeventhSlotTriangleIsometry).val
      (griessShortVector (Sum.inl (0, generatedSeventhTargetPair 0))) 19 =
      griessShortVector (Sum.inl (0, generatedSeventhTargetPair 0)) 17 := rfl
  fin_cases k
  · exfalso
    rcases hv with hv | hv
    · have h := congrFun hv 19
      rw [hs19, generatedFeasibleSeventhSlot_root_vector_17,
        generatedFeasibleSeventhSlot_root_vector_19] at h
      simp at h
    · have h := congrFun hv 19
      rw [hs19, generatedFeasibleSeventhSlot_root_vector_17, Pi.neg_apply,
        generatedFeasibleSeventhSlot_root_vector_19] at h
      simp at h
  · exfalso
    rcases hv with hv | hv
    · have h := congrFun hv 17
      rw [hs17, generatedFeasibleSeventhSlot_root_vector_16,
        generatedFeasibleSeventhSlot_root_vector_17] at h
      simp at h
    · have h := congrFun hv 17
      rw [hs17, generatedFeasibleSeventhSlot_root_vector_16, Pi.neg_apply,
        generatedFeasibleSeventhSlot_root_vector_17] at h
      simp at h
  · rfl

/-- The explicit permutation sends the third triangle root label to the second. -/
theorem generatedFeasibleSeventhSlotTriangle_label_two :
    griessShortPermutation (generatedFeasibleSeventhSlotTriangleIsometry)
      (Sum.inl (0, generatedSeventhTargetPair 2)) = Sum.inl (0, generatedSeventhTargetPair 1) := by
  obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_spatial_label _
    generatedFeasibleSeventhSlotTriangle_spatial 2
  rw [hk]
  have hv := griessShortPermutation_vector
    (generatedFeasibleSeventhSlotTriangleIsometry)
    (Sum.inl (0, generatedSeventhTargetPair 2))
  rw [hk] at hv
  have hs16 : (generatedFeasibleSeventhSlotTriangleIsometry).val
      (griessShortVector (Sum.inl (0, generatedSeventhTargetPair 2))) 16 =
      griessShortVector (Sum.inl (0, generatedSeventhTargetPair 2)) 19 := rfl
  have hs19 : (generatedFeasibleSeventhSlotTriangleIsometry).val
      (griessShortVector (Sum.inl (0, generatedSeventhTargetPair 2))) 19 =
      griessShortVector (Sum.inl (0, generatedSeventhTargetPair 2)) 17 := rfl
  fin_cases k
  · exfalso
    rcases hv with hv | hv
    · have h := congrFun hv 19
      rw [hs19, generatedFeasibleSeventhSlot_root_vector_17,
        generatedFeasibleSeventhSlot_root_vector_19] at h
      simp at h
    · have h := congrFun hv 19
      rw [hs19, generatedFeasibleSeventhSlot_root_vector_17, Pi.neg_apply,
        generatedFeasibleSeventhSlot_root_vector_19] at h
      simp at h
  · rfl
  · exfalso
    rcases hv with hv | hv
    · have h := congrFun hv 16
      rw [hs16, generatedFeasibleSeventhSlot_root_vector_19,
        generatedFeasibleSeventhSlot_root_vector_16] at h
      simp at h
    · have h := congrFun hv 16
      rw [hs16, generatedFeasibleSeventhSlot_root_vector_19, Pi.neg_apply,
        generatedFeasibleSeventhSlot_root_vector_16] at h
      simp at h

/-- A genuine element of the actual seventh H stabilizer moving the first positive triangle
root axis to the third, and the third to the second. -/
theorem generatedFeasibleSeventhSlot_attainment : ∃ g : H, g ∈ generatedSeventhLocalAxisStabilizer ∧
    rhoLocal g (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 0)) 0) =
      conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 2)) 0 ∧
    rhoLocal g (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 2)) 0) =
      conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 1)) 0 := by
  obtain ⟨f, hfix, hlabel⟩ := generatedFeasibleSeventhSlotTriangle_fixer_exists
  refine ⟨localFiberIntoH f, hfix, ?_, ?_⟩
  · change localGriessRepresentation f _ = _
    rw [generatedFeasibleSeventhSlot_fiber_image f hfix 0, hlabel,
      generatedFeasibleSeventhSlotTriangle_label_zero]
  · change localGriessRepresentation f _ = _
    rw [generatedFeasibleSeventhSlot_fiber_image f hfix 2, hlabel,
      generatedFeasibleSeventhSlotTriangle_label_two]

/-- The actual local vector action restricted to the seventh H stabilizer. -/
noncomputable instance (priority := 2000) generatedFeasibleSeventhSlotStabilizerSmul :
    SMul generatedSeventhLocalAxisStabilizer GriessSpace where
  smul h x := rhoLocal h.val x

/-- The genuine restricted action of the actual seventh H stabilizer. -/
noncomputable instance generatedFeasibleSeventhSlotStabilizerAction :
    MulAction generatedSeventhLocalAxisStabilizer GriessSpace where
  smul h x := rhoLocal h.val x
  one_smul x := by
    change rhoLocal 1 x = x
    rw [rhoLocal.map_one]
    rfl
  mul_smul h k x := by
    change rhoLocal (h.val * k.val) x = rhoLocal h.val (rhoLocal k.val x)
    rw [rhoLocal.map_mul]
    rfl

/-- The three positive triangle root axes. -/
def generatedFeasibleSeventhSlotRootAxis (k : Fin 3) : GriessSpace :=
  conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair k)) 0

/-- The three positive triangle root axes are distinct actual vectors. -/
theorem generatedFeasibleSeventhSlotRootAxis_injective :
    Function.Injective generatedFeasibleSeventhSlotRootAxis := by
  intro k l h
  have he := @generatedAxis_signed_injective (Sum.inl (0, generatedSeventhTargetPair k), 0)
    (Sum.inl (0, generatedSeventhTargetPair l), 0) h
  simp only [Prod.mk.injEq, Sum.inl.injEq, true_and, and_true] at he
  have hc := congrArg griessCoordinatePair he
  rw [(generatedSeventh_pair_coordinate_certificate k).2,
    (generatedSeventh_pair_coordinate_certificate l).2] at hc
  fin_cases k <;> fin_cases l <;> first | rfl | (exfalso; revert hc; decide)

/-- The entire orbit of the first positive triangle root axis under the actual seventh H
stabilizer is exactly the catalogue of the three positive triangle root axes. -/
theorem generatedFeasibleSeventhSlot_root_orbit_eq :
    MulAction.orbit generatedSeventhLocalAxisStabilizer (generatedFeasibleSeventhSlotRootAxis 0) =
      Set.range generatedFeasibleSeventhSlotRootAxis := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_coverage g.val g.property 0
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨g, hg, h0, h2⟩ := generatedFeasibleSeventhSlot_attainment
    fin_cases k
    · exact ⟨1, one_smul _ _⟩
    · refine ⟨⟨g * g, generatedSeventhLocalAxisStabilizer.mul_mem hg hg⟩, ?_⟩
      change rhoLocal (g * g) (generatedFeasibleSeventhSlotRootAxis 0) = _
      rw [map_mul, LinearEquiv.mul_apply]
      change rhoLocal g (rhoLocal g
        (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 0)) 0)) = _
      rw [h0, h2]
      rfl
    · exact ⟨⟨g, hg⟩, h0⟩

/-- The actual first-axis orbit under the seventh H stabilizer has exactly three elements. -/
theorem generatedFeasibleSeventhSlot_root_orbit_card :
    Nat.card (MulAction.orbit generatedSeventhLocalAxisStabilizer
      (generatedFeasibleSeventhSlotRootAxis 0)) = 3 := by
  rw [generatedFeasibleSeventhSlot_root_orbit_eq, Nat.card_range_of_injective
    generatedFeasibleSeventhSlotRootAxis_injective, Nat.card_eq_fintype_card, Fintype.card_fin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
