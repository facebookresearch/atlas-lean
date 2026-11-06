/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZCubic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFrobeniusReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairOdd

/-! Reduction of actual XYZ multiplication to the mixed XYZ cubic coefficients
and octad multiplication. All repeated-color cubic coefficients vanish by the
concrete Conway product and spin parity. The remaining hypotheses explicitly
state the two source computations still required, rather than assuming full
triality product preservation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

lemma xyzReduction_cubic_cycle (x y z : GriessSpace) :
    griessForm (griessProd x y) z = griessForm (griessProd y z) x := by
  rw [griessProd_frobenius, griessForm_swap]

lemma xyzReduction_cubic_swap (x y z : GriessSpace) :
    griessForm (griessProd x y) z = griessForm (griessProd y x) z := by
  rw [griessProd_comm]

/-- Every repeated-color XYZ source cubic coefficient is zero. -/
theorem trialityXYZ_cubic_repeated_zero (s t u : Fin 3) (k l m : Fin 49152)
    (h : s = t ∨ t = u ∨ u = s) :
    griessForm (griessProd (trialityXYZBasis s k) (trialityXYZBasis t l))
      (trialityXYZBasis u m) = 0 := by
  fin_cases s <;> fin_cases t <;> fin_cases u
  · exact trialityXYZ_cubic_XXX_zero k l m
  · exact trialityXYZ_cubic_XX_tensor_zero k l m 1 (by decide)
  · exact trialityXYZ_cubic_XX_tensor_zero k l m 2 (by decide)
  · rw [xyzReduction_cubic_cycle, xyzReduction_cubic_cycle, xyzReduction_cubic_swap]
    exact trialityXYZ_cubic_XX_tensor_zero k m l 1 (by decide)
  · exact trialityXYZ_cubic_XYY_zero k l m
  · norm_num at h
  · rw [xyzReduction_cubic_cycle, xyzReduction_cubic_cycle, xyzReduction_cubic_swap]
    exact trialityXYZ_cubic_XX_tensor_zero k m l 2 (by decide)
  · norm_num at h
  · exact trialityXYZ_cubic_XZZ_zero k l m
  · rw [xyzReduction_cubic_cycle]
    exact trialityXYZ_cubic_XX_tensor_zero l m k 1 (by decide)
  · rw [xyzReduction_cubic_swap]
    exact trialityXYZ_cubic_XYY_zero l k m
  · norm_num at h
  · rw [xyzReduction_cubic_cycle, xyzReduction_cubic_cycle]
    exact trialityXYZ_cubic_XYY_zero m k l
  · exact trialityXYZ_cubic_tensor_zero 1 1 1 k l m (by decide) (by decide) (by decide)
  · exact trialityXYZ_cubic_tensor_zero 1 1 2 k l m (by decide) (by decide) (by decide)
  · norm_num at h
  · exact trialityXYZ_cubic_tensor_zero 1 2 1 k l m (by decide) (by decide) (by decide)
  · exact trialityXYZ_cubic_tensor_zero 1 2 2 k l m (by decide) (by decide) (by decide)
  · rw [xyzReduction_cubic_cycle]
    exact trialityXYZ_cubic_XX_tensor_zero l m k 2 (by decide)
  · norm_num at h
  · rw [xyzReduction_cubic_swap]
    exact trialityXYZ_cubic_XZZ_zero l k m
  · norm_num at h
  · exact trialityXYZ_cubic_tensor_zero 2 1 1 k l m (by decide) (by decide) (by decide)
  · exact trialityXYZ_cubic_tensor_zero 2 1 2 k l m (by decide) (by decide) (by decide)
  · rw [xyzReduction_cubic_cycle, xyzReduction_cubic_cycle]
    exact trialityXYZ_cubic_XZZ_zero m k l
  · exact trialityXYZ_cubic_tensor_zero 2 2 1 k l m (by decide) (by decide) (by decide)
  · exact trialityXYZ_cubic_tensor_zero 2 2 2 k l m (by decide) (by decide) (by decide)

set_option maxRecDepth 10000 in
/-- The single mixed XYZ identity supplies all six permutations; the other
21 color patterns vanish before and after triality. -/
theorem trialityXYZ_cubic_of_mixed
    (hmixed : ∀ (d e f : Fin 2048) (j k l : Fin 24),
      griessForm (griessProd
        (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d, j))))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (e, k)))))
        (sExtra (trialityXYZBasis 2 (finProdFinEquiv (f, l)))) =
      griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d, j)))
        (trialityXYZBasis 1 (finProdFinEquiv (e, k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f, l))))
    (s t u : Fin 3) (k l m : Fin 49152) :
    griessForm (griessProd (sExtra (trialityXYZBasis s k))
      (sExtra (trialityXYZBasis t l))) (sExtra (trialityXYZBasis u m)) =
    griessForm (griessProd (trialityXYZBasis s k) (trialityXYZBasis t l))
      (trialityXYZBasis u m) := by
  have hm (a b c : Fin 49152) :
      griessForm (griessProd (sExtra (trialityXYZBasis 0 a))
        (sExtra (trialityXYZBasis 1 b))) (sExtra (trialityXYZBasis 2 c)) =
      griessForm (griessProd (trialityXYZBasis 0 a) (trialityXYZBasis 1 b))
        (trialityXYZBasis 2 c) := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using
      hmixed
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm a).1
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm b).1
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm c).1
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm a).2
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm b).2
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm c).2
  by_cases h : s = t ∨ t = u ∨ u = s
  · rw [sExtra_XYZ_basis, sExtra_XYZ_basis, sExtra_XYZ_basis]
    rw [trialityXYZ_cubic_repeated_zero s t u k l m h]
    apply trialityXYZ_cubic_repeated_zero
    rcases h with h | h | h
    · exact Or.inl (congrArg trialityCycle h)
    · exact Or.inr (Or.inl (congrArg trialityCycle h))
    · exact Or.inr (Or.inr (congrArg trialityCycle h))
  · fin_cases s <;> fin_cases t <;> fin_cases u
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact hm k l m
    · norm_num at h
    · apply (griessCubic_triality_cycle _ _ _).mpr
      apply (griessCubic_triality_cycle _ _ _).mpr
      apply (griessCubic_triality_swap_left _ _ _).mpr
      exact hm k m l
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · apply (griessCubic_triality_swap_left _ _ _).mpr
      exact hm l k m
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · apply (griessCubic_triality_cycle _ _ _).mpr
      apply (griessCubic_triality_cycle _ _ _).mpr
      exact hm m k l
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · apply (griessCubic_triality_cycle _ _ _).mpr
      exact hm l m k
    · norm_num at h
    · apply (griessCubic_triality_cycle _ _ _).mpr
      apply (griessCubic_triality_swap_left _ _ _).mpr
      exact hm m l k
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h

set_option maxRecDepth 10000 in
/-- Full XYZ source multiplication needs only the octad×XYZ products and
one scalar mixed-color XYZ identity. All other source tests are discharged. -/
theorem triality_XYZ_XYZ_product_of_octad_and_mixed
    (hOT : ∀ (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k))
    (hmixed : ∀ (d e f : Fin 2048) (j k l : Fin 24),
      griessForm (griessProd
        (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d, j))))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (e, k)))))
        (sExtra (trialityXYZBasis 2 (finProdFinEquiv (f, l)))) =
      griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d, j)))
        (trialityXYZBasis 1 (finProdFinEquiv (e, k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f, l))))
    (s t : Fin 3) (k l : Fin 49152) :
    TrialityProductPreserved (trialityXYZBasis s k) (trialityXYZBasis t l) := by
  apply (trialityProductPreserved_iff_source_cubic _ _).mpr
  intro i
  rcases i with i | ⟨⟨a,p⟩ | ⟨⟨o,e⟩ | ⟨u,m⟩⟩⟩
  · simp only [trialitySourceBasis]
    apply (griessCubic_triality_cycle _ _ _).mpr
    apply (griessCubic_triality_cycle _ _ _).mpr
    apply griessCubic_triality_of_pair
    exact sExtra_preserves_diagonal_product (Pi.single i 1) (trialityXYZBasis s k)
  · simp only [trialitySourceBasis]
    apply (griessCubic_triality_cycle _ _ _).mpr
    apply (griessCubic_triality_cycle _ _ _).mpr
    apply griessCubic_triality_of_pair
    simpa only [TrialityProductPreserved, Prod.mk.eta, Equiv.apply_symm_apply] using
      triality_ABC_XYZ_product a s p
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm k).1
        ((finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).symm k).2
  · simp only [trialitySourceBasis]
    apply (griessCubic_triality_cycle _ _ _).mpr
    apply (griessCubic_triality_cycle _ _ _).mpr
    exact griessCubic_triality_of_pair _ _ _ (hOT o e s k)
  · simp only [trialitySourceBasis]
    exact trialityXYZ_cubic_of_mixed hmixed s t u k l m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
