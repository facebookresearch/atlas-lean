/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayFrobenius
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBilinearReduction
/-! Frobenius reduction of concrete triality multiplication checks.

A form-preserving operator's multiplication defect pairs cyclically against
transformed test vectors. The full actual source basis therefore detects
preservation of each pair, and cubic tests can be cycled or reversed.
The global equivalence requires every source cubic test explicitly; it does
not assume or assert the unfinished triality product theorem. The fixed
right-factor helper likewise states its basis-product hypotheses explicitly.
These reductions use the proved concrete Frobenius identity and positive
Griess form. Source: Conway's Griess algebra and Seysen's source dictionary. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual vector by which a linear equivalence fails to preserve a product. -/
noncomputable def griessProductDefect (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (x y : GriessSpace) : GriessSpace :=
  e (griessProd x y) - griessProd (e x) (e y)

lemma griessProductDefect_eq_zero_iff (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (x y : GriessSpace) : griessProductDefect e x y = 0 ↔
      e (griessProd x y) = griessProd (e x) (e y) := sub_eq_zero

lemma griessProductDefect_symm (e : GriessSpace ≃ₗ[ℝ] GriessSpace) (x y : GriessSpace) :
    griessProductDefect e x y = griessProductDefect e y x := by
  simp only [griessProductDefect, griessProd_comm x y, griessProd_comm (e x) (e y)]

lemma griessProductDefect_pairing_cycle (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, griessForm (e x) (e y) = griessForm x y) (x y z : GriessSpace) :
    griessForm (griessProductDefect e x y) (e z) =
      griessForm (e x) (griessProductDefect e y z) := by
  simp only [griessProductDefect, map_sub, LinearMap.sub_apply]
  rw [he (griessProd x y) z, griessProd_frobenius,
    griessProd_frobenius, he x (griessProd y z)]

lemma griessForm_eq_of_source_pairings (x y : GriessSpace)
    (h : ∀ i, griessForm x (trialitySourceBasis i) =
      griessForm y (trialitySourceBasis i)) : x = y := by
  have hl : griessForm x = griessForm y := by
    apply LinearMap.ext_on_range trialitySourceBasis_span
    exact h
  have hz : griessForm (x - y) (x - y) = 0 := by
    have hd : griessForm (x - y) = griessForm x - griessForm y := map_sub griessForm x y
    rw [hd, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hl (x - y))
  exact sub_eq_zero.mp ((griessForm_self_eq_zero_iff (x - y)).mp hz)

lemma griessForm_eq_of_transformed_source_pairings
    (e : GriessSpace ≃ₗ[ℝ] GriessSpace) (x y : GriessSpace)
    (h : ∀ i, griessForm x (e (trialitySourceBasis i)) =
      griessForm y (e (trialitySourceBasis i))) : x = y := by
  have hl : (griessForm x).comp e.toLinearMap = (griessForm y).comp e.toLinearMap := by
    apply LinearMap.ext_on_range trialitySourceBasis_span
    intro i
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h i
  apply griessForm_eq_of_source_pairings
  intro i
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun hl (e.symm (trialitySourceBasis i))

lemma griessProduct_preserved_iff_source_cubic (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, griessForm (e x) (e y) = griessForm x y) (x y : GriessSpace) :
    e (griessProd x y) = griessProd (e x) (e y) ↔
      ∀ i, griessForm (griessProd (e x) (e y)) (e (trialitySourceBasis i)) =
        griessForm (griessProd x y) (trialitySourceBasis i) := by
  constructor
  · intro hp i
    rw [← hp, he]
  · intro h
    apply griessForm_eq_of_transformed_source_pairings e
    intro i
    rw [he]
    exact (h i).symm

lemma griessProduct_preserved_of_source_right (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, griessForm (e x) (e y) = griessForm x y)
    (y : GriessSpace)
    (hy : ∀ i, e (griessProd y (trialitySourceBasis i)) =
      griessProd (e y) (e (trialitySourceBasis i))) (x : GriessSpace) :
    e (griessProd x y) = griessProd (e x) (e y) := by
  apply (griessProductDefect_eq_zero_iff e x y).mp
  apply griessForm_eq_of_transformed_source_pairings e
  intro i
  rw [griessProductDefect_pairing_cycle e he]
  rw [(griessProductDefect_eq_zero_iff e y (trialitySourceBasis i)).mpr (hy i)]
  simp

lemma griessForm_swap (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma griessCubic_triality_cycle (x y z : GriessSpace) :
    (griessForm (griessProd (sExtra x) (sExtra y)) (sExtra z) =
      griessForm (griessProd x y) z) ↔
    (griessForm (griessProd (sExtra y) (sExtra z)) (sExtra x) =
      griessForm (griessProd y z) x) := by
  rw [griessProd_frobenius, griessProd_frobenius,
    griessForm_swap (sExtra x), griessForm_swap x]

/-- Test a given pair against every actual source basis vector. -/
theorem trialityProductPreserved_iff_source_cubic (x y : GriessSpace) :
    TrialityProductPreserved x y ↔
      ∀ i, griessForm (griessProd (sExtra x) (sExtra y)) (sExtra (trialitySourceBasis i)) =
        griessForm (griessProd x y) (trialitySourceBasis i) :=
  griessProduct_preserved_iff_source_cubic sExtra sExtra_preserves_griessForm x y

theorem trialityProductPreserved_of_source_right (y : GriessSpace)
    (hy : ∀ i, TrialityProductPreserved y (trialitySourceBasis i)) (x : GriessSpace) :
    TrialityProductPreserved x y :=
  griessProduct_preserved_of_source_right sExtra sExtra_preserves_griessForm y hy x

lemma griessCubic_triality_swap_left (x y z : GriessSpace) :
    (griessForm (griessProd (sExtra x) (sExtra y)) (sExtra z) =
      griessForm (griessProd x y) z) ↔
    (griessForm (griessProd (sExtra y) (sExtra x)) (sExtra z) =
      griessForm (griessProd y x) z) := by
  rw [griessProd_comm (sExtra x) (sExtra y), griessProd_comm x y]

lemma griessCubic_triality_of_pair (x y z : GriessSpace)
    (hxy : TrialityProductPreserved x y) :
    griessForm (griessProd (sExtra x) (sExtra y)) (sExtra z) =
      griessForm (griessProd x y) z := by
  rw [← hxy, sExtra_preserves_griessForm]

/-- The actual source cubic identities are equivalent to full product preservation. -/
theorem griessProduct_invariance_iff_source_cubic
    (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, griessForm (e x) (e y) = griessForm x y) :
    (∀ x y, e (griessProd x y) = griessProd (e x) (e y)) ↔
      ∀ i j k, griessForm
        (griessProd (e (trialitySourceBasis i)) (e (trialitySourceBasis j)))
          (e (trialitySourceBasis k)) =
        griessForm (griessProd (trialitySourceBasis i) (trialitySourceBasis j))
          (trialitySourceBasis k) := by
  constructor
  · intro hp i j k
    rw [← hp, he]
  · intro hc
    apply (griessProduct_invariance_iff_source_basis e).mpr
    intro i j
    exact (griessProduct_preserved_iff_source_cubic e he _ _).mpr (hc i j)
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
