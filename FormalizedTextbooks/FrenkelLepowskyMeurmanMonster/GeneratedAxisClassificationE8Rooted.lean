/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Sections

/-! A section through the distinguished frame class is already a monomial
image of a coordinate section. The internal norm-eight transitivity and
actual frame stabilizer recognition discharge this essential incidence step. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A positive coordinate frame vector belongs to the section when its
coordinate is in the specified codeword. -/
theorem generatedAxisE8_frame_supported (c : Fin 24 → ZMod 2) (i : Fin 24)
    (hi : c i ≠ 0) : generatedOctadSupported c (leechCoordinateFrameLattice i).val := by
  intro j hj
  by_cases hji : j = i
  · subst j
    exact False.elim (hi hj)
  · simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hji]

/-- Support preservation also holds for the inverse actual lattice isometry. -/
theorem generatedAxisE8_preserves_inv (c : Fin 24 → ZMod 2) (g : leechIsomSubgroup)
    (hg : generatedOctadPreserves c g) : generatedOctadPreserves c g⁻¹ := by
  intro u
  have h := hg ((leechIntegralAction g).symm u)
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [map_inv, LinearEquiv.coe_inv] using h.symm

/-- An actual section incident with the distinguished norm-eight class is
a monomial image of the original coordinate section. -/
theorem generatedAxisE8_rooted_monomial (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8) (i : Fin 24) (hi : c i ≠ 0)
    (g : leechIsomSubgroup)
    (hb : leechReduction (leechCoordinateFrameLattice 0) ∈
      generatedAxisE8FrameClasses (generatedAxisE8ImageSection g c)) :
    ∃ m : leechIsomSubgroup, m ∈ golayMonomialSubgroup ∧
      generatedAxisE8ImageSection g c = generatedAxisE8ImageSection m c := by
  obtain ⟨u, hu, hnu, hub⟩ := hb
  obtain ⟨v, hv, hgv⟩ := (generatedAxisE8ImageSection_mem g c u).mp hu
  have hnv : leechSquareSum v.val = 64 := by
    rw [← leechIntegralAction_squareSum g v, hgv]
    exact hnu
  obtain ⟨k, _, hkp, hkv⟩ := generatedOctad_normEight_transitive c hc hw v
    (leechCoordinateFrameLattice i) hv (generatedAxisE8_frame_supported c i hi)
    hnv (leechCoordinateFrameVector_square i)
  let m := g * k⁻¹
  have hm : leechIntegralAction m (leechCoordinateFrameLattice i) = u := by
    change leechIntegralAction (g * k⁻¹) (leechCoordinateFrameLattice i) = u
    rw [map_mul, LinearEquiv.mul_apply, ← hkv, map_inv, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
    exact hgv
  have hfix : m ∈ MulAction.stabilizer leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)) := by
    change leechModTwoAction m (leechReduction (leechCoordinateFrameLattice 0)) = _
    calc
      leechModTwoAction m (leechReduction (leechCoordinateFrameLattice 0)) =
          leechModTwoAction m (leechReduction (leechCoordinateFrameLattice i)) :=
        congrArg (leechModTwoAction m) (leechFrame_reduction_eq i).symm
      _ = leechReduction (leechIntegralAction m (leechCoordinateFrameLattice i)) := rfl
      _ = leechReduction u := congrArg leechReduction hm
      _ = leechReduction (leechCoordinateFrameLattice 0) := hub
  refine ⟨m, leechFrameClass_stabilizer_eq_monomial.le hfix, ?_⟩
  exact (generatedAxisE8ImageSection_mul_preserving g k⁻¹ c
    (generatedAxisE8_preserves_inv c k hkp)).symm

/-- Arbitrary original Golay signs preserve every integral coordinate section. -/
theorem generatedAxisE8_sign_preserves (c : Fin 24 → ZMod 2) (d : golayCode) :
    generatedOctadPreserves c (golaySignIsometry d) := by
  intro u
  rw [leechIntegralAction_golaySign]
  constructor
  · intro h i hi
    have hz := h i hi
    simp only [golayIntegerSign] at hz
    split_ifs at hz <;> simpa only [neg_eq_zero] using hz
  · intro h i hi
    simp only [golayIntegerSign, h i hi, neg_zero, ite_self]

/-- A genuine Golay permutation maps a coordinate section to the permuted code section. -/
theorem generatedAxisE8_permutation_image (c : Fin 24 → ZMod 2)
    (p : golayAutomorphismSubgroup) :
    generatedAxisE8ImageSection (golayPermutationIsometry p) c =
      generatedAxisE8CoordinateSection (golayPermute p.val c) := by
  ext u
  rw [generatedAxisE8ImageSection_mem]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (generatedOctadSupported_permutation c (golayPermute p.val c) p rfl v).mpr hv
  · intro hu
    let v := (leechIntegralAction (golayPermutationIsometry p)).symm u
    refine ⟨v, ?_, LinearEquiv.apply_symm_apply _ u⟩
    have h := generatedOctadSupported_permutation c (golayPermute p.val c) p rfl v
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.mp hu

/-- Every monomial image is an actual coordinate code section. -/
theorem generatedAxisE8_monomial_image (c : Fin 24 → ZMod 2)
    (m : leechIsomSubgroup) (hm : m ∈ golayMonomialSubgroup) :
    ∃ p : golayAutomorphismSubgroup, generatedAxisE8ImageSection m c =
      generatedAxisE8CoordinateSection (golayPermute p.val c) := by
  obtain ⟨d, p, rfl⟩ := hm
  refine ⟨p, ?_⟩
  rw [generatedAxisE8ImageSection_mul, generatedAxisE8_permutation_image]
  exact generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ d)

/-- The essential rooted-section coverage conclusion uses only actual
isometries, internal transitivity, and actual monomial recognition. -/
theorem generatedAxisE8_rooted_coordinate (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8) (i : Fin 24) (hi : c i ≠ 0)
    (g : leechIsomSubgroup)
    (hb : leechReduction (leechCoordinateFrameLattice 0) ∈
      generatedAxisE8FrameClasses (generatedAxisE8ImageSection g c)) :
    ∃ p : golayAutomorphismSubgroup, generatedAxisE8ImageSection g c =
      generatedAxisE8CoordinateSection (golayPermute p.val c) := by
  obtain ⟨m, hm, he⟩ := generatedAxisE8_rooted_monomial c hc hw i hi g hb
  obtain ⟨p, hp⟩ := generatedAxisE8_monomial_image c m hm
  exact ⟨p, he.trans hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
