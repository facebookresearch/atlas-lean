/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingE7ProjectionCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitE8Section

/-! Genuine identification of the standard E7 normal with the original containing first root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem source_normal_permutation :
    ∃ p : golayAutomorphismSubgroup, p.val 4 = 0 ∧ p.val 5 = 1 ∧
      golayPermute p.val golayStandardOctad = golayStandardOctad := by
  let a : Fin 5 → Fin 24 := ![4, 5, 0, 1, 2]
  let b : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have ha : Function.Injective a := by decide +kernel
  have hb : Function.Injective b := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a b ha hb
  refine ⟨p, hp 0, hp 1, ?_⟩
  apply golayOctad_unique_through_first_five _ _
    ((p.property _).mp golayStandardOctad_mem) golayStandardOctad_mem
    ((Equiv.sum_comp p.val.symm (fun i => (golayStandardOctad i).val)).trans
      golayStandardOctad_weight) golayStandardOctad_weight
  intro i hi
  let j : Fin 5 := ⟨i.val, hi⟩
  have hbi : b j = i := Fin.ext rfl
  have hpi : p.val.symm i = a j := by rw [← hbi, ← hp j, p.val.symm_apply_apply]
  have hs : ∀ j : Fin 5, golayStandardOctad (a j) = 1 := by decide +kernel
  refine ⟨?_, ?_⟩
  · change golayStandardOctad (p.val.symm i) = 1
    rw [hpi]
    exact hs j
  · simp [golayStandardOctad, show i.val < 8 by omega]

private theorem normal_coordinates :
    generatedTenthE7OrbitNormalRoot.val = fun i : Fin 24 =>
      4 * (if i = 4 then (1 : ℤ) else 0) + 4 * (if i = 5 then 1 else 0) := by
  change generatedTenthE7XiNormal = _
  decide +kernel

/-- A genuine source-octad-preserving monomial sends the positive standard normal to the
original positive containing first root, retaining its full integral orientation. -/
theorem generatedFeasibleContainingE7_source_normal_transport :
    ∃ t : leechIsomSubgroup, t ∈ golayMonomialSubgroup ∧
      generatedAxisE8ImageSection t golayStandardOctad =
        generatedAxisE8CoordinateSection golayStandardOctad ∧
      leechIntegralAction t generatedTenthE7OrbitNormalRoot =
        griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  obtain ⟨p, hp4, hp5, hpword⟩ := source_normal_permutation
  let f : Fin 2 → Fin 24 := fun j => Fin.castAdd 22 j
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨d, hd⟩ := golayCoordinateProjection_surjective (by decide : 2 < 8) f hf ![0, 1]
  have hd0 : d.val 0 = 0 := congrFun hd 0
  have hd1 : d.val 1 = 1 := congrFun hd 1
  let t := golaySignIsometry d * golayPermutationIsometry p
  have hv : (leechIntegralAction (golayPermutationIsometry p)
      generatedTenthE7OrbitNormalRoot).val = fun i : Fin 24 =>
        4 * (if i = 0 then (1 : ℤ) else 0) + 4 * (if i = 1 then 1 else 0) := by
    rw [leechIntegralAction_golayPermutation, normal_coordinates]
    funext i
    have ha : p.val.symm i = 4 ↔ i = 0 := by rw [p.val.symm_apply_eq, hp4]
    have hb : p.val.symm i = 5 ↔ i = 1 := by rw [p.val.symm_apply_eq, hp5]
    simp only [golayIntegerPermute, ha, hb]
  refine ⟨t, ⟨d, p, rfl⟩, ?_, ?_⟩
  · change generatedAxisE8ImageSection (golaySignIsometry d * golayPermutationIsometry p)
      golayStandardOctad = _
    rw [generatedAxisE8ImageSection_mul, generatedAxisE8_permutation_image, hpword]
    exact generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ d)
  · change leechIntegralAction (golaySignIsometry d * golayPermutationIsometry p) _ = _
    rw [map_mul, LinearEquiv.mul_apply]
    apply Subtype.ext
    rw [leechIntegralAction_golaySign]
    change golayIntegerSign d.val
      (leechIntegralAction (golayPermutationIsometry p) generatedTenthE7OrbitNormalRoot).val =
        griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair))
    rw [hv]
    funext i
    by_cases hi0 : i = 0
    · subst i
      simp [golayIntegerSign, hd0, griessShortIntegral,
        generatedFeasiblePhysicalRootPair_coordinates]
    · by_cases hi1 : i = 1
      · subst i
        simp [golayIntegerSign, hd1, griessShortIntegral,
          generatedFeasiblePhysicalRootPair_coordinates]
      · simp [golayIntegerSign, hi0, hi1, griessShortIntegral,
          generatedFeasiblePhysicalRootPair_coordinates]

private theorem standard_normal_pairing (u : Fin 24 → ℤ) :
    leechIntegralPairing generatedTenthE7OrbitNormalRoot.val u = 4 * (u 4 + u 5) := by
  rw [normal_coordinates]
  unfold leechIntegralPairing
  simp only [add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem source_normal_pairing (u : Fin 24 → ℤ) :
    leechIntegralPairing
      (griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair))) u =
        4 * (u 0 - u 1) := by
  unfold leechIntegralPairing
  simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates, ite_true,
    add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Every genuine positive-normal transport identifies the entire actual perpendicular
preferred-root condition, independently of its physical representative orientation. -/
theorem generatedFeasibleContainingE7_normal_short_orthogonal
    (t : leechIsomSubgroup)
    (ht : leechIntegralAction t generatedTenthE7OrbitNormalRoot =
      griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
    (r : GriessShortIndex) :
    griessShortIntegral (griessShortPermutation t r) 0 =
        griessShortIntegral (griessShortPermutation t r) 1 ↔
      griessShortIntegral r 4 + griessShortIntegral r 5 = 0 := by
  have h := generatedFeasibleContaining_integral_action_pairing t
    generatedTenthE7OrbitNormalRoot (griessShortLatticeVector r)
  rw [ht] at h
  change leechIntegralPairing
    (griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
    (leechIntegralAction t (griessShortLatticeVector r)).val =
      leechIntegralPairing generatedTenthE7OrbitNormalRoot.val (griessShortIntegral r) at h
  rw [standard_normal_pairing] at h
  rcases generatedE8Short_integral_sign t r with hr | hr
  · rw [hr] at h
    change leechIntegralPairing
      (griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
      (griessShortIntegral (griessShortPermutation t r)) = _ at h
    rw [source_normal_pairing] at h
    omega
  · rw [hr] at h
    change leechIntegralPairing
      (griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
      (-griessShortIntegral (griessShortPermutation t r)) = _ at h
    have hn (u v : Fin 24 → ℤ) : leechIntegralPairing u (-v) =
        -leechIntegralPairing u v := by
      simp [leechIntegralPairing, Pi.neg_apply, Finset.sum_neg_distrib]
    rw [hn, source_normal_pairing] at h
    omega

private theorem section_short_transport (t : leechIsomSubgroup)
    (ht : generatedAxisE8ImageSection t golayStandardOctad =
      generatedAxisE8CoordinateSection golayStandardOctad) (r : GriessShortIndex) :
    griessShortPermutation t r ∈
        generatedAxisE8ShortLines (generatedAxisE8CoordinateSection golayStandardOctad) ↔
      r ∈ generatedAxisE8ShortLines (generatedAxisE8CoordinateSection golayStandardOctad) := by
  have h := generatedAxisE8ShortLines_image_mem t
    (generatedAxisE8CoordinateSection golayStandardOctad) r
  change _ ∈ generatedAxisE8ShortLines (generatedAxisE8ImageSection t golayStandardOctad) ↔
    _ at h
  rwa [ht] at h

private theorem source_root_standard_address (t : leechIsomSubgroup)
    (htS : generatedAxisE8ImageSection t golayStandardOctad =
      generatedAxisE8CoordinateSection golayStandardOctad)
    (htN : leechIntegralAction t generatedTenthE7OrbitNormalRoot =
      griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
    (r : generatedFeasibleContainingE7ProjectionRootLines) :
    ∃ n : Fin 63, generatedTenthE7OrbitNodeLabel n = (griessShortPermutation t).symm r.val.val := by
  let e := griessShortPermutation t
  have hm : e.symm r.val.val ∈
      generatedAxisE8ShortLines (generatedAxisE8CoordinateSection golayStandardOctad) := by
    apply (section_short_transport t htS _).mp
    change e (e.symm r.val.val) ∈ _
    rw [e.apply_symm_apply]
    exact r.val.property
  have ho : griessShortIntegral (e.symm r.val.val) 4 +
      griessShortIntegral (e.symm r.val.val) 5 = 0 := by
    apply (generatedFeasibleContainingE7_normal_short_orthogonal t htN _).mp
    change griessShortIntegral (e (e.symm r.val.val)) 0 =
      griessShortIntegral (e (e.symm r.val.val)) 1
    rw [e.apply_symm_apply]
    exact r.property
  let rs : generatedTenthE7StandardRootLines := ⟨⟨e.symm r.val.val, by
    rwa [generatedTenth_e7_standard_e8_section_actual]⟩, ho⟩
  obtain ⟨i, hi⟩ := generatedTenthE7StandardRootLineEquiv.surjective rs
  have hord : Function.Surjective generatedTenthE7OrbitOrder :=
    Finite.surjective_of_injective generatedTenth_e7_orbit_order_injective
  obtain ⟨n, hn⟩ := hord i
  refine ⟨n, ?_⟩
  have he := congrArg (fun x : generatedTenthE7StandardRootLines => x.val.val) hi
  rw [← hn] at he
  exact he

/-- Any two complete source E7 projection lines are joined by an actual whole-section
isometry fixing the original first root with its positive integral orientation. -/
theorem generatedFeasibleContainingE7_projection_lines_transitive
    (r s : generatedFeasibleContainingE7ProjectionRootLines) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g golayStandardOctad =
        generatedAxisE8CoordinateSection golayStandardOctad ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g r.val.val = s.val.val := by
  obtain ⟨t, _, htS, htN⟩ := generatedFeasibleContainingE7_source_normal_transport
  obtain ⟨i, hi⟩ := source_root_standard_address t htS htN r
  obtain ⟨j, hj⟩ := source_root_standard_address t htS htN s
  obtain ⟨a, haN, ha⟩ := generatedTenth_e7_root_orbit_positive_between i j
  have haL : griessShortPermutation a.val (generatedTenthE7OrbitNodeLabel i) =
      generatedTenthE7OrbitNodeLabel j := by
    apply griessShortClass_injective
    rw [griessShortPermutation_class, ← generatedTenth_e7_orbit_node_class_actual,
      ← generatedTenth_e7_orbit_node_class_actual]
    exact ha
  let g := t * a.val * t⁻¹
  refine ⟨g, ?_, ?_, ?_⟩
  · have htm := (generatedAxisE8SectionStabilizer_mem golayStandardOctad t).mpr htS
    have ham : a.val ∈ generatedAxisE8SectionStabilizer golayStandardOctad := by
      apply (generatedAxisE8SectionStabilizer_mem _ _).mpr
      have h := generatedTenth_e7_root_orbit_e8_section_map a
      rwa [generatedTenth_e7_standard_e8_section_actual] at h
    apply (generatedAxisE8SectionStabilizer_mem _ _).mp
    exact (generatedAxisE8SectionStabilizer golayStandardOctad).mul_mem
      ((generatedAxisE8SectionStabilizer golayStandardOctad).mul_mem htm ham)
      ((generatedAxisE8SectionStabilizer golayStandardOctad).inv_mem htm)
  · change leechIntegralAction (t * a.val * t⁻¹) _ = _
    rw [map_mul, map_mul, map_inv]
    change leechIntegralAction t (leechIntegralAction a.val
      ((leechIntegralAction t).symm
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))))) = _
    rw [← htN, LinearEquiv.symm_apply_apply, haN]
  · change griessShortPermutation (t * a.val * t⁻¹) r.val.val = s.val.val
    rw [map_mul, map_mul, map_inv]
    change griessShortPermutation t (griessShortPermutation a.val
      ((griessShortPermutation t).symm r.val.val)) = s.val.val
    rw [← hi, haL, hj, Equiv.apply_symm_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
