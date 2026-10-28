/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Transitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadPermutations

/-! The original unsigned Mathieu point stabilizer has exactly the pair, octad, and odd orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The three catalogue families have distinct original zeroth coordinates. -/
theorem leechNormSixHS100LabelPoint_zero (a : LeechNormSixHS100Labels) :
    (leechNormSixHS100LabelPoint a).val.val 0 =
      match a with
      | Sum.inl _ => 4
      | Sum.inr (Sum.inl _) => 2
      | Sum.inr (Sum.inr _) => 1 := by
  rcases a with a | (o | j)
  · norm_num [leechNormSixHS100LabelPoint, leechNormSixHS100Pair, leechNormSixHS100PairIntegral]
  · change (leechNormSixHS100Octad o.val).val 0 = 2
    rw [leechNormSixHS100Octad_coordinate]
    simp only [Fin.val_zero, (Finset.mem_filter.mp o.property).2.1, ↓reduceIte]
  · change (leechNormSixHS100Odd j.val).val 0 = 1
    rw [leechNormSixHS100Odd_coordinate]
    simp [Ne.symm j.property.1]

/-- The actual point stabilizer preserves the entire original zeroth coordinate of each point. -/
theorem leechNormSixHS100Mathieu_zero (g : leechNormSixHS100PairPointStabilizer)
    (z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :
    (g • z).val.val 0 = z.val.val 0 := by
  obtain ⟨p, rfl⟩ := leechNormSixHS100PairPointHom_surjective g
  change (leechIntegralAction (golayPermutationIsometry p.val) z.val).val 0 = _
  rw [leechNormSixHS100Permutation_action]
  obtain ⟨h0, _⟩ := (leechNormSixHS100TwoCoordinates_mem p.val).mp p.property
  change z.val.val (p.val.val.symm 0) = _
  rw [p.val.val.symm_apply_eq.mpr h0.symm]

/-- Genuine five-transitivity and Golay octad uniqueness give exact positive-octad coordinates. -/
theorem leechNormSixHS100Octad_standard_coordinates (o : generatedFeasibleOctadContainingLabels)
    (p : golayAutomorphismSubgroup)
    (hp : golayPermute p.val (golayEncoder (golayLabelCoefficients (golayOctadLabel o.val))) =
      golayStandardOctad) (i : Fin 24) :
    (leechIntegralAction (golayPermutationIsometry p) (leechNormSixHS100Octad o.val)).val i =
      if i.val < 8 then 2 else 0 := by
  rw [leechNormSixHS100Permutation_action]
  change (leechNormSixHS100Octad o.val).val (p.val.symm i) = _
  rw [leechNormSixHS100Octad_coordinate]
  have he := congrArg (fun c : Fin 24 → ZMod 2 => (c i).val) hp
  change (golayEncoder (golayLabelCoefficients (golayOctadLabel o.val)) (p.val.symm i)).val =
    (golayStandardOctad i).val at he
  rw [golayLabelEncoder_match] at he
  by_cases hi : i.val < 8
  · have he' : (if (golayEncodedMask (golayOctadLabel o.val).val).testBit
        (p.val.symm i).val then 1 else 0) = (1 : ℕ) := by
      simpa [golayStandardOctad, hi, ZMod.val_one_eq_one_mod] using he
    have hh := congrArg (fun n : ℕ => (2 : ℤ) * (n : ℤ)) he'
    simpa [hi, mul_ite] using hh
  · have he' : (if (golayEncodedMask (golayOctadLabel o.val).val).testBit
        (p.val.symm i).val then 1 else 0) = (0 : ℕ) := by
      simpa [golayStandardOctad, hi, ZMod.val_one_eq_one_mod] using he
    have hh := congrArg (fun n : ℕ => (2 : ℤ) * (n : ℤ)) he'
    simpa [hi, mul_ite] using hh

/-- All seventy-seven original positive containing-pair octads form one actual Mathieu orbit. -/
theorem leechNormSixHS100Mathieu_octad_transitive
    (o v : generatedFeasibleOctadContainingLabels) :
    ∃ g : leechNormSixHS100PairPointStabilizer,
      g • leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o)) =
        leechNormSixHS100LabelPoint (Sum.inr (Sum.inl v)) := by
  obtain ⟨p, hp0, hp1, hp⟩ := leechRootedA2Octad_permutation_to_standard o.val
    (Finset.mem_filter.mp o.property).2.1 (Finset.mem_filter.mp o.property).2.2
  obtain ⟨q, hq0, hq1, hq⟩ := leechRootedA2Octad_permutation_to_standard v.val
    (Finset.mem_filter.mp v.property).2.1 (Finset.mem_filter.mp v.property).2.2
  let pp : golayPointStabilizer 2 :=
    ⟨p, (leechNormSixHS100TwoCoordinates_mem p).mpr ⟨hp0, hp1⟩⟩
  let qq : golayPointStabilizer 2 :=
    ⟨q, (leechNormSixHS100TwoCoordinates_mem q).mpr ⟨hq0, hq1⟩⟩
  have he : leechNormSixHS100PairPointHom pp •
      leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o)) =
      leechNormSixHS100PairPointHom qq •
        leechNormSixHS100LabelPoint (Sum.inr (Sum.inl v)) := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (leechNormSixHS100Octad_standard_coordinates o p hp i).trans
      (leechNormSixHS100Octad_standard_coordinates v q hq i).symm
  refine ⟨(leechNormSixHS100PairPointHom qq)⁻¹ * leechNormSixHS100PairPointHom pp, ?_⟩
  rw [mul_smul, he, inv_smul_smul]

/-- All twenty-two original outside odd positions form one actual unsigned Mathieu orbit. -/
theorem leechNormSixHS100Mathieu_odd_transitive (j k : LeechNormSixHS100OddPositions) :
    ∃ g : leechNormSixHS100PairPointStabilizer,
      g • leechNormSixHS100LabelPoint (Sum.inr (Sum.inr j)) =
        leechNormSixHS100LabelPoint (Sum.inr (Sum.inr k)) := by
  let a : Fin 3 → Fin 24 := ![0, 1, j.val]
  let b : Fin 3 → Fin 24 := ![0, 1, k.val]
  have ha : Function.Injective a := by
    intro r s h
    fin_cases r <;> fin_cases s <;> simp_all [a, j.property.1, j.property.2, Ne.symm j.property.1, Ne.symm j.property.2]
  have hb : Function.Injective b := by
    intro r s h
    fin_cases r <;> fin_cases s <;> simp_all [b, k.property.1, k.property.2, Ne.symm k.property.1, Ne.symm k.property.2]
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
  have hp0 : p.val 0 = 0 := hp 0
  have hp1 : p.val 1 = 1 := hp 1
  have hpj : p.val j.val = k.val := hp 2
  let pp : golayPointStabilizer 2 :=
    ⟨p, (leechNormSixHS100TwoCoordinates_mem p).mpr ⟨hp0, hp1⟩⟩
  refine ⟨leechNormSixHS100PairPointHom pp, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (leechIntegralAction (golayPermutationIsometry p) (leechNormSixHS100Odd j.val)).val =
    (leechNormSixHS100Odd k.val).val
  rw [leechNormSixHS100Permutation_action]
  funext i
  change (leechNormSixHS100Odd j.val).val (p.val.symm i) =
    (leechNormSixHS100Odd k.val).val i
  rw [leechNormSixHS100Odd_coordinate, leechNormSixHS100Odd_coordinate]
  have he : p.val.symm i = j.val ↔ i = k.val := by rw [p.val.symm_apply_eq, hpj]
  simp only [he]

/-- Two complete original points lie in the same actual Mathieu orbit exactly when their zeroth coordinates agree. -/
theorem leechNormSixHS100Mathieu_same_orbit_iff
    (z w : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :
    (∃ g : leechNormSixHS100PairPointStabilizer, g • z = w) ↔ z.val.val 0 = w.val.val 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (leechNormSixHS100Mathieu_zero g z).symm
  · intro h
    obtain ⟨a, rfl⟩ := leechNormSixHS100LabelPoint_surjective z
    obtain ⟨b, rfl⟩ := leechNormSixHS100LabelPoint_surjective w
    rw [leechNormSixHS100LabelPoint_zero, leechNormSixHS100LabelPoint_zero] at h
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · exact ⟨1, by simp [Subsingleton.elim a b]⟩
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact leechNormSixHS100Mathieu_octad_transitive a b
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact leechNormSixHS100Mathieu_odd_transitive a b

/-- The three genuine Mathieu orbits are exactly the three physical-coordinate families. -/
theorem leechNormSixHS100Mathieu_orbit (z :
    LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :
    MulAction.orbit leechNormSixHS100PairPointStabilizer z =
      {w | w.val.val 0 = z.val.val 0} := by
  ext w
  exact (leechNormSixHS100Mathieu_same_orbit_iff z w).trans eq_comm

/-- Any subset of the complete actual geometry splits exactly over the three original families. -/
theorem leechNormSixHS100Catalogue_subset_card (s : Set
    (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)) :
    Nat.card s =
      Nat.card {u : Unit // leechNormSixHS100LabelPoint (Sum.inl u) ∈ s} +
      Nat.card {o : generatedFeasibleOctadContainingLabels //
        leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o)) ∈ s} +
      Nat.card {j : LeechNormSixHS100OddPositions //
        leechNormSixHS100LabelPoint (Sum.inr (Sum.inr j)) ∈ s} := by
  let q : LeechNormSixHS100Labels → Prop := fun a => leechNormSixHS100LabelPoint a ∈ s
  have e : {a // q a} ≃ s := leechNormSixHS100CatalogEquiv.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Nat.card_congr e,
    Nat.card_congr (@Equiv.subtypeSum Unit
      (generatedFeasibleOctadContainingLabels ⊕ LeechNormSixHS100OddPositions) q), Nat.card_sum,
    Nat.card_congr (@Equiv.subtypeSum generatedFeasibleOctadContainingLabels
      LeechNormSixHS100OddPositions (fun a => q (Sum.inr a))), Nat.card_sum]
  exact (Nat.add_assoc _ _ _).symm

/-- The three complete physical Mathieu families contain one, seventy-seven, and twenty-two points. -/
theorem leechNormSixHS100Mathieu_family_cards :
    Nat.card {z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion //
      z.val.val 0 = 4} = 1 ∧
    Nat.card {z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion //
      z.val.val 0 = 2} = 77 ∧
    Nat.card {z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion //
      z.val.val 0 = 1} = 22 := by
  have ho : Nat.card generatedFeasibleOctadContainingLabels = 77 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, generatedFeasibleOctadContainingLabels_card]
  constructor
  · change Nat.card ({z | z.val.val 0 = 4} : Set
      (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)) = 1
    rw [leechNormSixHS100Catalogue_subset_card]
    norm_num only [Set.mem_ofPred_eq, leechNormSixHS100LabelPoint_zero,
      Nat.card_subtype_true, Nat.card_of_isEmpty, Nat.card_unique]
  constructor
  · change Nat.card ({z | z.val.val 0 = 2} : Set
      (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)) = 77
    rw [leechNormSixHS100Catalogue_subset_card]
    norm_num only [Set.mem_ofPred_eq, leechNormSixHS100LabelPoint_zero,
      Nat.card_subtype_true, Nat.card_of_isEmpty, ho]
  · change Nat.card ({z | z.val.val 0 = 1} : Set
      (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)) = 22
    rw [leechNormSixHS100Catalogue_subset_card]
    norm_num only [Set.mem_ofPred_eq, leechNormSixHS100LabelPoint_zero,
      Nat.card_subtype_true, Nat.card_of_isEmpty, leechNormSixHS100OddPositions_card]

/-- The original positive pair is the singleton Mathieu orbit. -/
theorem leechNormSixHS100Mathieu_pair_orbit_card :
    Nat.card (MulAction.orbit leechNormSixHS100PairPointStabilizer leechNormSixHS100PairPoint) = 1 := by
  rw [leechNormSixHS100Mathieu_orbit]
  exact leechNormSixHS100Mathieu_family_cards.1

/-- Each original containing-pair octad has an actual Mathieu orbit of seventy-seven points. -/
theorem leechNormSixHS100Mathieu_octad_orbit_card (o : generatedFeasibleOctadContainingLabels) :
    Nat.card (MulAction.orbit leechNormSixHS100PairPointStabilizer
      (leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o)))) = 77 := by
  rw [leechNormSixHS100Mathieu_orbit, leechNormSixHS100LabelPoint_zero]
  exact leechNormSixHS100Mathieu_family_cards.2.1

/-- Each original outside odd position has an actual Mathieu orbit of twenty-two points. -/
theorem leechNormSixHS100Mathieu_odd_orbit_card (j : LeechNormSixHS100OddPositions) :
    Nat.card (MulAction.orbit leechNormSixHS100PairPointStabilizer
      (leechNormSixHS100LabelPoint (Sum.inr (Sum.inr j)))) = 22 := by
  rw [leechNormSixHS100Mathieu_orbit, leechNormSixHS100LabelPoint_zero]
  exact leechNormSixHS100Mathieu_family_cards.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
