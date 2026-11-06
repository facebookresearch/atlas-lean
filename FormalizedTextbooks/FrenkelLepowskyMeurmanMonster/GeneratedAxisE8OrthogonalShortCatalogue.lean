/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadComplementOrbitProof
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadQPhase

/-! The actual integral short roots orthogonal to the original coordinate E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Actual preferred short lines orthogonal to every integral vector of a given section. -/
def generatedAxisE8OrthogonalShortLines (S : Submodule ℤ leechIntegral) :
    Set GriessShortIndex :=
  {r | ∀ u : leechIntegral, u ∈ S →
    leechIntegralPairing (griessShortIntegral r) u.val = 0}

/-- The original section codeword is precisely the physical block eight through fifteen. -/
theorem generatedAxisE8Orthogonal_old_word :
    golayOctadWord generatedOctadBasisOctad =
      fun i : Fin 24 => if 8 ≤ i.val ∧ i.val < 16 then (1 : ZMod 2) else 0 := by
  have hl : golayOctadLabel generatedOctadBasisOctad = 3 :=
    congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, by decide +kernel⟩)
  have hc : ∀ i : Fin 24,
      (golayEncodedMask 3).testBit i.val = decide (8 ≤ i.val ∧ i.val < 16) := by
    decide +kernel
  ext i
  apply ZMod.val_injective 2
  change (golayEncoder (golayLabelCoefficients
      (golayOctadLabel generatedOctadBasisOctad)) i).val = _
  rw [golayLabelEncoder_match, hl]
  change (if (golayEncodedMask 3).testBit i.val then 1 else 0) = _
  by_cases hi : 8 ≤ i.val ∧ i.val < 16
  · have hb : (golayEncodedMask 3).testBit i.val = true := by
      simpa [hi] using hc i
    rw [hb]
    simp only [hi, ite_true]
    exact (by decide +kernel : (1 : ℕ) = (1 : ZMod 2).val)
  · have hb : (golayEncodedMask 3).testBit i.val = false := by
      simpa [hi] using hc i
    rw [hb]
    simp only [Bool.false_eq_true, ite_false, hi]
    rfl

/-- Orthogonality to the actual section is exactly vanishing on its eight physical coordinates. -/
theorem generatedAxisE8Orthogonal_old_mem (r : GriessShortIndex) :
    r ∈ generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) ↔
      ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → griessShortIntegral r i = 0 := by
  constructor
  · intro hr i hi0 hi1
    have hf : leechCoordinateFrameLattice i ∈
        generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad) := by
      change ∀ k : Fin 24, golayOctadWord generatedOctadBasisOctad k = 0 →
        leechCoordinateFrameVector i k = 0
      intro k hk
      by_cases hki : k = i
      · subst k
        rw [generatedAxisE8Orthogonal_old_word] at hk
        simp [hi0, hi1] at hk
      · simp [leechCoordinateFrameVector, hki]
    have h := hr _ hf
    change (griessShortIntegral r) ⬝ᵥ Pi.single i 8 = 0 at h
    rw [dotProduct_single] at h
    omega
  · intro hr u hu
    change generatedOctadSupported (golayOctadWord generatedOctadBasisOctad) u.val at hu
    change ∑ i, griessShortIntegral r i * u.val i = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : 8 ≤ i.val ∧ i.val < 16
    · rw [hr i hi.1 hi.2, zero_mul]
    · rw [hu i (by rw [generatedAxisE8Orthogonal_old_word]; simp [hi]), mul_zero]

/-- The120 physical pair nodes give actual increasing catalogue indices. -/
def generatedAxisE8OrthogonalPairIndex (n : Fin 120) : Fin 276 :=
  griessPairIndex (golayOctadComplementPairNode n).1 (golayOctadComplementPairNode n).2
    (by
      have h := (Finset.mem_filter.mp (golayOctadComplement_pair_member n)).2.1
      exact ne_of_lt h)

/-- Those indices retain precisely the original physical node coordinates. -/
theorem generatedAxisE8OrthogonalPairIndex_coordinates (n : Fin 120) :
    griessCoordinatePair (generatedAxisE8OrthogonalPairIndex n) =
      golayOctadComplementPairNode n := by
  rw [generatedAxisE8OrthogonalPairIndex, griessPairIndex_coordinates]
  have hlt : (golayOctadComplementPairNode n).1 <
      (golayOctadComplementPairNode n).2 :=
    (Finset.mem_filter.mp (golayOctadComplement_pair_member n)).2.1
  simp only [hlt, ite_true]

/-- The30 original disjoint octad labels give actual original octad dictionary indices. -/
def generatedAxisE8OrthogonalOctadIndex (n : Fin 30) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨golayOctadComplementOctadNode n, by
      have h := (Finset.mem_filter.mp (golayOctadComplement_octad_member n)).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- Those indices are bound to their original encoded codewords. -/
theorem generatedAxisE8OrthogonalOctadIndex_label (n : Fin 30) :
    golayOctadLabel (generatedAxisE8OrthogonalOctadIndex n) =
      golayOctadComplementOctadNode n := by
  exact congrArg Subtype.val
    ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)

/-- The original preferred complement catalogue has240 pair and1920 octad addresses. -/
def generatedAxisE8OrthogonalCatalogueLabel :
    (Fin 2 × Fin 120) ⊕ (Fin 30 × Fin 64) → GriessShortIndex
  | Sum.inl (s, n) => Sum.inl (s, generatedAxisE8OrthogonalPairIndex n)
  | Sum.inr (n, e) => Sum.inr (Sum.inl (generatedAxisE8OrthogonalOctadIndex n, e))

/-- Different physical complement addresses produce different actual preferred short labels. -/
theorem generatedAxisE8OrthogonalCatalogueLabel_injective :
    Function.Injective generatedAxisE8OrthogonalCatalogueLabel := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hh := Sum.inl_injective h
      have hs : x.1 = y.1 := congrArg (fun z : Fin 2 × Fin 276 => z.1) hh
      have hp : generatedAxisE8OrthogonalPairIndex x.2 =
          generatedAxisE8OrthogonalPairIndex y.2 := congrArg (fun z : Fin 2 × Fin 276 => z.2) hh
      have hn := congrArg griessCoordinatePair hp
      rw [generatedAxisE8OrthogonalPairIndex_coordinates,
        generatedAxisE8OrthogonalPairIndex_coordinates] at hn
      exact congrArg Sum.inl (Prod.ext hs (golayOctadComplement_pair_injective hn))
    | inr y => cases h
  | inr x =>
    cases y with
    | inl y => cases h
    | inr y =>
      have hh := Sum.inl_injective (Sum.inr_injective h)
      have he : x.2 = y.2 := congrArg (fun z : Fin 759 × Fin 64 => z.2) hh
      have ho : generatedAxisE8OrthogonalOctadIndex x.1 =
          generatedAxisE8OrthogonalOctadIndex y.1 := congrArg (fun z : Fin 759 × Fin 64 => z.1) hh
      have hn := congrArg golayOctadLabel ho
      rw [generatedAxisE8OrthogonalOctadIndex_label,
        generatedAxisE8OrthogonalOctadIndex_label] at hn
      exact congrArg Sum.inr (Prod.ext (golayOctadComplement_octad_injective hn) he)

set_option maxHeartbeats 8000000 in
-- Check both original preferred pair sign families against the eight physical section coordinates.
private theorem pair_zero_check : ∀ s : Fin 2, ∀ a b : Fin 24, a < b →
    ((∀ i : Fin 24, 8 ≤ i.val → i.val < 16 →
      4 * (if i = a then (1 : ℤ) else 0) +
        (if s = 0 then -4 else 4) * (if i = b then 1 else 0) = 0) ↔
      ¬ (8 ≤ a.val ∧ a.val < 16) ∧ ¬ (8 ≤ b.val ∧ b.val < 16)) := by
  decide +kernel

/-- Original pair lines are orthogonal exactly when both physical coordinates are outside. -/
theorem generatedAxisE8Orthogonal_pair_mem (s : Fin 2) (p : Fin 276) :
    Sum.inl (s, p) ∈ generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) ↔
      griessCoordinatePair p ∈ golayOctadComplementPairs := by
  rw [generatedAxisE8Orthogonal_old_mem]
  have hlt := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hlt
  simp only [golayOctadComplementPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    griessShortIntegral]
  have hltNat : (griessCoordinatePair p).1.val < (griessCoordinatePair p).2.val := hlt
  simpa only [hltNat, true_and] using pair_zero_check s _ _ hlt

/-- Original octad lines are orthogonal exactly when their actual support avoids the section. -/
theorem generatedAxisE8Orthogonal_octad_mem (o : Fin 759) (e : Fin 64) :
    Sum.inr (Sum.inl (o, e)) ∈ generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) ↔
      golayOctadLabel o ∈ golayOctadComplementOctads := by
  rw [generatedAxisE8Orthogonal_old_mem]
  have hw : golayMaskWeight (golayEncodedMask (golayOctadLabel o).val) = 8 :=
    (Finset.mem_filter.mp ((golayOctads.orderIsoOfFin golayOctads_card) o).property).2
  simp only [golayOctadComplementOctads, Finset.mem_filter, Finset.mem_univ,
    true_and, hw]
  constructor
  · intro h j
    let i : Fin 24 := ⟨8 + j.val, by omega⟩
    have hz := h i (by dsimp [i]; omega) (by dsimp [i]; omega)
    have hv : griessShortVector (Sum.inr (Sum.inl (o, e))) i = 0 := by
      simp [griessShortVector, hz]
    have hb := mt (generatedAxis_octad_coordinate_ne_zero o e i).mpr (not_ne_iff.mpr hv)
    exact Bool.eq_false_iff.mpr hb
  · intro h i hi0 hi1
    let j : Fin 8 := ⟨i.val - 8, by omega⟩
    have hj : 8 + j.val = i.val := by dsimp [j]; omega
    have hb := h j
    rw [hj] at hb
    simp only [griessShortIntegral, hb, Bool.false_eq_true, ite_false]

/-- Every actual preferred complement address gives a genuinely orthogonal original short line. -/
theorem generatedAxisE8OrthogonalCatalogueLabel_mem
    (a : (Fin 2 × Fin 120) ⊕ (Fin 30 × Fin 64)) :
    generatedAxisE8OrthogonalCatalogueLabel a ∈ generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
  rcases a with ⟨s, n⟩ | ⟨n, e⟩
  · rw [generatedAxisE8OrthogonalCatalogueLabel, generatedAxisE8Orthogonal_pair_mem,
      generatedAxisE8OrthogonalPairIndex_coordinates]
    exact golayOctadComplement_pair_member n
  · rw [generatedAxisE8OrthogonalCatalogueLabel, generatedAxisE8Orthogonal_octad_mem,
      generatedAxisE8OrthogonalOctadIndex_label]
    exact golayOctadComplement_octad_member n

/-- The catalogue covers every actual preferred short line orthogonal to the original section. -/
theorem generatedAxisE8OrthogonalCatalogueLabel_cover (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) :
    ∃ a : (Fin 2 × Fin 120) ⊕ (Fin 30 × Fin 64),
      generatedAxisE8OrthogonalCatalogueLabel a = r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · obtain ⟨n, hn⟩ := golayOctadComplement_pairs_cover _
      ((generatedAxisE8Orthogonal_pair_mem s p).mp hr)
    have hp : generatedAxisE8OrthogonalPairIndex n = p := by
      apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      exact (generatedAxisE8OrthogonalPairIndex_coordinates n).trans hn
    exact ⟨Sum.inl (s, n), congrArg (fun p => Sum.inl (s, p)) hp⟩
  · obtain ⟨n, hn⟩ := golayOctadComplement_octads_cover _
      ((generatedAxisE8Orthogonal_octad_mem o e).mp hr)
    have ho : generatedAxisE8OrthogonalOctadIndex n = o := by
      apply (golayOctads.orderIsoOfFin golayOctads_card).injective
      apply Subtype.ext
      exact (generatedAxisE8OrthogonalOctadIndex_label n).trans hn
    exact ⟨Sum.inr (n, e), congrArg (fun o => Sum.inr (Sum.inl (o, e))) ho⟩
  · have hz := (generatedAxisE8Orthogonal_old_mem _).mp hr 8 (by decide) (by decide)
    simp only [griessShortIntegral] at hz
    split_ifs at hz <;> norm_num at hz

/-- The2160 actual preferred complement labels have a complete original catalogue bijection. -/
def generatedAxisE8OrthogonalCatalogueEquiv :
    ((Fin 2 × Fin 120) ⊕ (Fin 30 × Fin 64)) ≃
      generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) :=
  Equiv.ofBijective
    (fun a => ⟨generatedAxisE8OrthogonalCatalogueLabel a,
      generatedAxisE8OrthogonalCatalogueLabel_mem a⟩)
    ⟨fun _ _ h => generatedAxisE8OrthogonalCatalogueLabel_injective
      (congrArg Subtype.val h), by
      rintro ⟨r, hr⟩
      obtain ⟨a, ha⟩ := generatedAxisE8OrthogonalCatalogueLabel_cover r hr
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The genuine coordinate E8 section has exactly2160 preferred orthogonal short lines. -/
theorem generatedAxisE8Orthogonal_short_lines_card :
    Nat.card (generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) = 2160 := by
  rw [← Nat.card_congr generatedAxisE8OrthogonalCatalogueEquiv]
  simp [Nat.card_eq_fintype_card]

/-- Both orientations of all actual norm-four roots orthogonal to the original section. -/
def generatedAxisE8OrthogonalSignedRoots : Set leechIntegral :=
  {u | leechSquareSum u.val = 32 ∧
    ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → u.val i = 0}

/-- The actual oriented integral vector at one signed preferred complement address. -/
def generatedAxisE8OrthogonalSignedRoot
    (a : Bool × generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) :
    leechIntegral :=
  if a.1 then -griessShortLatticeVector a.2.val else griessShortLatticeVector a.2.val

/-- Every signed address describes an original norm-four root orthogonal to the actual section. -/
theorem generatedAxisE8OrthogonalSignedRoot_mem
    (a : Bool × generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) :
    generatedAxisE8OrthogonalSignedRoot a ∈ generatedAxisE8OrthogonalSignedRoots := by
  have hr := (generatedAxisE8Orthogonal_old_mem a.2.val).mp a.2.property
  change leechSquareSum (generatedAxisE8OrthogonalSignedRoot a).val = 32 ∧ _
  unfold generatedAxisE8OrthogonalSignedRoot
  cases hb : a.1
  · simp only [Bool.false_eq_true, ite_false]
    change leechSquareSum (griessShortIntegral a.2.val) = 32 ∧ _
    exact ⟨griessShortIntegral_squareSum a.2.val, hr⟩
  · simp only [ite_true, Submodule.coe_neg]
    change leechSquareSum (-griessShortIntegral a.2.val) = 32 ∧ _
    rw [leechSquareSum_neg]
    refine ⟨griessShortIntegral_squareSum a.2.val, ?_⟩
    intro i hi0 hi1
    change -griessShortIntegral a.2.val i = 0
    rw [hr i hi0 hi1, neg_zero]

/-- Different signed addresses give different actual integral roots. -/
theorem generatedAxisE8OrthogonalSignedRoot_injective :
    Function.Injective generatedAxisE8OrthogonalSignedRoot := by
  rintro ⟨b, r⟩ ⟨c, t⟩ h
  have hc := congrArg leechReduction h
  have he : r.val = t.val := by
    apply griessShortClass_injective
    change leechReduction (griessShortLatticeVector r.val) =
      leechReduction (griessShortLatticeVector t.val)
    cases b <;> cases c <;>
      simpa only [generatedAxisE8OrthogonalSignedRoot, Bool.false_eq_true, ite_false,
        Bool.true_eq, ite_true, leechReduction_neg] using hc
  have hrt : r = t := Subtype.ext he
  subst t
  have hne : griessShortLatticeVector r.val ≠ -griessShortLatticeVector r.val := by
    intro hv
    have hz : griessShortIntegral r.val = 0 := by
      funext i
      have hi := congrArg (fun u : leechIntegral => u.val i) hv
      change griessShortIntegral r.val i = -griessShortIntegral r.val i at hi
      change griessShortIntegral r.val i = 0
      omega
    have hn := griessShortIntegral_squareSum r.val
    rw [hz] at hn
    norm_num [leechSquareSum] at hn
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · change griessShortLatticeVector r.val = -griessShortLatticeVector r.val at h
      exact False.elim (hne h)
    · change -griessShortLatticeVector r.val = griessShortLatticeVector r.val at h
      exact False.elim (hne h.symm)
    · rfl
  exact Prod.ext hbc rfl

/-- Every actual norm-four root in the orthogonal complement has a signed original address. -/
theorem generatedAxisE8OrthogonalSignedRoot_cover (u : leechIntegral)
    (hu : u ∈ generatedAxisE8OrthogonalSignedRoots) :
    ∃ a : Bool × generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)),
      generatedAxisE8OrthogonalSignedRoot a = u := by
  obtain ⟨r, hr⟩ := leechShort_catalog u hu.1
  rcases hr with hr | hr
  · have hmem : r ∈ generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
      rw [generatedAxisE8Orthogonal_old_mem]
      intro i hi0 hi1
      rw [← hr]
      exact hu.2 i hi0 hi1
    exact ⟨(false, ⟨r, hmem⟩), Subtype.ext hr.symm⟩
  · have hmem : r ∈ generatedAxisE8OrthogonalShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
      rw [generatedAxisE8Orthogonal_old_mem]
      intro i hi0 hi1
      have hi := hu.2 i hi0 hi1
      rw [hr] at hi
      exact neg_eq_zero.mp hi
    exact ⟨(true, ⟨r, hmem⟩), Subtype.ext hr.symm⟩

/-- The oriented original catalogue is a bijection onto the actual orthogonal root set. -/
def generatedAxisE8OrthogonalSignedRootEquiv :
    (Bool × generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) ≃
      generatedAxisE8OrthogonalSignedRoots :=
  Equiv.ofBijective
    (fun a => ⟨generatedAxisE8OrthogonalSignedRoot a, generatedAxisE8OrthogonalSignedRoot_mem a⟩)
    ⟨fun _ _ h => generatedAxisE8OrthogonalSignedRoot_injective (congrArg Subtype.val h), by
      rintro ⟨u, hu⟩
      obtain ⟨a, ha⟩ := generatedAxisE8OrthogonalSignedRoot_cover u hu
      exact ⟨a, Subtype.ext ha⟩⟩

/-- Exactly4320 actual oriented norm-four roots are orthogonal to the original E8 section. -/
theorem generatedAxisE8Orthogonal_signed_roots_card :
    Nat.card generatedAxisE8OrthogonalSignedRoots = 4320 := by
  rw [← Nat.card_congr generatedAxisE8OrthogonalSignedRootEquiv, Nat.card_prod,
    generatedAxisE8Orthogonal_short_lines_card]
  norm_num [Nat.card_eq_fintype_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
