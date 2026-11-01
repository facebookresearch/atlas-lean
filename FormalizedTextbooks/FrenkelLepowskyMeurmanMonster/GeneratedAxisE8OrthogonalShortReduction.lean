/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8OrthogonalShortCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityOctad

/-! Genuine section-preserving generators normalize the actual orthogonal short roots. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Every original Golay sign preserves the entire original octad-three coordinate section. -/
theorem generatedAxisE8Orthogonal_sign_preserves (d : golayCode) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad)
      (golaySignIsometry d) := by
  intro u
  rw [leechIntegralAction_golaySign]
  constructor
  · intro h i hi
    have he := h i hi
    change (if d.val i = 0 then u.val i else -u.val i) = 0 at he
    split_ifs at he <;> simpa using he
  · intro h i hi
    change (if d.val i = 0 then u.val i else -u.val i) = 0
    rw [h i hi]
    split_ifs <;> rfl

/-- A genuine original word preserving the physical octad fixes its full integral section. -/
theorem generatedAxisE8Orthogonal_permutation_preserves (p : golayAutomorphismSubgroup)
    (hp : ∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
      (8 ≤ i.val ∧ i.val < 16)) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad)
      (golayPermutationIsometry p) := by
  have hz (i : Fin 24) : golayOctadWord generatedOctadBasisOctad i = 0 ↔
      ¬ (8 ≤ i.val ∧ i.val < 16) := by
    rw [generatedAxisE8Orthogonal_old_word]
    simp
  intro u
  rw [leechIntegralAction_golayPermutation]
  constructor
  · intro h i hi
    have hpi : golayOctadWord generatedOctadBasisOctad (p.val i) = 0 :=
      (hz _).mpr ((not_congr (hp i)).mpr ((hz i).mp hi))
    have he := h (p.val i) hpi
    simpa only [golayIntegerPermute, p.val.symm_apply_apply] using he
  · intro h i hi
    have hpi : golayOctadWord generatedOctadBasisOctad (p.val.symm i) = 0 := by
      apply (hz _).mpr
      have hh := hp (p.val.symm i)
      rw [p.val.apply_symm_apply] at hh
      exact (not_congr hh).mp ((hz i).mp hi)
    exact h (p.val.symm i) hpi

private theorem xi_forward (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedOctadBasisOctad) u.val) :
    generatedOctadSupported (golayOctadWord generatedOctadBasisOctad)
      (leechIntegralAction co1XiIsometry u).val := by
  intro i hi
  have hout : ¬ (8 ≤ i.val ∧ i.val < 16) := by
    rw [generatedAxisE8Orthogonal_old_word] at hi
    simpa using hi
  have hnum : (co1XiNumerator *ᵥ u.val) i = 0 := by
    change ∑ j, co1XiNumerator i j * u.val j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : 8 ≤ j.val ∧ j.val < 16
    · have hb : i.val / 4 ≠ j.val / 4 := by omega
      simp [co1XiNumerator, hb]
    · rw [hu j (by rw [generatedAxisE8Orthogonal_old_word]; simp [hj]), mul_zero]
  have hd := congrArg (fun v : Fin 24 → ℤ => v i) (co1Xi_integral_double u)
  change 2 * (leechIntegralAction co1XiIsometry u).val i = _ at hd
  rw [hnum] at hd
  omega

/-- The original Xi block matrix preserves the entire actual octad-three section. -/
theorem generatedAxisE8Orthogonal_xi_preserves :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) co1XiIsometry := by
  intro u
  constructor
  · intro h
    have h1 := xi_forward _ h
    have h2 := xi_forward _ h1
    have he : leechIntegralAction co1XiIsometry
        (leechIntegralAction co1XiIsometry (leechIntegralAction co1XiIsometry u)) = u := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
      rw [show co1XiIsometry * co1XiIsometry * co1XiIsometry = co1XiIsometry ^ 3 by
        simp [pow_succ, mul_assoc], co1XiIsometry_cube, map_one]
      rfl
    rw [he] at h2
    exact h2
  · exact xi_forward u

/-- Products of genuine section-preserving isometries preserve the same entire section. -/
theorem generatedAxisE8Orthogonal_preserves_mul (g h : leechIsomSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) g)
    (hh : generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) h) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) (g * h) := by
  intro u
  rw [map_mul, LinearEquiv.mul_apply]
  exact (hg _).trans (hh u)

private theorem pair_reduction_ordered (u : leechIntegral)
    (hs : leechSquareSum u.val = 32)
    (hu : ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → u.val i = 0)
    (a b : Fin 24) (hab : a < b) (ha : (u.val a).natAbs = 4)
    (hb : (u.val b).natAbs = 4) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  have hmem : (a, b) ∈ golayOctadComplementPairs := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, ?_, ?_⟩
    · intro hi
      rw [hu a hi.1 hi.2] at ha
      norm_num at ha
    · intro hi
      rw [hu b hi.1 hi.2] at hb
      norm_num at hb
  obtain ⟨p, hp, hpair⟩ := golayOctadComplement_pair_from_initial (a, b) hmem
  let v := leechIntegralAction (golayPermutationIsometry p⁻¹) u
  have hv0 : (v.val 0).natAbs = 4 := by
    change ((leechIntegralAction (golayPermutationIsometry p⁻¹) u).val 0).natAbs = 4
    rw [leechIntegralAction_golayPermutation]
    change (u.val (p.val 0)).natAbs = 4
    rcases hpair with ⟨h0, _⟩ | ⟨h0, _⟩ <;> rw [h0] <;> assumption
  have hv1 : (v.val 1).natAbs = 4 := by
    change ((leechIntegralAction (golayPermutationIsometry p⁻¹) u).val 1).natAbs = 4
    rw [leechIntegralAction_golayPermutation]
    change (u.val (p.val 1)).natAbs = 4
    rcases hpair with ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> assumption
  obtain ⟨d, hd⟩ := leechNormEight_four_signs
    (fun j : Fin 4 => v.val (Fin.castAdd 20 j)) ![4, 4, v.val 2, v.val 3] (by
      intro j
      fin_cases j <;> simp [hv0, hv1])
  have hfirst : (leechIntegralAction (golaySignIsometry d) v).val 0 = 4 := by
    rw [leechIntegralAction_golaySign]
    exact hd 0
  have hsecond : (leechIntegralAction (golaySignIsometry d) v).val 1 = 4 := by
    rw [leechIntegralAction_golaySign]
    exact hd 1
  have hn : leechSquareSum (leechIntegralAction (golaySignIsometry d) v).val = 32 := by
    dsimp [v]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum, hs]
  have hpres : generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad)
      (golayPermutationIsometry p⁻¹) := by
    apply generatedAxisE8Orthogonal_permutation_preserves
    intro i
    have hh := hp (p.val.symm i)
    rw [p.val.apply_symm_apply] at hh
    exact hh.symm
  refine ⟨golaySignIsometry d * golayPermutationIsometry p⁻¹,
    leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
      (golayPermutationIsometry_mem_concrete p⁻¹),
    generatedAxisE8Orthogonal_preserves_mul _ _ (generatedAxisE8Orthogonal_sign_preserves d)
      hpres, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply]
  exact leechShort_eq_pair_of_first _ hn hfirst hsecond

/-- Any actual pair root outside the section reaches the same pair by genuine preserving words. -/
theorem generatedAxisE8Orthogonal_pair_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 32)
    (hu : ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → u.val i = 0)
    (a b : Fin 24) (hab : a ≠ b) (ha : (u.val a).natAbs = 4)
    (hb : (u.val b).natAbs = 4) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  by_cases h : a < b
  · exact pair_reduction_ordered u hs hu a b h ha hb
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)
    exact pair_reduction_ordered u hs hu b a hba hb ha

private theorem initial_code :
    (golayCodeLabelEquiv (2063 : Fin 4096)).val = golayStandardOctad := by
  decide +kernel

private theorem octad_word_to_standard (u : leechIntegral)
    (hu : ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → u.val i = 0)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8)
    (hcoord : ∀ i, u.val i ^ 2 = 4 * (c i).val) :
    ∃ p : golayAutomorphismSubgroup,
      (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
        (8 ≤ i.val ∧ i.val < 16)) ∧ golayPermute p.val c = golayStandardOctad := by
  let d := golayCodeLabelEquiv.symm ⟨c, hc⟩
  have hd : (golayCodeLabelEquiv d).val = c :=
    congrArg Subtype.val (golayCodeLabelEquiv.apply_symm_apply ⟨c, hc⟩)
  have hmem : d ∈ golayOctadComplementOctads := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · change (∑ i : Fin 24,
        if (golayEncodedMask d.val).testBit i.val then 1 else 0) = 8
      simp_rw [← golayLabelEncoder_match]
      change (∑ i : Fin 24, ((golayCodeLabelEquiv d).val i).val) = 8
      rw [hd]
      exact hw
    · intro j
      let i : Fin 24 := ⟨8 + j.val, by omega⟩
      have hh := hcoord i
      rw [hu i (by dsimp [i]; omega) (by dsimp [i]; omega)] at hh
      have hz : ((golayCodeLabelEquiv d).val i).val = 0 := by rw [hd]; omega
      change (golayEncoder (golayLabelCoefficients d) i).val = 0 at hz
      rw [golayLabelEncoder_match] at hz
      cases hb : (golayEncodedMask d.val).testBit i.val
      · rfl
      · simp [hb] at hz
  obtain ⟨p, hpres, hp⟩ := golayOctadComplement_octad_from_initial d hmem
  refine ⟨p⁻¹, ?_, ?_⟩
  · intro i
    have hh := hpres (p.val.symm i)
    rw [p.val.apply_symm_apply] at hh
    exact hh.symm
  · have hh := congrArg (golayPermute p.val⁻¹) hp
    rw [golayPermute_inv, initial_code, hd] at hh
    exact hh.symm

/-- The actual outside octad family reaches the actual outside pair family by the original Xi. -/
theorem generatedAxisE8Orthogonal_octad_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 32)
    (hu : ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → u.val i = 0)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8)
    (hcoord : ∀ i, u.val i ^ 2 = 4 * (c i).val) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  obtain ⟨p, hpres, hp⟩ := octad_word_to_standard u hu c hc hw hcoord
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv (i : Fin 24) : v.val i ^ 2 = 4 * (golayStandardOctad i).val := by
    have he := congrFun hp i
    change c (p.val.symm i) = golayStandardOctad i at he
    change (leechIntegralAction (golayPermutationIsometry p) u).val i ^ 2 = _
    rw [leechIntegralAction_golayPermutation]
    simpa only [golayIntegerPermute, he] using hcoord (p.val.symm i)
  have hfirst (j : Fin 8) : v.val (Fin.castAdd 16 j) = -2 ∨
      v.val (Fin.castAdd 16 j) = 2 := by
    have he : v.val (Fin.castAdd 16 j) ^ 2 = (2 : ℤ) ^ 2 := by
      simpa only [golayStandardOctad, Fin.val_castAdd, j.isLt, ite_true,
        show (1 : ZMod 2).val = 1 by decide, Nat.cast_one, mul_one,
        show (2 : ℤ) ^ 2 = 4 by decide] using hv (Fin.castAdd 16 j)
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp he).symm
  have hzero (i : Fin 24) (hi : 8 ≤ i.val) : v.val i = 0 := by
    have hh := hv i
    simp [golayStandardOctad, show ¬ i.val < 8 by omega] at hh
    nlinarith
  obtain ⟨d, hd⟩ := leechShort_standard_octad_signs v hfirst hzero
  let w := leechIntegralAction (golaySignIsometry d) v
  let x := leechIntegralAction co1XiIsometry w
  have hx : x.val = fun i : Fin 24 => if i = 0 ∨ i = 4 then (-4 : ℤ) else 0 := by
    have hh := co1Xi_integral_double w
    rw [hd, leechShort_octad_xi_certificate] at hh
    funext i
    have he := congrFun hh i
    change 2 * x.val i = 2 * (if i = 0 ∨ i = 4 then (-4 : ℤ) else 0) at he
    omega
  have hxs : leechSquareSum x.val = 32 := by
    dsimp [x, w, v]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum,
      leechIntegralAction_squareSum, hs]
  have hxu : ∀ i : Fin 24, 8 ≤ i.val → i.val < 16 → x.val i = 0 := by
    intro i hi0 _
    have hi : i ≠ 0 ∧ i ≠ 4 := by constructor <;> intro h <;> subst i <;> omega
    simp [hx, hi]
  obtain ⟨e, he, hep, hpair⟩ := generatedAxisE8Orthogonal_pair_reduction x hxs hxu
    0 4 (by decide) (by simp [hx]) (by simp [hx])
  refine ⟨e * co1XiIsometry * golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem
      (leechConcreteGeneratorSubgroup.mul_mem
        (leechConcreteGeneratorSubgroup.mul_mem he co1XiIsometry_mem_concrete)
        (golaySignIsometry_mem_concrete d)) (golayPermutationIsometry_mem_concrete p),
    generatedAxisE8Orthogonal_preserves_mul _ _
      (generatedAxisE8Orthogonal_preserves_mul _ _
        (generatedAxisE8Orthogonal_preserves_mul _ _ hep
          generatedAxisE8Orthogonal_xi_preserves)
        (generatedAxisE8Orthogonal_sign_preserves d))
      (generatedAxisE8Orthogonal_permutation_preserves p hpres), ?_⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using hpair

/-- Every genuine norm-four root orthogonal to the original section has the same concrete target. -/
theorem generatedAxisE8Orthogonal_short_reduction (u : leechIntegral)
    (hu : u ∈ generatedAxisE8OrthogonalSignedRoots) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  rcases leechShort_even_shapes u hu.1 8 (hu.2 8 (by decide) (by decide)) with
    ⟨a, b, hab, ha, hb⟩ | ⟨c, hc, hw, hcoord⟩
  · exact generatedAxisE8Orthogonal_pair_reduction u hu.1 hu.2 a b hab ha hb
  · exact generatedAxisE8Orthogonal_octad_reduction u hu.1 hu.2 c hc hw hcoord

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
