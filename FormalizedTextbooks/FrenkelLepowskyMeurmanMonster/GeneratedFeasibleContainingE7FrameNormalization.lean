/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthInputRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport

/-! Genuine positive root normalization perpendicular to an actual coordinate frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- An actual section root perpendicular to the third frame has precisely two absolute-four
coordinates, neither of them the frame coordinate. -/
theorem generatedFeasibleContainingE7_frame_perpendicular_pair (u : leechIntegral)
    (hs : leechSquareSum u.val = 32) (hu : generatedStandardOctadSupported u.val)
    (h2 : u.val 2 = 0) :
    ∃ i j : Fin 24, i ≠ j ∧ i.val < 8 ∧ j.val < 8 ∧ i ≠ 2 ∧ j ≠ 2 ∧
      (u.val i).natAbs = 4 ∧ (u.val j).natAbs = 4 := by
  rcases leechShort_even_shapes u hs 8 (hu 8 (by decide)) with
    ⟨i, j, hij, hi, hj⟩ | ⟨c, _, hw, hc⟩
  · refine ⟨i, j, hij, ?_, ?_, ?_, ?_, hi, hj⟩
    · by_contra h
      rw [hu i (by omega)] at hi
      norm_num at hi
    · by_contra h
      rw [hu j (by omega)] at hj
      norm_num at hj
    · intro h
      subst i
      rw [h2] at hi
      norm_num at hi
    · intro h
      subst j
      rw [h2] at hj
      norm_num at hj
  · have h := generatedE8Short_octad_coordinates u hu c hw hc (2 : Fin 8)
    change u.val 2 = -2 ∨ u.val 2 = 2 at h
    rw [h2] at h
    norm_num at h

private theorem positive_minus_pair_of_first (u : Fin 24 → ℤ)
    (hs : leechSquareSum u = 32) (h0 : u 0 = 4) (h1 : u 1 = -4) :
    u = griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  have hr : ∑ i : Fin 22, u i.succ.succ ^ 2 = 0 := by
    change (∑ i : Fin 24, u i ^ 2) = 32 at hs
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, h0] at hs
    change 4 ^ 2 + (u 1 ^ 2 + ∑ i : Fin 22, u i.succ.succ ^ 2) = 32 at hs
    rw [h1] at hs
    linarith
  have hz (i : Fin 22) : u i.succ.succ = 0 := by
    have hb := Finset.single_le_sum (fun j _ => sq_nonneg (u j.succ.succ))
      (Finset.mem_univ i)
    rw [hr] at hb
    nlinarith
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simpa [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates] using h0
  · simpa [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates] using h1
  · have hk : k.succ.succ ≠ (1 : Fin 24) := by
      intro h
      have he := congrArg Fin.val h
      change k.val + 1 + 1 = 1 at he
      omega
    simpa [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates,
      Fin.succ_ne_zero, hk] using hz k

/-- Every actual section root perpendicular to the third frame reaches the positive original
first root by a genuine section-preserving monomial which fixes that frame pointwise. -/
theorem generatedFeasibleContainingE7_frame_root_normalize (u : leechIntegral)
    (hs : leechSquareSum u.val = 32) (hu : generatedStandardOctadSupported u.val)
    (h2 : u.val 2 = 0) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      generatedStandardOctadPreserves e ∧
      leechIntegralAction e (leechCoordinateFrameLattice 2) = leechCoordinateFrameLattice 2 ∧
      leechIntegralAction e u =
        griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  obtain ⟨i, j, hij, hii, hji, hi2, hj2, hi, hj⟩ :=
    generatedFeasibleContainingE7_frame_perpendicular_pair u hs hu h2
  let a : Fin 3 → Fin 8 := ![⟨i.val, hii⟩, ⟨j.val, hji⟩, 2]
  have ha : Function.Injective a := by
    intro x y h
    have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi2v : i.val ≠ 2 := fun h => hi2 (Fin.ext h)
    have hj2v : j.val ≠ 2 := fun h => hj2 (Fin.ext h)
    fin_cases x <;> fin_cases y <;> norm_num [a, Fin.ext_iff] at h ⊢ <;> omega
  obtain ⟨f8, hf8, hfa⟩ := generatedE8Short_extend_tuple (by decide : 3 < 8) a ha
  let f : Fin 4 → Fin 24 := fun k => Fin.castAdd 16 (f8 k)
  have hf : Function.Injective f := by
    intro x y h
    exact hf8 (Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  have hfi : f 0 = i := by
    apply Fin.ext
    simpa [f, a] using congrArg (fun k : Fin 8 => k.val) (hfa 0)
  have hfj : f 1 = j := by
    apply Fin.ext
    simpa [f, a] using congrArg (fun k : Fin 8 => k.val) (hfa 1)
  have hf2 : f 2 = 2 := by
    apply Fin.ext
    simpa [f, a] using congrArg (fun k : Fin 8 => k.val) (hfa 2)
  obtain ⟨p, hpres, hp⟩ := generatedStandardOctad_prepare_four f hf
    (fun k => (f8 k).isLt)
  have hp2 : p.val 2 = 2 := by simpa [hf2] using hp 2
  obtain ⟨d, hd⟩ := leechNormEight_four_signs ![u.val i, u.val j, 8, 0]
    ![4, -4, 8, 0] (by intro k; fin_cases k <;> simp [hi, hj])
  have hd2 : d.val 2 = 0 := by
    have h := hd 2
    change (if d.val 2 = 0 then (8 : ℤ) else -8) = 8 at h
    by_contra hn
    rw [ite_eq_right hn] at h
    norm_num at h
  let e := golaySignIsometry d * golayPermutationIsometry p
  have hrow (k : Fin 4) :
      (leechIntegralAction e u).val (Fin.castAdd 20 k) =
        if d.val (Fin.castAdd 20 k) = 0 then u.val (f k) else -u.val (f k) := by
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    have hpk : p.val.symm (Fin.castAdd 20 k) = f k := by
      rw [← hp k, p.val.symm_apply_apply]
    simp only [golayIntegerSign, golayIntegerPermute, hpk]
  refine ⟨e, ⟨d, p, rfl⟩,
    generatedStandardOctadPreserves_mul _ _ (generatedStandardOctadPreserves_sign d)
      (generatedStandardOctadPreserves_permutation p hpres), ?_, ?_⟩
  · apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext k
    change golayIntegerSign d.val
      (golayIntegerPermute p.val (Pi.single (2 : Fin 24) (8 : ℤ))) k =
        (Pi.single (2 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) k
    have hpk : p.val.symm k = 2 ↔ k = 2 := by rw [p.val.symm_apply_eq, hp2]
    by_cases hk : k = 2
    · subst k
      simp [golayIntegerSign, golayIntegerPermute, Pi.single_apply, hpk, hd2]
    · simp [golayIntegerSign, golayIntegerPermute, hpk, hk]
  · apply Subtype.ext
    apply positive_minus_pair_of_first
    · rw [leechIntegralAction_squareSum, hs]
    · have hh := hd 0
      change (if d.val 0 = 0 then u.val i else -u.val i) = 4 at hh
      rw [show (leechIntegralAction e u).val 0 = _ from hrow 0, hfi]
      exact hh
    · have hh := hd 1
      change (if d.val 1 = 0 then u.val j else -u.val j) = -4 at hh
      rw [show (leechIntegralAction e u).val 1 = _ from hrow 1, hfj]
      exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
