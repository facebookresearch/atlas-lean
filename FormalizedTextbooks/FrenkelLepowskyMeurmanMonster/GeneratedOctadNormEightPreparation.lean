/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightPreservation

/-! Actual norm-eight preparation stays inside the coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both nonterminal section shapes have a nonzero target tetrad. -/
theorem generatedStandardOctad_target_nonzero (s : Fin 8) (hs : s = 1 ∨ s = 2)
    (j : Fin 4) : (leechNormEightTargetRows s j).natAbs ≠ 0 := by
  rcases hs with rfl | rfl <;> revert j <;> decide +kernel

/-- Preparation of the two nonterminal shapes uses only section-preserving generators. -/
theorem generatedStandardOctad_normEight_preparation (u : leechIntegral) (s : Fin 8)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts s)
    (hu : generatedStandardOctadSupported u.val) (hs : s = 1 ∨ s = 2) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) =
        leechNormEightTargetRows s j := by
  obtain ⟨f, hf, habs⟩ := leechNormEight_select_target_coordinates u.val s hshape
  have hin (j : Fin 4) : (f j).val < 8 := by
    by_contra hn
    have hz := hu (f j) (by omega)
    have he := habs j
    rw [hz, Int.natAbs_zero] at he
    exact generatedStandardOctad_target_nonzero s hs j he.symm
  obtain ⟨p, hp, hpf⟩ := generatedStandardOctad_prepare_four f hf hin
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j))
    (leechNormEightTargetRows s) habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
      (golayPermutationIsometry_mem_concrete p),
    generatedStandardOctadPreserves_mul _ _ (generatedStandardOctadPreserves_sign d)
      (generatedStandardOctadPreserves_permutation p hp), ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hpf j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

/-- The terminal coordinate shape can also be normalized without leaving the section. -/
theorem generatedStandardOctad_normEight_terminal (u : leechIntegral)
    (hs : leechSquareSum u.val = 64) (hu : generatedStandardOctadSupported u.val)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts 0) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      (leechIntegralAction e u).val = Pi.single 0 8 := by
  classical
  have hc : (Finset.univ.filter (fun i => (u.val i).natAbs = 8)).card = 1 := by
    have he := congrFun hshape 8
    exact he
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega :
    0 < (Finset.univ.filter (fun i => (u.val i).natAbs = 8)).card)
  have hui : (u.val i).natAbs = 8 := (Finset.mem_filter.mp hi).2
  have hin : i.val < 8 := by
    by_contra hn
    rw [hu i (by omega), Int.natAbs_zero] at hui
    omega
  let i8 : Fin 8 := ⟨i.val, hin⟩
  let a : Fin 4 → Fin 24 := fun j =>
    Fin.castAdd 16 (Equiv.swap (0 : Fin 8) i8 (Fin.castAdd 4 j))
  have ha : Function.Injective a := by
    intro j k h
    have he := (Equiv.swap (0 : Fin 8) i8).injective
      (Fin.ext (congrArg (fun x : Fin 24 => x.val) h))
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) he)
  obtain ⟨p, hp, hpa⟩ := generatedStandardOctad_prepare_four a ha
    (fun j => (Equiv.swap (0 : Fin 8) i8 (Fin.castAdd 4 j)).isLt)
  have ha0 : a 0 = i := by
    change Fin.castAdd 16 (Equiv.swap (0 : Fin 8) i8 0) = i
    rw [Equiv.swap_apply_left]
    exact Fin.ext rfl
  have hpi : p.val.symm 0 = i := by
    have he : p.val i = 0 := by
      have he' := hpa 0
      change p.val (a 0) = 0 at he'
      rwa [ha0] at he'
    rw [← he, p.val.symm_apply_apply]
  have hfirst : (leechIntegralAction (golayPermutationIsometry p) u).val 0 = u.val i := by
    rw [leechIntegralAction_golayPermutation]
    exact congrArg u.val hpi
  have hui' : u.val i = 8 ∨ u.val i = -8 := by
    have he : (u.val i).natAbs = (8 : ℤ).natAbs := hui
    exact Int.natAbs_eq_natAbs_iff.mp he
  rcases hui' with he | he
  · refine ⟨golayPermutationIsometry p, golayPermutationIsometry_mem_concrete p,
      generatedStandardOctadPreserves_permutation p hp,
      leechNormEight_eq_axis_of_first _ ?_ (hfirst.trans he)⟩
    rw [leechIntegralAction_squareSum, hs]
  · let d : golayCode := ⟨golayEncoder (Pi.single 11 1), ⟨Pi.single 11 1, rfl⟩⟩
    refine ⟨golaySignIsometry d * golayPermutationIsometry p,
      leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
        (golayPermutationIsometry_mem_concrete p),
      generatedStandardOctadPreserves_mul _ _ (generatedStandardOctadPreserves_sign d)
        (generatedStandardOctadPreserves_permutation p hp),
      leechNormEight_eq_axis_of_first _ ?_ ?_⟩
    · rw [leechIntegralAction_squareSum, hs]
    · rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign]
      change (if golayEncoder (Pi.single 11 1) 0 = 0 then _ else _) = 8
      rw [golay_all_one]
      simp only [one_ne_zero, ↓reduceIte, hfirst, he]
      norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
