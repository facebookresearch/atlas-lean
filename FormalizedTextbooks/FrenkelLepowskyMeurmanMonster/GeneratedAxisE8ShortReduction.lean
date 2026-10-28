/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityOctad

/-! All actual short vectors in the coordinate E8 section have a common target. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A weight-eight code supported in the first octad occupies every section coordinate. -/
theorem generatedE8Short_octad_coordinates (u : leechIntegral)
    (hu : generatedStandardOctadSupported u.val) (c : Fin 24 → ZMod 2)
    (hw : ∑ i, (c i).val = 8) (hcoord : ∀ i, u.val i ^ 2 = 4 * (c i).val) :
    ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2 := by
  have hz (j : Fin 16) : (c (Fin.natAdd 8 j)).val = 0 := by
    have hh := hcoord (Fin.natAdd 8 j)
    rw [hu _ (by simp)] at hh
    omega
  have ht : (∑ j : Fin 8, (c (Fin.castAdd 16 j)).val) = 8 := by
    rw [Fin.sum_univ_add (a := 8) (b := 16)] at hw
    simpa only [hz, Finset.sum_const_zero, add_zero] using hw
  have htInt : (∑ j : Fin 8, ((c (Fin.castAdd 16 j)).val : ℤ)) = 8 := by
    exact_mod_cast ht
  have hdef : (∑ j : Fin 8, (1 - ((c (Fin.castAdd 16 j)).val : ℤ))) = 0 := by
    rw [Finset.sum_sub_distrib, htInt]
    norm_num
  intro j
  have hle (k : Fin 8) : (c (Fin.castAdd 16 k)).val ≤ 1 := by
    have hh := ZMod.val_lt (c (Fin.castAdd 16 k))
    omega
  have hb := Finset.single_le_sum
    (fun k _ => show (0 : ℤ) ≤ 1 - (c (Fin.castAdd 16 k)).val by
      have hh := hle k
      omega) (Finset.mem_univ j)
  rw [hdef] at hb
  have hcj : (c (Fin.castAdd 16 j)).val = 1 := by
    have hh := hle j
    omega
  have hs : u.val (Fin.castAdd 16 j) ^ 2 = (2 : ℤ) ^ 2 := by
    simpa [hcj] using hcoord (Fin.castAdd 16 j)
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).symm

/-- Section-preserving concrete generators normalize every short vector in this E8 section. -/
theorem generatedE8Short_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 32) (hu : generatedStandardOctadSupported u.val) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  rcases leechShort_even_shapes u hs 8 (hu 8 (by decide)) with
    ⟨i, j, hij, hi, hj⟩ | ⟨c, _, hw, hcoord⟩
  · exact generatedE8Short_pair_reduction u hs hu i j hij hi hj
  · obtain ⟨d, hd⟩ := leechShort_standard_octad_signs u
      (generatedE8Short_octad_coordinates u hu c hw hcoord) hu
    let w := leechIntegralAction (golaySignIsometry d) u
    let x := leechIntegralAction co1XiIsometry w
    have hx : x.val = fun i : Fin 24 => if i = 0 ∨ i = 4 then (-4 : ℤ) else 0 := by
      have hh := co1Xi_integral_double w
      rw [hd, leechShort_octad_xi_certificate] at hh
      funext i
      have he := congrFun hh i
      change 2 * x.val i = 2 * (if i = 0 ∨ i = 4 then (-4 : ℤ) else 0) at he
      omega
    have hxs : leechSquareSum x.val = 32 := by
      dsimp [x, w]
      rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum, hs]
    have hxu : generatedStandardOctadSupported x.val :=
      (generatedStandardOctadPreserves_xi w).mpr
        ((generatedStandardOctadPreserves_sign d u).mpr hu)
    obtain ⟨e, he, hpres, hpair⟩ := generatedE8Short_pair_reduction x hxs hxu
      0 4 (by decide) (by simp [hx]) (by simp [hx])
    refine ⟨e * co1XiIsometry * golaySignIsometry d,
      leechConcreteGeneratorSubgroup.mul_mem
        (leechConcreteGeneratorSubgroup.mul_mem he co1XiIsometry_mem_concrete)
        (golaySignIsometry_mem_concrete d),
      generatedStandardOctadPreserves_mul _ _
        (generatedStandardOctadPreserves_mul _ _ hpres generatedStandardOctadPreserves_xi)
        (generatedStandardOctadPreserves_sign d), ?_⟩
    simpa only [map_mul, LinearEquiv.mul_apply] using hpair

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
