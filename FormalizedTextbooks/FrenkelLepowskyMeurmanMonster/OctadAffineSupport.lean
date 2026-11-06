/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual physical affine support of a three-octad cubic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadUnionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPhysicalSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The actual octad word vanishes off its physical support. -/
theorem golayOctadWord_supported (o : Fin 759) (i : Fin 24)
    (hi : i ∉ golayOctadSupport o) : golayOctadWord o i = 0 := by
  by_contra h
  exact hi ((golayOctadWord_ne_zero_iff o i).mp h)

/-- Every actual octad word is nonzero. -/
theorem golayOctadWord_ne_zero (o : Fin 759) : golayOctadWord o ≠ 0 := by
  intro h
  have hw := golayOctadWord_weight o
  simp [h] at hw

/-- The actual preferred negative pattern vanishes outside the octad support. -/
theorem griessOctadNegative_supported (o : Fin 759) (e : Fin 64) (i : Fin 24)
    (hi : i ∉ golayOctadSupport o) :
    integerParity (griessOctadNegativeInteger o e) i = 0 := by
  rw [griessOctadNegative_embedding]
  apply octadPhysicalEmbedding_supported
  simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
    Finset.mem_univ, true_and] using hi

/-- In a four-point octad intersection, the actual cubic syndrome condition
is exactly an affine coset of the four codewords supported on the union. -/
theorem griessOctad_triple_syndrome_four (o p u : Fin 759) (e f g : Fin 64)
    (hop : o ≠ p) (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    let n := integerParity (griessOctadNegativeInteger o e) +
      integerParity (griessOctadNegativeInteger p f) +
      integerParity (griessOctadNegativeInteger u g)
    let t := fun i => golayOctadWord o i * golayOctadWord p i
    golaySyndrome n = golaySyndrome t ↔
      n+t = 0 ∨ n+t = golayOctadWord o ∨ n+t = golayOctadWord p ∨
        n+t = golayOctadWord o + golayOctadWord p := by
  dsimp only
  let S := golayOctadSupport o ∪ golayOctadSupport p
  have hS : S.card ≤ 12 := by rw [golayOctad_union_card o p hfour]
  have hs (i : Fin 24) (hi : i ∉ S) :
      i ∉ golayOctadSupport o ∧ i ∉ golayOctadSupport p := by
    simpa only [S, Finset.mem_union, not_or] using hi
  apply golaySyndrome_supported_twelve_affine S hS _ _ _ _
    (golayOctadWord_mem_code o) (golayOctadWord_mem_code p)
    (golayOctadWord_ne_zero o) (golayOctadWord_ne_zero p)
    ((golayOctadWord_injective).ne hop)
  · intro i hi
    exact golayOctadWord_supported o i (hs i hi).1
  · intro i hi
    exact golayOctadWord_supported p i (hs i hi).2
  · intro i hi
    have huo : i ∉ golayOctadSupport u := by
      have hz : golayOctadWord u i = 0 := by
        rw [hu]
        simp [golayOctadWord_supported o i (hs i hi).1,
          golayOctadWord_supported p i (hs i hi).2]
      simp only [← golayOctadWord_ne_zero_iff, hz, ne_eq, not_true_eq_false,
        not_false_eq_true]
    simp only [Pi.add_apply, griessOctadNegative_supported o e i (hs i hi).1,
      griessOctadNegative_supported p f i (hs i hi).2,
      griessOctadNegative_supported u g i huo, zero_add]
  · intro i hi
    simp [golayOctadWord_supported o i (hs i hi).1]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
