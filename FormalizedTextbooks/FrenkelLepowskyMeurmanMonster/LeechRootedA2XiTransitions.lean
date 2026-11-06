/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Literal transitions of the original Xi matrix between rooted short families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A genuine pair-root vector with prescribed physical coordinates and sign. -/
theorem leechRootedA2_pair_mem (i j : Fin 24) (hij : i < j) (s : Fin 2) :
    (fun k => 4 * (if k = i then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) * (if k = j then 1 else 0)) ∈ leechIntegral := by
  let q : griessCoordinatePairs := ⟨(i, j), by simpa only [griessCoordinatePairs,
    Finset.mem_filter, Finset.mem_univ, true_and] using hij⟩
  let p := griessCoordinatePairEquiv.symm q
  have hp : griessCoordinatePair p = (i, j) :=
    congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply q)
  simpa only [griessShortIntegral, hp] using griessShortIntegral_mem (Sum.inl (s, p))

/-- The difference of lower tetrad coordinates1 and2 is fixed by the actual Xi matrix. -/
def leechRootedA2XiRoot : leechIntegral :=
  ⟨fun k => 4 * (if k = 1 then 1 else 0) - 4 * (if k = 2 then 1 else 0),
    by simpa only [ite_true, neg_mul, sub_eq_add_neg] using
      leechRootedA2_pair_mem 1 2 (by decide +kernel) 0⟩

/-- An integer numerator equality determines the original Xi integral action. -/
theorem leechRootedA2Xi_image_of_double (u v : leechIntegral)
    (h : co1XiNumerator *ᵥ u.val = (2 : ℕ) • v.val) :
    leechIntegralAction co1XiIsometry u = v := by
  apply Subtype.ext
  funext i
  have he := congrFun ((co1Xi_integral_double u).trans h) i
  simp only [Pi.smul_apply, nsmul_eq_mul] at he
  omega

/-- The exact source Xi action fixes the actual difference root. -/
theorem leechRootedA2XiRoot_fixed :
    leechIntegralAction co1XiIsometry leechRootedA2XiRoot = leechRootedA2XiRoot := by
  apply leechRootedA2Xi_image_of_double
  decide +kernel

/-- An actual pair short vector neighboring the Xi-fixed difference root. -/
def leechRootedA2XiPair : leechIntegral :=
  ⟨fun k => 4 * (if k = 1 then 1 else 0) + 4 * (if k = 4 then 1 else 0),
    by simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using
      leechRootedA2_pair_mem 1 4 (by decide +kernel) 1⟩

/-- The first Xi transition has eight absolute-two coordinates. -/
def leechRootedA2XiPairOctad : Fin 24 → ℤ :=
  ![2, 2, -2, -2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Literal integer coordinates of the actual pair-to-octad source action. -/
theorem leechRootedA2XiPair_image :
    (leechIntegralAction co1XiIsometry leechRootedA2XiPair).val =
      leechRootedA2XiPairOctad := by
  have h : co1XiNumerator *ᵥ leechRootedA2XiPair.val =
      (2 : ℕ) • leechRootedA2XiPairOctad := by decide +kernel
  funext i
  have he := congrFun ((co1Xi_integral_double leechRootedA2XiPair).trans h) i
  simp only [Pi.smul_apply, nsmul_eq_mul] at he
  omega

/-- The actual sorted octad selected by original Golay code3854. -/
noncomputable def leechRootedA2XiOctadIndex : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨(⟨3854, by decide⟩ : Fin 4096), by decide +kernel⟩

/-- The selected original code label is retained exactly. -/
theorem leechRootedA2XiOctadIndex_label :
    golayOctadLabel leechRootedA2XiOctadIndex = 3854 := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨(⟨3854, by decide⟩ : Fin 4096), by decide +kernel⟩)

/-- Literal increasing coordinates of the selected octad. -/
def leechRootedA2XiOctadPositions : Fin 8 → Fin 24 := ![0, 1, 2, 4, 8, 15, 18, 21]

/-- The original sorted octad coordinate map is the displayed literal map. -/
theorem leechRootedA2XiOctadIndex_coordinate (k : Fin 8) :
    golayOctadCoordinate leechRootedA2XiOctadIndex k = leechRootedA2XiOctadPositions k := by
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel leechRootedA2XiOctadIndex).val)
  let e := t.orderIsoOfFin (golayOctad_support_card leechRootedA2XiOctadIndex)
  have hm : ∀ k : Fin 8, (golayEncodedMask 3854).testBit
      (leechRootedA2XiOctadPositions k).val = true := by decide +kernel
  let v : t := ⟨leechRootedA2XiOctadPositions k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      leechRootedA2XiOctadIndex_label]
    exact hm k⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport (golayEncodedMask
      (golayOctadLabel leechRootedA2XiOctadIndex).val)).sort.idxOf
        (leechRootedA2XiOctadPositions k) = k.val
    rw [leechRootedA2XiOctadIndex_label]
    change (golayMaskSupport (golayEncodedMask 3854)).sort.idxOf
      (leechRootedA2XiOctadPositions k) = k.val
    have hs : (golayMaskSupport (golayEncodedMask 3854)).sort =
        List.ofFn leechRootedA2XiOctadPositions := by
      apply ((golayMaskSupport (golayEncodedMask 3854)).sortedLT_sort).eq_of_mem_iff
        (by decide +kernel)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ i : Fin 24, i ∈ golayMaskSupport (golayEncodedMask 3854) ↔
          i ∈ List.ofFn leechRootedA2XiOctadPositions := by decide +kernel
      exact hc i
    rw [hs]
    have hi : ∀ k : Fin 8, (List.ofFn leechRootedA2XiOctadPositions).idxOf
        (leechRootedA2XiOctadPositions k) = k.val := by decide +kernel
    exact hi k
  exact congrArg Subtype.val (show e k = v by rw [← he, e.apply_symm_apply])

/-- The original selected octad has signs negative at2 and18. -/
noncomputable def leechRootedA2XiOctad : leechIntegral :=
  griessShortLatticeVector (Sum.inr (Sum.inl (leechRootedA2XiOctadIndex, 4)))

/-- Literal coordinates certified against the original sorted octad and sign decoder. -/
theorem leechRootedA2XiOctad_coordinates : leechRootedA2XiOctad.val =
    ![2, 2, -2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 2, 0, 0] := by
  have hs : griessOctadSignMask leechRootedA2XiOctadIndex 4 = 262148 := by
    simp only [griessOctadSignMask, leechRootedA2XiOctadIndex_coordinate]
    decide +kernel
  change griessShortIntegral (Sum.inr (Sum.inl (leechRootedA2XiOctadIndex, 4))) = _
  simp only [griessShortIntegral, leechRootedA2XiOctadIndex_label, hs]
  decide +kernel

/-- The second actual Xi transition ends at an original odd short vector, with its sign retained. -/
theorem leechRootedA2XiOctad_image :
    leechIntegralAction co1XiIsometry leechRootedA2XiOctad =
      -griessShortLatticeVector (Sum.inr (Sum.inr (778, 2))) := by
  apply leechRootedA2Xi_image_of_double
  rw [leechRootedA2XiOctad_coordinates]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
