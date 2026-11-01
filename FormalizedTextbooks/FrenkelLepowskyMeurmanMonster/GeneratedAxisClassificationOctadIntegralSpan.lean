/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpanData

/-! The actual 120 supported short classes lie in the checked binary space. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Insertion intertwines local root coordinates with the actual catalogue roots. -/
theorem generatedOctadIntegerRoot_insert_sum (v : Fin 8 → ℤ) :
    generatedOctadIntegerInsert (generatedOctadIntegerRootMatrix *ᵥ v) =
      ∑ j, v j • griessShortIntegral (generatedOctadBasisLabel j) := by
  have hm : generatedOctadIntegerRootMatrix *ᵥ v =
      ∑ j, v j • generatedOctadIntegerRootMatrix.col j := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hm, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  have hj := (generatedOctadIntegerRoot_physical_certificate j).symm.trans
    (generatedOctadBasis_integer_certificate j)
  rw [hj]

/-- Every actual supported label is represented by one of the checked local patterns. -/
theorem generatedOctadShortSupport_local_pattern (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    ∃ v : Fin 8 → ℤ, generatedOctadIntegerRootMatrix *ᵥ
        generatedOctadIntegerRootCoordinates v = v ∧
      generatedOctadIntegerInsert v = griessShortIntegral r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · have hcoord : ∀ i : Fin 24, (0xff00 : ℕ).testBit i.val = true ↔
        ∃ k : Fin 8, i = ⟨8 + k.val, by omega⟩ := by decide +kernel
    change generatedOctadPairSupport generatedOctadBasisOctad p at hr
    rw [generatedOctadPairSupport, generatedOctadBasisOctad_mask] at hr
    obtain ⟨i, hi⟩ := (hcoord _).mp hr.1
    obtain ⟨j, hj⟩ := (hcoord _).mp hr.2
    refine ⟨generatedOctadIntegerPair s i j,
      generatedOctadIntegerPair_span_certificate s i j, ?_⟩
    rw [generatedOctadIntegerPair_insert_certificate]
    simp only [griessShortIntegral, hi, hj]
  · change o = generatedOctadBasisOctad at hr
    subst o
    refine ⟨generatedOctadIntegerSigns e, generatedOctadIntegerSigns_span_certificate e, ?_⟩
    rw [generatedOctadIntegerSigns_insert_certificate]
    simp only [griessShortIntegral, generatedOctadBasisOctad_mask,
      generatedOctadBasisOctad_sign_mask]
  · exact False.elim hr

/-- Every supported actual short lattice vector is an integer combination
of the eight checked preferred-short lattice vectors. -/
theorem generatedOctadShortSupport_integer_span (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    ∃ a : Fin 8 → ℤ, griessShortLatticeVector r =
      ∑ j, a j • griessShortLatticeVector (generatedOctadBasisLabel j) := by
  obtain ⟨v, hv, hr⟩ := generatedOctadShortSupport_local_pattern r hr
  refine ⟨generatedOctadIntegerRootCoordinates v, ?_⟩
  apply Subtype.ext
  change griessShortIntegral r = _
  have he := generatedOctadIntegerRoot_insert_sum (generatedOctadIntegerRootCoordinates v)
  rw [hv, hr] at he
  simpa only [Submodule.coe_sum, Submodule.coe_smul, griessShortLatticeVector] using he

/-- Every actual supported short class lies in the genuine checked binary span. -/
theorem generatedOctadShortSupport_binary_span (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    toAdd (griessShortQ r).base ∈ generatedOctadBasisBinaryMatrix.mulVecLin.range := by
  obtain ⟨a, ha⟩ := generatedOctadShortSupport_integer_span r hr
  have hb (j : Fin 8) : toAdd (griessShortQ (generatedOctadBasisLabel j)).base ∈
      generatedOctadBasisBinaryMatrix.mulVecLin.range := by
    rw [generatedOctadBasis_actual_base]
    refine ⟨Pi.single j 1, ?_⟩
    exact Matrix.mulVec_single_one generatedOctadBasisBinaryMatrix j
  change leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r)) ∈ _
  rw [ha, map_sum, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_zsmul, map_zsmul]
  exact generatedOctadBasisBinaryMatrix.mulVecLin.range.toAddSubgroup.zsmul_mem (hb j) (a j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
