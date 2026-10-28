/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightSeries

/-! The counted bounded assignments give genuine integral section vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Insert the eight integer coordinates and sixteen exterior zeros. -/
def generatedOctadEightInteger (a : Fin 8 → Fin 17) : Fin 24 → ℤ :=
  Fin.append (fun j => leechNormEightCoordinate (a j)) (fun _ : Fin 16 => 0)

/-- The inserted vector has the prescribed genuine source residues. -/
theorem generatedOctadEightInteger_residue (b : ZMod 2)
    (a : GeneratedOctadNormEightBounded b) (i : Fin 24) :
    (generatedOctadEightInteger a.val i : ZMod 4) =
      2 * (((b • golayStandardOctad) i).val : ZMod 4) := by
  refine Fin.addCases (m := 8) (n := 16) ?_ ?_ i
  · intro j
    simpa [generatedOctadEightInteger, golayStandardOctad] using a.property.1 j
  · intro j
    simp [generatedOctadEightInteger, golayStandardOctad]

/-- The counted assignments have the actual integral square sum 64. -/
theorem generatedOctadEightInteger_square (b : ZMod 2)
    (a : GeneratedOctadNormEightBounded b) :
    leechSquareSum (generatedOctadEightInteger a.val) = 64 := by
  have hs := congrArg (fun n : ℕ => (n : ℤ)) a.property.2.1
  simp only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs] at hs
  unfold leechSquareSum generatedOctadEightInteger
  rw [Fin.sum_univ_add (a := 8) (b := 16)]
  simpa only [Fin.append_left, Fin.append_right, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, Nat.cast_ofNat] using hs

/-- The counted assignments satisfy the actual source sum congruence. -/
theorem generatedOctadEightInteger_sum (b : ZMod 2)
    (a : GeneratedOctadNormEightBounded b) :
    ((∑ i, generatedOctadEightInteger a.val i : ℤ) : ZMod 8) = 0 := by
  unfold generatedOctadEightInteger
  rw [Fin.sum_univ_add (a := 8) (b := 16)]
  simpa only [Fin.append_left, Fin.append_right, Finset.sum_const_zero, add_zero]
    using a.property.2.2

/-- Every bounded assignment counted above is a genuine norm-eight section vector. -/
def generatedOctadBoundedVector (s : Σ b : ZMod 2, GeneratedOctadNormEightBounded b) :
    GeneratedOctadNormEight golayStandardOctad := by
  refine ⟨⟨generatedOctadEightInteger s.2.val, ?_⟩, ?_,
    generatedOctadEightInteger_square s.1 s.2⟩
  · apply (mem_leechIntegral_iff_source _).mpr
    refine ⟨0, Or.inl rfl, s.1 • golayStandardOctad,
      golayCode.smul_mem s.1 golayStandardOctad_mem, ?_, ?_⟩
    · simpa only [Int.cast_zero, zero_add] using generatedOctadEightInteger_residue s.1 s.2
    · simpa only [Int.cast_zero, mul_zero] using generatedOctadEightInteger_sum s.1 s.2
  · intro i
    refine Fin.addCases (m := 8) (n := 16) ?_ ?_ i
    · intro j hj
      simp [golayStandardOctad] at hj
    · intro j _
      simp [generatedOctadEightInteger]

/-- The underlying inserted integer coordinates recover the assignment uniquely. -/
theorem generatedOctadEightInteger_injective : Function.Injective generatedOctadEightInteger := by
  intro a k h
  funext j
  apply leechNormEightCoordinate_injective
  have he := congrFun h (Fin.castAdd 16 j)
  simpa only [generatedOctadEightInteger, Fin.append_left] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
