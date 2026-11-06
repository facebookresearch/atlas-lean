/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSourceOctadSubgroup

/-! The five actual source words generate the entire source-octad permutation stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The actual pair-word certificate is the original pointwise group action. -/
theorem generatedFifthSourceOctad_rep_pair (r : Fin 28) :
    generatedFifthSourceOctadPairRep r • ({8, 11} : Finset (Fin 24)) =
      generatedFifthSourceOctadPair r := by
  rw [Finset.smul_finset_def, Finset.image_insert, Finset.image_singleton]
  change ({(generatedFifthSourceOctadPairRep r).val 8,
    (generatedFifthSourceOctadPairRep r).val 11} : Finset (Fin 24)) = _
  exact generatedFifthSourceOctadPair_certificate r

/-- Fixing the original unordered pair is the literal physical preservation condition. -/
theorem generatedFifthSourceOctad_pair_fixed_iff (p : golayAutomorphismSubgroup) :
    p • ({8, 11} : Finset (Fin 24)) = ({8, 11} : Finset (Fin 24)) ↔
      ∀ i : Fin 24, (p.val i = 8 ∨ p.val i = 11) ↔ (i = 8 ∨ i = 11) := by
  constructor
  · intro hp i
    have h : p • i ∈ ({8, 11} : Finset (Fin 24)) ↔
        i ∈ ({8, 11} : Finset (Fin 24)) := by
      conv_lhs => rw [← hp]
      exact Finset.smul_mem_smul_finset_iff
        (s := ({8, 11} : Finset (Fin 24))) (b := i) p
    have hpi : p • i = p.val i := rfl
    rw [hpi] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  · intro hp
    ext i
    obtain ⟨a, rfl⟩ := p.val.surjective i
    change p • a ∈ p • ({8, 11} : Finset (Fin 24)) ↔
      p • a ∈ ({8, 11} : Finset (Fin 24))
    rw [Finset.smul_mem_smul_finset_iff]
    have hpa : p • a = p.val a := rfl
    rw [hpa]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (hp a).symm

/-- Every genuine source-octad permutation has the same pair image as a displayed actual word. -/
theorem generatedFifthSourceOctad_pair_transversal (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedFifthSourceOctadSubgroup) :
    ∃ r : Fin 28, generatedFifthSourceOctadPairRep r • ({8, 11} : Finset (Fin 24)) =
      p • ({8, 11} : Finset (Fin 24)) := by
  have h8 := (generatedFifthSourceOctad_preserves_coordinates p hp 8).mpr (by decide)
  have h11 := (generatedFifthSourceOctad_preserves_coordinates p hp 11).mpr (by decide)
  obtain ⟨r, hr⟩ := generatedFifthSourceOctadPair_covers (p.val 8) (p.val 11)
    h8.1 h8.2 h11.1 h11.2 (p.val.injective.ne (by decide))
  refine ⟨r, ?_⟩
  rw [generatedFifthSourceOctad_rep_pair, ← hr]
  simp only [Finset.smul_finset_def, Finset.image_insert, Finset.image_singleton]
  rfl

/-- The five original words generate the full genuine source-octad stabilizer. -/
theorem generatedFifthSourceOctad_five_eq :
    generatedFifthSourceOctadFiveSubgroup = generatedFifthSourceOctadSubgroup := by
  apply le_antisymm generatedFifthSourceOctad_five_le
  intro p hp
  obtain ⟨r, hr⟩ := generatedFifthSourceOctad_pair_transversal p hp
  let q := generatedFifthSourceOctadPairRep r
  have hq : q ∈ generatedFifthSourceOctadFiveSubgroup := generatedFifthSourceOctad_rep_mem r
  have hfix : (q⁻¹ * p) • ({8, 11} : Finset (Fin 24)) = ({8, 11} : Finset (Fin 24)) := by
    rw [mul_smul, ← hr, inv_smul_smul]
  have hflag : q⁻¹ * p ∈ generatedFourthPermutationFlagStabilizer :=
    ⟨generatedFifthSourceOctadSubgroup.mul_mem
      (generatedFifthSourceOctadSubgroup.inv_mem (generatedFifthSourceOctad_five_le hq)) hp,
      (generatedFifthSourceOctad_pair_fixed_iff _).mp hfix⟩
  have hrem := generatedFifthSourceOctad_flag_le hflag
  have hprod := generatedFifthSourceOctadFiveSubgroup.mul_mem hq hrem
  simpa only [mul_inv_cancel_left] using hprod

/-- Inclusion of the five actual words implies inclusion of the full genuine octad stabilizer. -/
theorem generatedFifthSourceOctad_le_of_generators (P : Subgroup golayAutomorphismSubgroup)
    (hP : ∀ k : Fin 5, generatedFifthSourceOctadPermutation k ∈ P) :
    generatedFifthSourceOctadSubgroup ≤ P := by
  rw [← generatedFifthSourceOctad_five_eq]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact hP k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
