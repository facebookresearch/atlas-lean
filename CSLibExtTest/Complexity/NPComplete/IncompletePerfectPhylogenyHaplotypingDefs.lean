/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotypingDefs

namespace MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open HaplotypeInferencePureParsimony (Explains)
open Cslib.Bioinformatics.Phylogenetics.Splits (IsPerfectPhylogeny FourGametes
  exists_perfectPhylogeny_iff)

private theorem accepts_encoding (i : IncompletePerfectPhylogenyHaplotypingInstance) :
    incompletePerfectPhylogenyHaplotypingDec (bitEncode i) = true ↔
      WellFormed i ∧ IncompletePerfectPhylogenyHaplotypingFeasible i := by
  simp [incompletePerfectPhylogenyHaplotypingDec, bitDecode_bitEncode]

/-- Homozygous genotypes `01`, `10`, and `0?` on two sites. -/
private abbrev partial3 : List (List ℕ) := [[0, 1], [1, 0], [0, 3]]

/-- Homozygous genotypes `01`, `10`, `00`, `11`: all four gametes. -/
private abbrev gametes4 : List (List ℕ) := [[0, 1], [1, 0], [0, 0], [1, 1]]

/-- The completion of `partial3` that fills `?` with `1`. -/
private abbrev completed3 : List (List ℕ) := [[0, 1], [1, 0], [0, 1]]

/-- A lone continuation bit is a truncated instance encoding. -/
example : incompletePerfectPhylogenyHaplotypingDec [true] = false := by
  have h : bitDecode (α := IncompletePerfectPhylogenyHaplotypingInstance) [true] = none := rfl
  simp [incompletePerfectPhylogenyHaplotypingDec, h]

/-- Completing `0?` as `01` leaves only the gametes `01` and `10`, which pass the four-gamete
test, so a perfect phylogeny exists. -/
example :
    incompletePerfectPhylogenyHaplotypingDec
      (bitEncode ((2, partial3) : IncompletePerfectPhylogenyHaplotypingInstance)) = true := by
  apply (accepts_encoding _).2
  let H : Fin partial3.length × Bool → Fin 2 → Bool := fun x k =>
    decide ((completed3.getD x.1 []).getD k 0 = 1)
  refine ⟨by unfold WellFormed; decide, fun j => completed3.getD j [], H, ?_, ?_⟩
  · unfold Completes Explains
    decide
  · refine (exists_perfectPhylogeny_iff (by decide) H).2 fun j k hfg => ?_
    obtain ⟨x, hx₁, hx₂⟩ := hfg true true
    obtain ⟨y, hy₁, hy₂⟩ := hfg true false
    clear hfg
    revert x y j k
    decide

/-- With no `?` and no `2`, the haplotypes are the genotypes themselves, and the two sites show
all four gametes, so no perfect phylogeny exists. -/
example :
    incompletePerfectPhylogenyHaplotypingDec
      (bitEncode ((2, gametes4) : IncompletePerfectPhylogenyHaplotypingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, c, H, hc, T, hT⟩ := (accepts_encoding _).1 hacc
  have hlen : ∀ j : Fin gametes4.length, (gametes4.get j).length = 2 := by decide
  have hne3 : ∀ (j : Fin gametes4.length) (k : Fin 2), (gametes4.get j).getD k 0 ≠ 3 := by
    decide
  have h01 : ∀ (j : Fin gametes4.length) (k : Fin 2),
      (gametes4.get j).getD k 0 = 0 ∨ (gametes4.get j).getD k 0 = 1 := by decide
  have hrow : ∀ (j : Fin gametes4.length) (k : Fin 2),
      H (j, false) k = decide ((gametes4.get j).getD k 0 = 1) := by
    intro j k
    obtain ⟨⟨-, -, hagree⟩, hexp⟩ := hc j
    have hval := hagree k (by have := k.isLt; have := hlen j; simp only at *; omega) (hne3 j k)
    obtain ⟨h₀, h₁, -⟩ := hexp k
    rw [hval] at h₀ h₁
    rcases h01 j k with h | h
    · rw [(h₀ h).1, h]
      rfl
    · rw [(h₁ h).1, h]
      rfl
  have hfour : FourGametes (H · 0) (H · 1) := by
    intro b c
    cases b <;> cases c
    · exact ⟨(⟨2, by decide⟩, false), (hrow _ _).trans rfl, (hrow _ _).trans rfl⟩
    · exact ⟨(⟨0, by decide⟩, false), (hrow _ _).trans rfl, (hrow _ _).trans rfl⟩
    · exact ⟨(⟨1, by decide⟩, false), (hrow _ _).trans rfl, (hrow _ _).trans rfl⟩
    · exact ⟨(⟨3, by decide⟩, false), (hrow _ _).trans rfl, (hrow _ _).trans rfl⟩
  exact (exists_perfectPhylogeny_iff (by decide) H).1 ⟨T, hT⟩ 0 1 hfour

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((2, gametes4) : IncompletePerfectPhylogenyHaplotypingInstance) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping
