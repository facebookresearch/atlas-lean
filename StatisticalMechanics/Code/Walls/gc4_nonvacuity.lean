/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.gc3_core
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph Set
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent
open StatMech.Ising
open StatMech.Walls.GhcEqGap

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


















def gc4_NoneLeTwiceAll (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (Φ : Finset ι → Finset ι → ℝ) (o x y : V) : Prop :=
  (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)






theorem gc4_residue_iff_noneLe (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    GHS3SummedGapNonpos ends M A Φ o x y ↔ gc4_NoneLeTwiceAll ends M A Φ o x y :=
  gc3_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ
















theorem gc4_noneLe_of_noNoneConn (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hnone : ∀ m ∈ M, ¬ aie_noneConn ends m o x y) :
    gc4_NoneLeTwiceAll ends M A Φ o x y := by
  unfold gc4_NoneLeTwiceAll
  have hfilt : M.filter (fun m => aie_noneConn ends m o x y) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro m hm; exact hnone m hm
  rw [hfilt, Finset.sum_empty]
  have hnn : 0 ≤ ∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A :=
    Finset.sum_nonneg (fun m hm =>
      aie_mass_nonneg ends m (Φ m) (hΦnn m (Finset.mem_of_mem_filter m hm)) A)
  linarith













theorem gc4_noneLe_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    gc4_NoneLeTwiceAll ends M A Φ o x y :=
  gc4_noneLe_of_noNoneConn ends M A Φ hΦnn
    (fun m hm hnone => aie_noneConn_not_allConn ends m hnone (hall m hm))







theorem gc4_gap_neg_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    ∀ m ∈ M, aie_gap ends m (Φ m) A o x y = -2 * aie_mass ends m (Φ m) A
      ∧ aie_gap ends m (Φ m) A o x y ≤ 0 := by
  intro m hm'
  have heq := aie_gap_allConn ends m (hnd m hm') A (hm m hm') hox hoy hxy (Φ m) (hΦ m hm')
    (hall m hm')
  refine ⟨heq, ?_⟩
  rw [heq]
  have : 0 ≤ aie_mass ends m (Φ m) A := aie_mass_nonneg ends m (Φ m) (hΦnn m hm') A
  linarith






theorem gc4_noneLe_empty (ends : ι → Sym2 V) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ)
    (o x y : V) :
    gc4_NoneLeTwiceAll ends (∅ : Finset (Finset ι)) A Φ o x y := by
  unfold gc4_NoneLeTwiceAll
  simp











theorem gc4_residue_of_noNoneConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hnone : ∀ m ∈ M, ¬ aie_noneConn ends m o x y) :
    GHS3SummedGapNonpos ends M A Φ o x y :=
  (gc4_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ).mpr
    (gc4_noneLe_of_noNoneConn ends M A Φ hΦnn hnone)





theorem gc4_residue_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    GHS3SummedGapNonpos ends M A Φ o x y :=
  (gc4_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ).mpr
    (gc4_noneLe_of_allConnOnly ends M A Φ hΦnn hall)




theorem gc4_residue_empty (ends : ι → Sym2 V) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ)
    (o x y : V) :
    GHS3SummedGapNonpos ends (∅ : Finset (Finset ι)) A Φ o x y :=
  gc3_residue_empty ends A Φ o x y

end StatMech.Walls
