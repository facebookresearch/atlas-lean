/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.gc3_core
import Code.Walls.gc2_shiftbij
import Code.Ising.EnsembleGHS

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

















def gc4_MassesLe (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (Φ : Finset ι → Finset ι → ℝ) (o x y : V) : Prop :=
  (∑ m ∈ M, aie_mass ends m (Φ m) A)
    ≤ (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x}))


















theorem gc4_masses_le_of_residue (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ)
    (hres : GHS3SummedGapNonpos ends M A Φ o x y) :
    gc4_MassesLe ends M A Φ o x y := by
  
  have hsplit := aie_inclusion_exclusion_split ends M A o x y Φ
  unfold gc4_MassesLe
  unfold GHS3SummedGapNonpos at hres
  rw [hsplit] at hres
  linarith
















theorem gc4_massesLe_iff_residue (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ) :
    gc4_MassesLe ends M A Φ o x y ↔ GHS3SummedGapNonpos ends M A Φ o x y := by
  unfold gc4_MassesLe GHS3SummedGapNonpos
  rw [aie_inclusion_exclusion_split ends M A o x y Φ]
  constructor <;> intro h <;> linarith











theorem gc4_massesLe_iff_noneLe (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    gc4_MassesLe ends M A Φ o x y
      ↔ (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) :=
  (gc4_massesLe_iff_residue ends M A o x y Φ).trans
    (gc3_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ)






theorem gc4_massesLe_of_noneLe (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hnone : (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)) :
    gc4_MassesLe ends M A Φ o x y :=
  (gc4_massesLe_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ).2 hnone

















theorem gc4_massesLe_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    gc4_MassesLe ends M A Φ o x y :=
  gc4_masses_le_of_residue ends M A o x y Φ
    (gc3_residue_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall)




theorem gc4_massesLe_empty (ends : ι → Sym2 V) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ)
    (o x y : V) :
    gc4_MassesLe ends (∅ : Finset (Finset ι)) A Φ o x y :=
  gc4_masses_le_of_residue ends (∅ : Finset (Finset ι)) A o x y Φ
    (gc3_residue_empty ends A Φ o x y)








theorem gc4_massesLe_single_allConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    gc4_MassesLe ends ({m} : Finset (Finset ι)) (sources ends m) (fun _ => φ) o x y :=
  gc4_masses_le_of_residue ends ({m} : Finset (Finset ι)) (sources ends m) o x y (fun _ => φ)
    (gc3_residue_single_allConn ends m hnd hox hoy hxy φ hφnn hφ hall)

end StatMech.Walls
