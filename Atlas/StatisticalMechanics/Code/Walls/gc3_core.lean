/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.gc_core
import Code.Walls.gc3_signedperSuper
import Code.Walls.gc3_backbonetrichotomy
import Code.Walls.gc3_backbonenotsigndef
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
















theorem gc3_summedGap_eq (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M, aie_gap ends m (Φ m) A o x y
      = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
        - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) :=
  aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ


























def GHS3SummedGapNonpos (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (Φ : Finset ι → Finset ι → ℝ) (o x y : V) : Prop :=
  ∑ m ∈ M, aie_gap ends m (Φ m) A o x y ≤ 0











theorem gc3_residue_iff_noneLe (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    GHS3SummedGapNonpos ends M A Φ o x y
      ↔ (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by
  unfold GHS3SummedGapNonpos
  rw [gc3_summedGap_eq ends M hnd A hm hox hoy hxy Φ hΦ]
  constructor <;> intro h <;> linarith















theorem gc3_ghs_masses_le_of_residue (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ)
    (hres : GHS3SummedGapNonpos ends M A Φ o x y) :
    (∑ m ∈ M, aie_mass ends m (Φ m) A)
      ≤ (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
        + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
        + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x})) := by
  have hsplit := aie_inclusion_exclusion_split ends M A o x y Φ
  unfold GHS3SummedGapNonpos at hres
  rw [hsplit] at hres
  linarith




















theorem gc3_residue_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    GHS3SummedGapNonpos ends M A Φ o x y := by
  unfold GHS3SummedGapNonpos
  refine Finset.sum_nonpos (fun m hmem => ?_)
  rw [aie_gap_allConn ends m (hnd m hmem) A (hm m hmem) hox hoy hxy (Φ m) (hΦ m hmem)
    (hall m hmem)]
  have hmass : 0 ≤ aie_mass ends m (Φ m) A :=
    aie_mass_nonneg ends m (Φ m) (hΦnn m hmem) A
  linarith




theorem gc3_residue_empty (ends : ι → Sym2 V) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ)
    (o x y : V) :
    GHS3SummedGapNonpos ends (∅ : Finset (Finset ι)) A Φ o x y := by
  unfold GHS3SummedGapNonpos
  rw [Finset.sum_empty]









theorem gc3_residue_single_allConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    GHS3SummedGapNonpos ends ({m} : Finset (Finset ι)) (sources ends m) (fun _ => φ) o x y := by
  refine gc3_residue_of_allConnOnly ends {m} ?_ (sources ends m) ?_ hox hoy hxy (fun _ => φ)
    ?_ ?_ ?_
  · intro m' hm' i hi
    rw [Finset.mem_singleton] at hm'; subst hm'; exact hnd i hi
  · intro m' hm'; rw [Finset.mem_singleton] at hm'; subst hm'; rfl
  · intro m' _ K; exact hφnn K
  · intro m' hm' K P hP hK
    rw [Finset.mem_singleton] at hm'; subst hm'; exact hφ K P hP hK
  · intro m' hm'; rw [Finset.mem_singleton] at hm'; subst hm'; exact hall
















theorem gc3_residue_not_termwise (ends : ι → Sym2 V) (m₁ m₂ : Finset ι)
    (hnd₁ : ∀ i ∈ m₁, ¬ (ends i).IsDiag) (hnd₂ : ∀ i ∈ m₂, ¬ (ends i).IsDiag)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m₁ → K ⊆ m₁ → φ (K ∆ P) = φ K)
    (hφ' : ∀ K P, P ⊆ m₂ → K ⊆ m₂ → φ (K ∆ P) = φ K)
    (h₁ : aie_allConn ends m₁ o x y) (h₂ : aie_noneConn ends m₂ o x y) :
    aie_gap ends m₁ φ (sources ends m₁) o x y ≤ 0
      ∧ 0 ≤ aie_gap ends m₂ φ (sources ends m₂) o x y := by
  refine ⟨?_, ?_⟩
  · rw [aie_gap_allConn ends m₁ hnd₁ (sources ends m₁) rfl hox hoy hxy φ hφ h₁]
    have : 0 ≤ aie_mass ends m₁ φ (sources ends m₁) := aie_mass_nonneg ends m₁ φ hφnn _
    linarith
  · rw [aie_gap_noneConn ends m₂ hnd₂ (sources ends m₂) rfl hox hoy hxy φ hφ' h₂]
    exact aie_mass_nonneg ends m₂ φ hφnn _

end StatMech.Walls



















namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech.Ising
open StatMech.Walls.GhcEqGap











theorem gc3_ursell_nonpos_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y






theorem gc3_ghs_concavity_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) :
    GHSThreePointSym G β h o :=
  gc_ghs_concavity_of_signDominance G β h hβ hh o hsd










theorem gc3_aizenman_barsky_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsd : GHSSignDominance G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor

end StatMech.Walls
