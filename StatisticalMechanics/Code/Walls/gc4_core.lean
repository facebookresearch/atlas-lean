/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.gc3_core
import Code.Walls.gc3_backbonenotsigndef
import Code.Walls.gc4_persupertrichotomy
import Code.Walls.gc4_shiftpreservesclass
import Code.Walls.gc4_massshiftinvariant
import Code.Walls.gc4_nonvacuity
import Code.Walls.gc4_massesle
import Code.Walls.gc4_concavitysharpness
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph Set
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent
open StatMech.Ising
open StatMech.Walls.GhcEqGap

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


















theorem gc4_core_residue_iff_noneLe (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    GHS3SummedGapNonpos ends M A Φ o x y
      ↔ ((∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)) :=
  gc3_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ























theorem gc4_within_super_massShift (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (S : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ (S ∆ sources ends K) = aie_mass ends m φ S :=
  gc4_aie_mass_shift_invariant ends m K hK S φ hφ








theorem gc4_shift_preserves_factor (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (A : Finset V) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = asd_ghsBackboneFactor ends m o x y
      ∧ Set.MapsTo (fun N => N ∆ K)
          {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} :=
  gc4_shift_preserves_backboneFactor ends m K hK A o x y



















theorem gc4_shift_cannot_cross_class (ends : ι → Sym2 V) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : aie_allConn ends m₁ o x y) (h₂ : aie_noneConn ends m₂ o x y) :
    asd_ghsBackboneFactor ends m₁ o x y = -2
      ∧ asd_ghsBackboneFactor ends m₂ o x y = 1
      ∧ asd_ghsBackboneFactor ends m₁ o x y ≠ asd_ghsBackboneFactor ends m₂ o x y := by
  obtain ⟨hxy₁, hoy₁, hox₁⟩ := h₁
  refine ⟨asd_ghsBackboneFactor_allConn ends m₁ hxy₁ hoy₁ hox₁,
    aie_backbone_value_none ends m₂ h₂, ?_⟩
  rw [asd_ghsBackboneFactor_allConn ends m₁ hxy₁ hoy₁ hox₁, aie_backbone_value_none ends m₂ h₂]
  norm_num






theorem gc4_classes_disjoint (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnone : aie_noneConn ends m o x y) (hall : aie_allConn ends m o x y) : False :=
  aie_noneConn_not_allConn ends m hnone hall

















theorem gc4_aie_mass_empty (ends : ι → Sym2 V) (φ : Finset ι → ℝ) (S : Finset V) :
    aie_mass ends (∅ : Finset ι) φ S = if S = ∅ then φ ∅ else 0 := by
  unfold aie_mass
  rw [Finset.powerset_empty]
  simp only [Finset.filter_singleton]
  have hsrc : sources ends (∅ : Finset ι) = (∅ : Finset V) := by
    ext v; simp [RandomCurrent.sources, degK]
  rw [hsrc]
  by_cases h : S = ∅
  · subst h; simp
  · rw [if_neg (by tauto), if_neg h]; simp






theorem gc4_gap_empty_pos (ends : ι → Sym2 V) (φ : Finset ι → ℝ) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    aie_gap ends (∅ : Finset ι) φ (∅ : Finset V) o x y = φ ∅ := by
  
  have hnone : aie_noneConn ends (∅ : Finset ι) o x y := gc3_noneConn_empty ends hox hoy hxy
  unfold aie_gap
  rw [gc4_aie_mass_empty, gc4_aie_mass_empty, gc4_aie_mass_empty, gc4_aie_mass_empty]
  have hxy0 : (∅ : Finset V) ∆ ({x, y} : Finset V) = ({x, y} : Finset V) := by
    rw [symmDiff_eq_right.mpr (by simp)]
  have hoy0 : (∅ : Finset V) ∆ ({o, y} : Finset V) = ({o, y} : Finset V) := by
    rw [symmDiff_eq_right.mpr (by simp)]
  have hox0 : (∅ : Finset V) ∆ ({o, x} : Finset V) = ({o, x} : Finset V) := by
    rw [symmDiff_eq_right.mpr (by simp)]
  rw [if_pos rfl, hxy0, hoy0, hox0, if_neg (insert_ne_empty x {y}),
    if_neg (insert_ne_empty o {y}), if_neg (insert_ne_empty o {x})]
  ring












theorem gc4_abstract_residue_false {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (ends : ι → Sym2 V) :
    ¬ GHS3SummedGapNonpos ends ({∅} : Finset (Finset ι)) (∅ : Finset V)
        (fun _ _ => (1 : ℝ)) o x y := by
  
  have hnone : aie_noneConn ends (∅ : Finset ι) o x y := gc3_noneConn_empty ends hox hoy hxy
  unfold GHS3SummedGapNonpos
  rw [Finset.sum_singleton]
  rw [gc4_gap_empty_pos ends (fun _ => (1 : ℝ)) hox hoy hxy]
  norm_num






theorem gc4_residue_refutable {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (ends : ι → Sym2 V) :
    ¬ (∀ (M : Finset (Finset ι)) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ),
        (∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K) → GHS3SummedGapNonpos ends M A Φ o x y) := by
  intro hall
  exact gc4_abstract_residue_false hox hoy hxy ends
    (hall ({∅} : Finset (Finset ι)) (∅ : Finset V) (fun _ _ => (1 : ℝ))
      (fun _ _ _ => zero_le_one))















theorem gc4_core_masses_le_of_residue (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ)
    (hres : GHS3SummedGapNonpos ends M A Φ o x y) :
    gc4_MassesLe ends M A Φ o x y :=
  gc4_masses_le_of_residue ends M A o x y Φ hres















theorem gc4_core_concavity_sharpness {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : W) (J : ℝ)
    (hsd : ∀ h', 0 ≤ h' → GHSSignDominance G β h' o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    GHSThreePointSym G β h o
      ∧ ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))
      ∧ bondEnergySusceptibility G β h o
          ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc4_concavitySharpness G β h hβ hh o J hsd hfactor
















theorem gc4_core_residue_of_allConnOnly (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
    GHS3SummedGapNonpos ends M A Φ o x y :=
  gc4_residue_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall



theorem gc4_core_residue_empty (ends : ι → Sym2 V) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ)
    (o x y : V) :
    GHS3SummedGapNonpos ends (∅ : Finset (Finset ι)) A Φ o x y :=
  gc3_residue_empty ends A Φ o x y
















theorem gc4_genuine_object_is_ensemble {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 W → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Ising.Current W)) (B : Finset W) (o x y : W) (μ : ℝ)
    (hμ : 0 ≤ μ) :
    (-2 * μ * tcp_allConnProb G β J M B o x y ≤ 0)
      ∧ tcp_allConnProb G β J M B o x y ≤ 1 :=
  ⟨egh_u3_nonpos G β J hβ hJ M B o x y μ hμ,
   egh_ensemble_prob_le_one G β J hβ hJ M B o x y⟩

end StatMech.Walls
