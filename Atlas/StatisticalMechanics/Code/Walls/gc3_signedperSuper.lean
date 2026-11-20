/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Ising.AizenmanSignDominance
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


















theorem gc3_signedPerSuper (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K)
      = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) *
          (1 - (if connK ends m x y then 1 else 0)
             - (if connK ends m o y then 1 else 0)
             - (if connK ends m o x then 1 else 0)) := by
  
  rw [asd_switching_weighted_indicator ends m hnd A hm hxy φ hφ,
      asd_switching_weighted_indicator ends m hnd A hm hoy φ hφ,
      asd_switching_weighted_indicator ends m hnd A hm hox φ hφ]
  ring














theorem gc3_gap_eq_mass_mul_backbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_gap ends m φ A o x y
      = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
  unfold aie_gap aie_mass asd_ghsBackboneFactor
  exact gc3_signedPerSuper ends m hnd A hm hox hoy hxy φ hφ












theorem gc3_gap_allConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
  rw [gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ,
      aie_backbone_value_all ends m hall]; ring





theorem gc3_gap_noneConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnone : aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A := by
  rw [gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ,
      aie_backbone_value_none ends m hnone]; ring





theorem gc3_gap_exactlyOne (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = 0 := by
  rw [gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ,
      aie_backbone_value_one ends m hnotall hnotnone]; ring










theorem gc3_mass_nonneg (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (S : Finset V) : 0 ≤ aie_mass ends m φ S :=
  aie_mass_nonneg ends m φ hφnn S









theorem gc3_per_super_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aie_allConn ends m o x y) :
    0 ≤ aie_gap ends m φ A o x y := by
  rw [gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ]
  exact mul_nonneg (gc3_mass_nonneg ends m φ hφnn A)
    (aie_backbone_factor_nonneg_not_all ends m hnotall)

end StatMech.Walls
