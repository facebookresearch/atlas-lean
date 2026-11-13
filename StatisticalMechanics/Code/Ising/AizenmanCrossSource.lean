/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.MultiReplica
import Code.Ising.AizenmanSignDominance
import Code.Ising.AizenmanInclusionExclusion
import Code.Ising.AizenmanHdom

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising








open StatMech.Sharpness.RandomCurrent




local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]











theorem gha_crossSource_mass_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A
      ∧ aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A
      ∧ aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A :=
  ⟨ahd_mass_reroute_xy_eq ends m hnd A hm hxy φ hφ hall,
   ahd_mass_reroute_oy_eq ends m hnd A hm hoy φ hφ hall,
   ahd_mass_reroute_ox_eq ends m hnd A hm hox φ hφ hall⟩







theorem gha_crossSource_total_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) + aie_mass ends m φ (A ∆ {o, y})
        + aie_mass ends m φ (A ∆ {o, x})
      = 3 * aie_mass ends m φ A := by
  obtain ⟨h1, h2, h3⟩ := gha_crossSource_mass_eq ends m hnd A hm hox hoy hxy φ hφ hall
  rw [h1, h2, h3]; ring





theorem gha_allConn_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A :=
  ahd_gap_eq_neg_two_mass ends m hnd A hm hox hoy hxy φ hφ hall
















def gha_crossSourceDom (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (o x y : V) (Φ : Finset ι → Finset ι → ℝ) : Prop :=
  2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ ∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y})








theorem gha_crossSource_singleton_collapse (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A :=
  (gha_crossSource_mass_eq ends m hnd A hm hox hoy hxy φ hφ hall).1







theorem gha_crossSourceDom_holds_of_no_allConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    gha_crossSourceDom ends M A o x y Φ := by
  unfold gha_crossSourceDom
  rw [hno, Finset.sum_empty, mul_zero]
  exact Finset.sum_nonneg (fun m _ => aie_mass_nonneg ends m (Φ m) (hΦnn m) _)




















theorem gha_crossSource_hdom_refutable :
    ¬ gha_crossSourceDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
  unfold gha_crossSourceDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := srcK ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton, Finset.sum_singleton] at hdom
  
  have heq : aie_mass ahd_triEnds m₀ (fun _ => 1) (A₀ ∆ {1, 2})
      = aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := by
    refine gha_crossSource_singleton_collapse ahd_triEnds m₀ ahd_triEnds_nd A₀ hA₀.symm
      (o := 0) (x := 1) (y := 2) (by decide) (by decide) (by decide) (fun _ => 1)
      (fun _ _ _ _ => rfl) hall
  rw [heq] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising

end StatMech

